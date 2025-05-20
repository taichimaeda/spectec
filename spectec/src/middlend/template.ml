
open Il.Ast
open Il.Print
open Util
open Source

module Set = Set.Make(String)
module Map = Map.Make(String)

let error at msg = Error.error at "template" msg

(* TODO: (lemmagen) Templates can substitute exp only *)
(* TODO: (lemmagen) ... on tuple exp expands entry in args *)
type slotentry = exp * bind list

type slottree = 
  | LeafT of slotentry
  | NodeT of slottree Map.t

type slottrie =
  | LeafI of slot option
  | NodeI of slot option * slottrie Map.t

let rec string_of_slottree tree = 
  match tree with
  | LeafT (e, bs) -> string_of_exp e ^ " " ^ string_of_binds bs
  | NodeT cs -> 
    Map.fold (fun k v acc -> acc ^ k ^ " -> " ^ string_of_slottree v ^ " ") cs ""

let rec string_of_slottrie trie =
  let aux s = 
    Option.value ~default:"empty" (Option.map string_of_slot s) in

  match trie with
  | LeafI s -> "LeafI (" ^ aux s ^ ")"
  | NodeI (s, cs) -> "NodeI (" ^ aux s ^ ")" ^
    Map.fold (fun k v acc -> acc ^ k ^ " -> " ^ string_of_slottrie v ^ " ") cs ""

type env =
  { typs : slottree Map.t ref;
    defs : slottree Map.t ref;
    rels : slottree Map.t ref;
    grams : slottree Map.t ref;    
    thms : slottree Map.t ref;
  }

let new_env () =
  { typs = ref Map.empty;
    defs = ref Map.empty;
    rels = ref Map.empty;
    grams = ref Map.empty;
    thms = ref Map.empty;
  }

let rec env_def d =
  match d.it with
  | TypD (_id, _ps, _insts) -> 
    failwith "unimplemented (lemmagen)"
  | RelD (_id, _mixop, _t, _rules) -> 
    failwith "unimplemented (lemmagen)"
  | DecD (_id, _ps, _t, _clauses) -> 
    failwith "unimplemented (lemmagen)"
  | RecD _ds -> 
    failwith "unimplemented (lemmagen)"
  | ThmD (_id, _bs, _e) | LemD (_id, _bs, _e) -> 
    failwith "unimplemented (lemmagen)"
  | TmplD _ | HintD _ -> ()

let slots_list f xs = List.flatten (List.map f xs)

let rec slots_iter it =
  match it with
  | Opt | List | List1 -> []
  | ListN (e, _) -> slots_exp e 
  
and slots_typ t =
  match t.it with
  | VarT (_, as_) -> slots_list slots_arg as_
  | BoolT -> []
  | NumT _ -> []
  | TextT -> []
  | TupT ets -> slots_list (fun (e, t) -> slots_exp e @ slots_typ t) ets
  | IterT (t1, it) -> slots_typ t1 @ slots_iter it
  | BotT -> []

and slots_deftyp dt =
  match dt.it with
  | AliasT t -> slots_typ t
  | StructT tfs -> slots_list slots_typfield tfs
  | VariantT tcs -> slots_list slots_typcase tcs

and slots_typfield (_, (_, t, prems), _) = 
  slots_typ t @ slots_list slots_prem prems
and slots_typcase (_, (_, t, prems), _) =
  slots_typ t @ slots_list slots_prem prems

and slots_exp e = 
  match e.it with
  | VarE _ -> []
  | BoolE _ | NatE _ | TextE _ -> []
  | UnE (_, e1) -> slots_exp e1
  | BinE (_, e1, e2) -> slots_exp e1 @ slots_exp e2
  | CmpE (_, e1, e2) -> slots_exp e1 @ slots_exp e2
  | TupE es -> slots_list slots_exp es
  | ProjE (e1, _) -> slots_exp e1
  | CaseE (_, e1) -> slots_exp e1
  | UncaseE (e1, _) -> slots_exp e1
  | OptE None -> []
  | OptE (Some e1) -> slots_exp e1
  | TheE e1 -> slots_exp e1
  | StrE efs -> slots_list slots_expfield efs
  | DotE (e1, _) -> slots_exp e1
  | CompE (e1, e2) -> slots_exp e1 @ slots_exp e2
  | ListE es -> slots_list slots_exp es
  | LenE e1 -> slots_exp e1
  | CatE (e1, e2) -> slots_exp e1 @ slots_exp e2
  | IdxE (e1, e2) -> slots_exp e1 @ slots_exp e2
  | SliceE (e1, e2, e3) -> slots_exp e1 @ slots_exp e2 @ slots_exp e3
  | UpdE (e1, p1, e2) -> slots_exp e1 @ slots_path p1 @ slots_exp e2
  | ExtE (e1, p1, e2) -> slots_exp e1 @ slots_path p1 @ slots_exp e2
  | CallE (_, as_) -> slots_list slots_arg as_
  | IterE (e1, ie) -> slots_exp e1 @ slots_iterexp ie
  | SubE (e1, t1, t2) -> slots_exp e1 @ slots_typ t1 @ slots_typ t2
  | RuleE (_, _, e1) -> slots_exp e1
  | ForallE (_, as_, e1) -> slots_list slots_arg as_ @ slots_exp e1
  | ExistsE (_, as_, e1) -> slots_list slots_arg as_ @ slots_exp e1
  | TmplE s -> [s]

and slots_expfield (_, e) = slots_exp e

and slots_path p =
  match p.it with
  | RootP -> []
  | IdxP (p1, e) -> slots_path p1 @ slots_exp e
  | SliceP (p1, e1, e2) -> slots_path p1 @ slots_exp e1 @ slots_exp e2
  | DotP (p1, _) -> slots_path p1

and slots_iterexp (iter, bs) =
    slots_iter iter @ slots_list (fun (_, t) -> slots_typ t) bs

and slots_prem prem =
  match prem.it with
  | RulePr (_, _, e) -> slots_exp e
  | IfPr e -> slots_exp e
  | LetPr (e1, e2, _) -> slots_exp e1 @ slots_exp e2
  | ElsePr -> []
  | IterPr (prem1, iter) -> slots_prem prem1 @ slots_iterexp iter

and slots_arg a =
  match a.it with
  | ExpA e -> slots_exp e
  | TypA t -> slots_typ t

and slots_param p = 
  match p.it with
  | ExpP (_, t) -> slots_typ t
  | TypP _ -> []

let slots_inst inst =
  match inst.it with
  | InstD (_, as_, dt) -> 
    slots_list slots_arg as_ @ slots_deftyp dt

let slots_rule rule =
  match rule.it with
  | RuleD (_, _, _, e, prems) ->
    slots_exp e @ slots_list slots_prem prems

let slots_clause clause =
  match clause.it with
  | DefD (_, as_, e, prems) ->
    slots_list slots_arg as_ @ slots_exp e @ slots_list slots_prem prems

let rec slots_def d = 
  let d' = match d.it with
    | TmplD d1 -> d1
    | _ -> error d.at "not a template definition" in
  match d'.it with
  | TypD (_, ps, insts) -> 
    slots_list slots_param ps @ slots_list slots_inst insts
  | RelD (_, _, t, rules) -> 
    slots_typ t @ slots_list slots_rule rules
  | DecD (_, ps, t, clauses) ->
    slots_list slots_param ps @ slots_typ t @ slots_list slots_clause clauses
  | RecD ds -> 
    slots_list slots_def ds
  | ThmD (_, _, e) | LemD (_, _, e) -> 
    slots_exp e
  | TmplD _ | HintD _ -> assert false

(* TODO: (lemmagen) Is this correct? *)
let rec insert_trie s ids trie =
  match ids with
  | [] -> 
    (match trie with
    | LeafI _ -> LeafI (Some s)
    | NodeI (_, trie) -> NodeI (Some s, trie))
  | id::ids' -> 
    (match trie with
    | LeafI s' -> 
      let c = insert_trie s ids' (LeafI None) in
      let cs = Map.add id c Map.empty in
      NodeI (s', cs)
    | NodeI (s', trie') ->
      let cs = match Map.find_opt id trie' with
      | None -> 
        let c = insert_trie s ids' (LeafI None) in
        Map.add id c trie'
      | Some c' -> 
        let c = insert_trie s ids' c' in
        Map.add id c trie' in
      NodeI (s', cs))

let make_trie ss = 
  let rec linearize' s acc =
    match s.it with
    | TopS id -> [id.it]
    | DotS (s1, id) -> linearize' s1 (id.it::acc)
    | WildS s1 -> linearize' s1 ("*"::acc)
    | VarS s1 -> linearize' s1 acc in

  let linearize s =
    List.rev (linearize' s []) in

  let empty = LeafI None in
  List.fold_left (fun acc s -> 
    let ids = linearize s in
    insert_trie s ids acc) empty ss

type subst = slot * slotentry
type substs = subst list

type comb = substs list

let make_comb (_tree : slottree) (_trie : slottrie) : comb = 
  failwith "unimplemented (lemmagen)"

let subst_def (_d : def) : def * bind list = 
  failwith "unimplemented (lemmagen)"

let transform (d : def) : def =
  let d', _bs = subst_def d in
  (* TODO: (lemmagen) Handle top-level binds *)
  match d'.it with
  | _ -> d'
