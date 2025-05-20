
open Il.Ast
open Il.Print
open Util
open Source

module Set = Set.Make(String)
module Map = Map.Make(String)

let error at msg = Error.error at "template" msg

(* TODO: (lemmagen) Templates can substitute exp only *)
(* TODO: (lemmagen) ... on tuple exp expands entry in args *)
type slotentry = bind list * exp

type slottree = 
  | LeafT of slotentry option
  | NodeT of slottree Map.t

type slottrie =
  | LeafI of slot option
  | NodeI of slot option * slottrie Map.t

let rec string_of_slottree tree = 
  match tree with
  | LeafT None -> "leaf()"
  | LeafT Some (bs, e) -> "leaf(" ^ string_of_binds bs ^ string_of_exp e ^ ")"
  | NodeT cs -> "node(" ^ 
      Map.fold (fun k v acc -> acc ^ k ^ " -> " ^ string_of_slottree v ^ " ") cs "" ^ ")"

let rec string_of_slottrie trie =
  let aux s = 
    Option.value ~default:"" (Option.map string_of_slot s) in

  match trie with
  | LeafI s -> "leaf(" ^ aux s ^ ")"
  | NodeI (s, cs) -> "node(" ^ aux s ^
      Map.fold (fun k v acc -> acc ^ k ^ " -> " ^ string_of_slottrie v ^ " ") cs "" ^ ")"

type env = slottree

let id_vars = "variables"
let id_typs = "types"
let id_rels = "relations"
let id_defs = "definitions"
let id_thms = "theorems"

let top_ids = [
  id_vars;
  id_typs;
  id_rels;
  id_defs;
  id_thms;
]

let rec find env ids =
  assert (List.mem (List.hd ids) top_ids);
  match ids, env with
  | [], LeafT (Some entry) -> entry
  | [], LeafT None -> error no_region "empty slot"
  | [], NodeT _ -> error no_region "not enough slot ids"
  | _::_, LeafT _ -> error no_region "too many slot ids"
  | id'::ids', NodeT cs ->
    (match Map.find_opt id' cs with
    | None -> error no_region "unexpected slot id"
    | Some env' -> find env' ids')

let rec bound env ids = 
  assert (List.mem (List.hd ids) top_ids);
  match ids, env with
  | [], LeafT (Some _) -> true
  | [], LeafT None -> false
  | [], NodeT _ -> false
  | _::_, LeafT _ -> false
  | id'::ids', NodeT cs ->
    (match Map.find_opt id' cs with
      | None -> false
      | Some env' -> bound env' ids')

let rec bind env ids entry =
  assert (List.mem (List.hd ids) top_ids);
  match ids, env with
  | [], LeafT _ -> LeafT (Some entry) (* override *)
  | [], NodeT _ -> error no_region "not enough slot ids"
  | _::_, LeafT (Some _) -> error no_region "occupied slot"
  | id'::ids', LeafT None ->
    let c = bind (LeafT None) ids' entry in
    let cs = Map.add id' c Map.empty in
    NodeT cs
  | id'::ids', NodeT cs ->
    let c = bind (LeafT None) ids' entry in
    let cs' = Map.add id' c cs in
    NodeT cs'

let new_env () : env = LeafT None

let entry_of_id id = 
  [], (TextE id.it) $$ id.at % (TextT $ id.at)

let entry_of_exp bs e = 
  let mem = Il.Free.Set.mem in
  let fs = Il.Free.free_exp e in
  let bs' = List.filter (fun b ->
    match b.it with 
    | ExpB (id, _, _) -> mem id.it fs.varid
    | TypB id -> mem id.it fs.typid) bs in
  bs', e

let entry_of_exps bs es =
  let bss', es' = List.split (List.map (entry_of_exp bs) es) in
  let bs' = List.flatten bss' in
  let ts' = List.map (fun e -> e, e.note) es' in
  let at = (List.hd es).at in
  bs', TupE es' $$ at % (TupT ts' $ at)
  
let env_rule_prems env id1 id2 bs prems =
  let es = List.map (fun p ->
    (match p.it with
    | RulePr (id, mixop, e) -> RuleE (id, mixop, e)
    | IfPr e -> e.it
    | LetPr (e1, e2, _) -> CmpE (EqOp, e1, e2)
    (* TODO: (lemmagen) Not yet supported *)
    | ElsePr -> BoolE true
    (* TODO: (lemmagen) Not yet supported *)
    | IterPr _ -> BoolE true)
    $$ p.at % (BoolT $ p.at)) prems in
  env := bind !env [id_rels; id1.it; "rules"; id2.it; "premises"] (entry_of_exps bs es)

let env_rule_instr_ok env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c; i; ft]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs i);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Instr_ok"

let env_rule_instrs_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c; is; ft]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs is);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Instrs_ok"

let env_rule_admininstr_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [s; c; a; ft]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "store"] (entry_of_exp bs s);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs a);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Admin_instr_ok"

let env_rule_admininstrs_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [s; c; as_; ft]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "store"] (entry_of_exp bs s);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs as_);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Admin_instrs_ok"

let env_rule_step env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c1; c2]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "before"] (entry_of_exp bs c1);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "after"] (entry_of_exp bs c2)
  | RuleD _ -> error r.at "unexpected form of rule Step"

let env_rule_step_pure env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [as1; as2]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "before"] (entry_of_exp bs as1);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "after"] (entry_of_exp bs as2)
  | RuleD _ -> error r.at "unexpected form of rule Step"

let env_rule_step_read env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c1; as2]; _}, _) ->
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "before"] (entry_of_exp bs c1);
    env := bind !env [id_rels; id1.it; "rules"; id2.it; "after"] (entry_of_exp bs as2)
  | RuleD _ -> error r.at "unexpected form of rule Step"

let env_rule env id1 r =
  match r.it with
  | RuleD (id2, bs, _, _, prems) ->
    env_rule_prems env id1 id2 bs prems;
  
  match id1.it with
  | "Instr_ok" -> env_rule_instr_ok env id1 r
  | "Instrs_ok" -> env_rule_instr_ok env id1 r
  | "Admin_instr_ok" -> env_rule_admininstr_ok env id1 r
  | "Admin_instrs_ok" -> env_rule_admininstrs_ok env id1 r
  | "Step" -> env_rule_step env id1 r
  | "Step_pure" -> env_rule_step_pure env id1 r
  | "Step_read" -> env_rule_step_read env id1 r
  | _ -> ()

let rec env_def env d =
  match d.it with
  | RecD ds -> 
    List.iter (env_def env) ds
  | TypD (id, _, _) -> 
    env := bind !env [id_typs; id.it; "name"] (entry_of_id id)
  | RelD (id, _, _, rs) -> 
    env := bind !env [id_rels; id.it; "name"] (entry_of_id id);
    List.iter (env_rule env id) rs
  | DecD (id, _, _, _) -> 
    env := bind !env [id_defs; id.it; "name"] (entry_of_id id)
  | ThmD (id, _bs, _e) | LemD (id, _bs, _e) -> 
    env := bind !env [id_thms; id.it; "name"] (entry_of_id id)
  | TmplD _ | HintD _ -> ()

let env ds : env =
  let env = new_env () in
  List.iter (env_def (ref env)) ds;
  env

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
let rec insert_trie ids s trie =
  match ids with
  | [] -> (match trie with
    | LeafI _ -> LeafI (Some s)
    | NodeI (_, cs) -> NodeI (Some s, cs))
  | id::ids' -> (match trie with
    | LeafI s' -> 
      let c = insert_trie ids' s (LeafI None) in
      let cs = Map.add id c Map.empty in
      NodeI (s', cs)
    | NodeI (s', cs) ->
      let c = match Map.find_opt id cs with
        | None -> insert_trie ids' s (LeafI None)
        | Some trie' -> insert_trie ids' s trie' in
      let cs' = Map.add id c cs in
      NodeI (s', cs'))

let make_trie ss = 
  let rec linearize' s acc =
    match s.it with
    | TopS id -> [id.it]
    | DotS (s1, id) -> linearize' s1 (id.it::acc)
    | WildS s1 -> linearize' s1 ("*"::acc)
    | VarS s1 -> linearize' s1 acc in

  let linearize s =
    List.rev (linearize' s []) in

  List.fold_left (fun acc s -> 
    let ids = linearize s in
    insert_trie ids s acc) (LeafI None) ss

type subst = slot * slotentry
type substs = subst list

type comb = substs list

let make_comb (_env : env) (_trie : slottrie) : comb = 
  failwith "unimplemented (lemmagen)"

let subst_def (_substs : substs) (_d : def) : def * bind list = 
  failwith "unimplemented (lemmagen)"

let transform ds =
  let env = env ds in
  ds
  |> List.map (fun d ->
    let slots = slots_def d in
    let trie = make_trie slots in
    let comb = make_comb env trie in
    comb 
    |> List.map (fun substs -> 
      let d', _bs = subst_def substs d in
      (* TODO: (lemmagen) Handle extra top-level binds *)
      match d'.it with
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
      | TmplD _ | HintD _ ->
        assert false))
  |> List.flatten
