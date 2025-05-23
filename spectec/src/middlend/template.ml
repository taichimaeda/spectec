
open Il.Ast
open Il.Print
open Il.Eq
open Util
open Source

module Set = Set.Make(String)
module Map = Map.Make(String)

(* Helpers *)

let error at msg = Error.error at "template" msg


(* Environment *)

(* templates can substitute exp only *)
type slotentry = bind list * exp

(* data indexed by slottrie *)
(* represented as a tree of slot entries *)
type slottree = 
  | LeafT of slotentry option  (* data at terminals only *)
  | NodeT of slottree Map.t

(* slot indices on slottree *)
(* bundled as trie (prefix tree) *)
type slottrie =
  | LeafI of slot option       (* slot at terminals only *)
  | NodeI of slottrie Map.t

type env =
  { data : slottree ref; 

    (* auxiliary data *)
    step_pure_prems : (exp * slotentry) list ref;  (* LHS to previous premises *)
    step_read_prems : (exp * slotentry) list ref;  (* LHS to previous premises *)
  }

let new_env () : env = 
  { data = ref (LeafT None);

    step_pure_prems = ref [];
    step_read_prems = ref [];
  }

let _string_of_slotentry (bs, e) = 
  [string_of_binds bs; string_of_exp e ]
  |> List.filter (fun s -> s <> "")
  |> String.concat " "

let rec _string_of_slottree tree = 
  match tree with
  | LeafT None -> "leaf()"
  | LeafT Some e -> "leaf(" ^ _string_of_slotentry e ^ ")"
  | NodeT cs -> "node(" ^ String.concat ", " 
      (Map.fold (fun k v acc -> acc @ [k ^ " -> " ^ _string_of_slottree v]) cs []) ^ ")"

let rec _string_of_slottrie trie =
  match trie with
  | LeafI s -> "leaf(" ^ Option.value ~default:"" (Option.map string_of_slot s) ^ ")"
  | NodeI cs -> "node(" ^ String.concat ", " 
      (Map.fold (fun k v acc -> acc @ [k ^ " -> " ^ _string_of_slottrie v]) cs []) ^ ")"

let _string_of_env env = 
  "data(" ^ _string_of_slottree !(env.data) ^ ")"

let rec _find tree ids =
  match ids, tree with
  | [], LeafT (Some e) -> e
  | [], LeafT None -> error no_region "empty slot"
  | [], NodeT _ -> error no_region "too short slot ids"
  | _::_, LeafT _ -> error no_region "too long slot ids"
  | id'::ids', NodeT cs ->
    let k = if id' = "" then "_" else id' in
    (match Map.find_opt k cs with
    | None -> error no_region "unexpected slot id"
    | Some env' -> _find env' ids')

let rec bind tree ids e =
  match ids, tree with
  | [], LeafT _ -> LeafT (Some e) (* overwrite *)
  | [], NodeT _ -> 
    error no_region "cannot overwrite non-terminal slot"
  | _::_, LeafT (Some _) -> 
    error no_region "cannot overwrite occupied terminal slot"
  | id::ids', LeafT None ->
    let k = if id = "" then "_" else id in
    let c = bind (LeafT None) ids' e in
    let cs = Map.add k c Map.empty in
    NodeT cs
  | id::ids', NodeT cs ->
    let k = if id = "" then "_" else id in
    let c = 
      match Map.find_opt k cs with
      | None -> bind (LeafT None) ids' e
      | Some tree' -> bind tree' ids' e in
    let cs' = Map.add k c cs in
    NodeT cs'

let rec fixpoint eq f x = 
  fixpoint' 0 eq f x

and fixpoint' c eq f x = 
  if c > 10000 then 
    error no_region "maximum recursion depth reached for fixpoint";
  let y = f x in
  if eq x y then y else fixpoint' (c + 1) eq f y

(* custom cmp that ignores pos *)
let cmp_bind b1 b2 = 
  match b1.it, b2.it with
  | ExpB (id1, _, _), ExpB (id2, _, _) -> String.compare id1.it id2.it
  | TypB id1, TypB id2 -> String.compare id1.it id2.it
  | ExpB _, TypB _ -> -1
  | TypB _, ExpB _ -> 1

(* custom mem that ignores pos *)
let mem_bind b bs =
  List.exists (eq_bind b) bs

(* custom equality that ignores the order of binds *)
let eq_binds bs1 bs2 = 
  let bs1' = List.sort cmp_bind bs1 in
  let bs2' = List.sort cmp_bind bs2 in
  List.length bs1' = List.length bs2' &&
  List.for_all2 (fun b1 b2 -> eq_bind b1 b2) bs1' bs2'

(* custom diff that maintains the order of binds *)
let diff_binds bs1 bs2 =
  List.filter (fun b1 -> not (mem_bind b1 bs2)) bs1

(* custom uniq that maintains the order of binds *)
let uniq_binds bs = 
  List.fold_left (fun acc b ->
    if mem_bind b acc then acc else b::acc) [] bs

let deps_binds all bs =
  let open Il.Free in
  let fss = List.map (fun b -> 
      match b.it with
      | ExpB (_, t, iter) ->
        let fs1 = free_typ t in
        let fss2 = List.map free_iter iter in
        let fs2 = List.fold_left union empty fss2 in
        union fs1 fs2
      | TypB _ -> empty) bs in
  let fs = List.fold_left union empty fss in
  let bs' = List.filter (fun b ->
    match b.it with 
    | ExpB (id, _, _) -> Set.mem id.it fs.varid
    | TypB id -> Set.mem id.it fs.typid) all in
  (* bs' must be before bs *)
  uniq_binds (bs' @ bs)

let binds_of_vars all fs = 
  let open Il.Free in
  let bs' = List.filter (fun b ->
    match b.it with 
    | ExpB (id, _, _) -> Set.mem id.it fs.varid
    | TypB id -> Set.mem id.it fs.typid) all in
  fixpoint eq_binds (deps_binds all) bs'

let binds_of_exp all e = 
  let open Il.Free in
  let fs = free_exp e in
  binds_of_vars all fs

let _binds_of_exps all es = 
  let open Il.Free in
  let fs = free_list free_exp es in
  binds_of_vars all fs

let binds_of_args all as_ = 
  let open Il.Free in
  let fs = free_list free_arg as_ in
  binds_of_vars all fs

let binds_of_rule all e prems = 
  let open Il.Free in
  let fs1 = free_exp e in
  let fs2 = free_list free_prem prems in
  let fs = union fs1 fs2 in
  binds_of_vars all fs

let entry_of_id id = 
  [], (TextE id.it) $$ id.at % (TextT $ id.at)

let entry_of_exp all e = 
  binds_of_exp all e, e

let env_rule_instr_ok env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c; i; ft]; _}, _) ->
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs i);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Instr_ok"

let env_rule_instrs_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c; is; ft]; _}, _) ->
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs is);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Instrs_ok"

let env_rule_admininstr_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [s; c; a; ft]; _}, _) ->
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "store"] (entry_of_exp bs s);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs a);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Admin_instr_ok"

let env_rule_admininstrs_ok env id1 r = 
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [s; c; as_; ft]; _}, _) ->
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "store"] (entry_of_exp bs s);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "context"] (entry_of_exp bs c);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "instrs"] (entry_of_exp bs as_);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "functype"] (entry_of_exp bs ft)
  | RuleD _ -> error r.at "unexpected form of rule Admin_instrs_ok"

let env_rule_step_pure env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [as1; as2]; _}, _) ->
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "before"] (entry_of_exp bs as1);
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "after"] (entry_of_exp bs as2)
  | RuleD _ -> error r.at "unexpected form of rule Step_pure"

let env_rule_step_read env id1 r =
  match r.it with
  | RuleD (id2, bs, _, {it = TupE [c1; as2]; _}, _) ->
    (match c1.it with
    | CaseE (_, {it = TupE [_; as1]; _}) -> 
      env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "before"] (entry_of_exp bs as1);
      env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "after"] (entry_of_exp bs as2)
    | _ -> error r.at "unexpected form of rule Step_read")
  | RuleD _ -> error r.at "unexpected form of rule Step_read"

let env_rule_prems env id1 r =
  let find_prevs k assoc : bind list * exp list = 
    let ents = List.filter_map (fun (k', ent) -> 
      if eq_exp k k' then Some ent else None) assoc in
    let bss, es = List.split ents in
    List.flatten bss, es in

  let add_prevs k ent assoc =
    (k, ent)::assoc in

  let neg_exp e = 
    UnE (NotOp, e) $$ e.at % (BoolT $ e.at) in

  let conj_exps es = 
    match es with 
    | [] -> BoolE true $$ no_region % (BoolT $ no_region)
    | e::es' -> List.fold_left (fun acc e1 -> 
      BinE (AndOp, e1, acc) $$ e1.at % (BoolT $ e.at)) e es' in
  
  let disj_exps es = 
    match es with 
    | [] -> BoolE true $$ no_region % (BoolT $ no_region)
    | e::es' -> List.fold_left (fun acc e1 -> 
      BinE (OrOp, e1, acc) $$ e1.at % (BoolT $ e.at)) e es' in

  let rec exp_of_prem prem =
    (match prem.it with
    | IfPr e -> e.it
    | RulePr (id, mixop, e) -> 
      RuleE (id, mixop, e)
    | LetPr (e1, e2, _) -> 
      CmpE (EqOp, e1, e2)
    | IterPr (prem1, ie) -> 
      IterE (exp_of_prem prem1, ie)
    | ElsePr -> error prem.at "unexpected otherwise premise") 
      $$ prem.at % (BoolT $ prem.at) in
      
  let exp_of_prems prevs prems =
    match prems with
    | [{it = ElsePr; _}] -> neg_exp (disj_exps prevs)
    | _ -> conj_exps (List.map exp_of_prem prems) in

  match id1.it, r.it with
  | "Step_pure", RuleD (id2, bs1, _, {it = TupE [as1; _]; _}, prems) ->
    let bs2, prevs = find_prevs as1 !(env.step_pure_prems) in
    let boole = exp_of_prems prevs prems in
    let bs' = binds_of_exp (bs1 @ bs2) boole in
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "premises"] (bs', boole);
    env.step_pure_prems := add_prevs as1 (bs', boole) !(env.step_pure_prems)
  | "Step_read", RuleD (id2, bs1, _, {it = TupE [c1; _]; _}, prems) ->
    let bs2, prevs = find_prevs c1 !(env.step_read_prems) in
    let boole = exp_of_prems prevs prems in
    let bs' = binds_of_exp (bs1 @ bs2) boole in
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "premises"] (bs', boole);
    env.step_read_prems := add_prevs c1 (bs', boole) !(env.step_read_prems)
  | _, RuleD (id2, bs1, _, _, prems) ->
    (* previous premises are not collected here *)
    let prevs = [] in
    let boole = exp_of_prems prevs prems in
    let bs' = binds_of_exp bs1 boole in
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "premises"] (bs', boole)

let env_rule_freevars env id1 r =
  match r.it with
  | RuleD (id2, bs, _, e, prems) ->
    let rec fold_iter id t its = 
      fold_iter' id t (List.rev its)
      
    and fold_iter' id t its =
      match its with
      | [] -> 
        VarE id $$ id.at % t, t
      | it::its' ->
        (* emulates annot pass in frontend *)
        let ie = it, [(id, t)] in
        let e1, t1 = fold_iter' id t its' in
        let t1' = IterT (t1, it) $ t1.at in
        let e1' = IterE (e1, ie) $$ e1.at % t1' in
        e1', t1' in

    let bs' = binds_of_rule bs e prems in
    let es = List.filter_map (fun b -> match b.it with
      | ExpB (id, t, iter) -> 
        let e', _ = fold_iter id t iter in Some e'
      | TypB _ -> None) bs' in
    let ts = List.map (fun e -> e, e.note) es in
    let at = match es with 
      | [] -> no_region
      | e::_ -> e.at in
    let tupe = TupE es $$ at % (TupT ts $ at) in
    env.data := bind !(env.data) ["relations"; id1.it; "rules"; id2.it; "freevars"] (bs', tupe)

let env_rule env id1 r =
  env_rule_prems env id1 r;
  env_rule_freevars env id1 r;
  
  match id1.it with
  | "Instr_ok" -> env_rule_instr_ok env id1 r
  | "Instrs_ok" -> env_rule_instrs_ok env id1 r
  | "Admin_instr_ok" -> env_rule_admininstr_ok env id1 r
  | "Admin_instrs_ok" -> env_rule_admininstrs_ok env id1 r
  | "Step_pure" -> env_rule_step_pure env id1 r
  | "Step_read" -> env_rule_step_read env id1 r
  | _ -> ()

(* binds must be properly handled *)
(* this includes quantifiers if collected in the future *)
let rec env_def env d =
  match d.it with
  | RecD ds -> 
    List.iter (env_def env) ds
  | TypD (id, _, _) -> 
    env.data := bind !(env.data) ["types"; id.it; "name"] (entry_of_id id)
  | RelD (id, _, _, rs) ->
    env.data := bind !(env.data) ["relations"; id.it; "name"] (entry_of_id id);
    List.iter (env_rule env id) rs
  | DecD (id, _, _, _) ->
    env.data := bind !(env.data) ["definitions"; id.it; "name"] (entry_of_id id)
  (* theorems and hints are currently not collected *)
  | ThmD _ | LemD _ | HintD _ -> ()
  | TmplD _ -> assert false

let env ds : env =
  let env = new_env () in
  List.iter (env_def env) ds;
  env


(* Collection *)

let slots_list f xs = List.flatten (List.map f xs)

let slots_pair f1 f2 (x, y) = f1 x @ f2 y

let rec slots_iter it =
  match it with
  | Opt | List | List1 -> []
  | ListN (e, _) -> slots_exp e 
  
and slots_typ t =
  match t.it with
  | VarT (_, as_) -> slots_list slots_arg as_
  | BoolT
  | NumT _
  | TextT -> []
  | TupT ets -> slots_list (slots_pair slots_exp slots_typ) ets
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
  slots_iter iter @ slots_list (slots_pair (fun _ -> []) slots_typ) bs

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
  match d.it with
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
  (* hints are currently ignored *)
  | HintD _ -> []
  | TmplD _ -> assert false


(* Combinations *)

let unwrap_varslot s : slot = 
  match s.it with
  | VarS s1 -> s1
  | _ -> s

let rec fold_slot ids : slot = 
  fold_slot' (List.rev ids)

and fold_slot' ids : slot =
  match ids with
  | [id] -> TopS (id $ no_region) $ no_region
  | "*"::ids' -> WildS (fold_slot' ids') $ no_region
  | id::ids' -> DotS (fold_slot' ids', id $ no_region) $ no_region
  | _ -> assert false

and unfold_slot s acc : string list =
  match s.it with
  | TopS id -> id.it::acc
  | DotS (s1, id) -> unfold_slot s1 (id.it::acc)
  | WildS s1 -> unfold_slot s1 ("*"::acc)
  | VarS _ -> assert false

(* TODO: (lemmagen) Is this correct? *)
let rec add_trie ids s trie =
  match ids, trie with
  | [], LeafI _ -> LeafI (Some s) (* overwrite *)
  | [], NodeI _ -> 
    error no_region "cannot overwrite non-terminal slot"
  | _::_, LeafI (Some _) -> 
    error no_region "cannot overwrite occupied terminal slot"
  | id::ids', LeafI None ->
    let c = add_trie ids' s (LeafI None) in
    let cs = Map.add id c Map.empty in
    NodeI cs
  | id::ids', NodeI cs ->
    let c = match Map.find_opt id cs with
      | None -> add_trie ids' s (LeafI None)
      | Some trie' -> add_trie ids' s trie' in
    let cs' = Map.add id c cs in
    NodeI cs'

let make_trie ss =
  List.fold_left (fun acc s -> 
    let s' = unwrap_varslot s in
    let ids = unfold_slot s' [] in
    add_trie ids s' acc) (LeafI None) ss

type subst = 
    slot      (* old slot with wildcard *)
  * slot      (* new slot without wildcard *)
  * slotentry (* slot entry to be substituted *)
type substs = subst list
type comb = substs list

let _string_of_subst (s, s', e) =
  "(" ^ string_of_slot s ^ " -> " ^ string_of_slot s' ^ " : " ^ _string_of_slotentry e ^ ")"

let _string_of_substs substs = 
  "{" ^ String.concat ",\n" (List.map _string_of_subst substs) ^ "}"

let _string_of_comb comb = 
  String.concat "\n\n" (List.map _string_of_substs comb)

let rec make_comb tree trie = 
  make_comb' tree trie []

and make_comb' tree trie ids = 
  let sum acc comb : comb = 
    acc @ comb in

  let product acc comb : comb =
    if acc = [] then comb else
    List.map (fun x -> 
    List.map (fun y -> x @ y) acc) comb
    |> List.flatten in

  (* TODO: (lemmagen) Remove this line *)
  (* let str1 = string_of_slottree tree in
  let str2 = string_of_slottrie trie in
  print_endline @@ "make_comb1: " ^ String.sub str1 0 (min (String.length str1) 100);
  print_endline @@ "make_comb2: " ^ str2; *)

  (* TODO: (lemmagen) Is this correct? *)
  try 
    match tree, trie with 
    | LeafT (Some e), LeafI (Some s) -> 
      let s' = fold_slot ids in
      [[s, s', e]]
    | NodeT cs, NodeI ds -> 
      (Map.fold (fun dk dv (acc : comb) ->
        match dk with
        | "*" -> 
          let comb = Map.fold (fun ck cv (acc' : comb) -> 
            let comb' = make_comb' cv dv (ids @ [ck]) in
            sum acc' comb') cs [] in
          product acc comb
        | _ ->
          let cv = Map.find dk cs in
          let comb = make_comb' cv dv (ids @ [dk]) in
          product acc comb) ds [])
    | LeafT _, NodeI _ -> 
      error no_region ("too long slot ids: " ^ String.concat "." ids)
    | NodeT _, LeafI _ ->
      error no_region ("too short slot ids: " ^ String.concat "." ids)
    | LeafT _, LeafI None | LeafT None, LeafI _ ->
      assert false
  with Not_found ->
    error no_region ("invalid slot ids: " ^ String.concat "." ids)


(* Repositioning *)

let repos_list f at xs = 
  List.map (f at) xs

let repos_opt f at x = 
  Option.map (f at) x

let repos_pair f1 f2 at (x, y) = 
  (f1 at x, f2 at y)

let repos_id at id : id = 
  id.it $ at

let repos_atom at atom : atom = 
  atom.it $$ at % atom.note

let repos_mixop at mixop : mixop = 
  repos_list (repos_list repos_atom) at mixop

let rec repos_iter at it : iter =
  match it with
  | Opt | List | List1 -> it
  | ListN (e, id) -> 
    ListN (repos_exp at e, repos_opt repos_id at id)

and repos_typ at t : typ =
  match t.it with
  | VarT (id, as_) -> 
    VarT (repos_id at id, repos_list repos_arg at as_) $ at
  | BoolT 
  | NumT _
  | TextT -> t.it $ at
  | TupT ets -> 
    TupT (repos_list (repos_pair repos_exp repos_typ) at ets) $ at
  | IterT (t1, it) ->
    IterT (repos_typ at t1, repos_iter at it) $ at
  | BotT -> t.it $ at

and repos_exp at e : exp = 
  match e.it with
  | VarE _ -> e.it $$ at % e.note
  | BoolE _ | NatE _ | TextE _ -> e.it $$ at % e.note
  | UnE (op, e1) ->
    UnE (op, repos_exp at e1) $$ at % e.note
  | BinE (op, e1, e2) -> 
    BinE (op, repos_exp at e1, repos_exp at e2) $$ at % e.note
  | CmpE (op, e1, e2) -> 
    CmpE (op, repos_exp at e1, repos_exp at e2) $$ at % e.note
  | TupE es -> 
    TupE (repos_list repos_exp at es) $$ at % e.note
  | ProjE (e1, i) -> 
    ProjE (repos_exp at e1, i) $$ at % e.note
  | CaseE (mixop, e1) -> 
    CaseE (repos_mixop at mixop, repos_exp at e1) $$ at % e.note
  | UncaseE (e1, mixop) -> 
    UncaseE (repos_exp at e1, repos_mixop at mixop) $$ at % e.note
  | OptE None -> e.it $$ at % e.note
  | OptE (Some e1) -> 
    OptE (Some (repos_exp at e1)) $$ at % e.note
  | TheE e1 -> 
    TheE (repos_exp at e1) $$ at % e.note
  | StrE efs -> 
    StrE (repos_list repos_expfield at efs) $$ at % e.note
  | DotE (e1, atom) ->
    DotE (repos_exp at e1, repos_atom at atom) $$ at % e.note
  | CompE (e1, e2) ->
    CompE (repos_exp at e1, repos_exp at e2) $$ at % e.note
  | ListE es -> 
    ListE (repos_list repos_exp at es) $$ at % e.note
  | LenE e1 ->
    LenE (repos_exp at e1) $$ at % e.note
  | CatE (e1, e2) ->
    CatE (repos_exp at e1, repos_exp at e2) $$ at % e.note
  | IdxE (e1, e2) ->
    IdxE (repos_exp at e1, repos_exp at e2) $$ at % e.note
  | SliceE (e1, e2, e3) ->
    SliceE (repos_exp at e1, repos_exp at e2, repos_exp at e3) $$ at % e.note
  | UpdE (e1, p1, e2) ->
    UpdE (repos_exp at e1, repos_path at p1, repos_exp at e2) $$ at % e.note
  | ExtE (e1, p1, e2) ->
    ExtE (repos_exp at e1, repos_path at p1, repos_exp at e2) $$ at % e.note
  | CallE (id, as_) -> 
    CallE (repos_id at id, repos_list repos_arg at as_) $$ at % e.note
  | IterE (e1, ie) ->
    IterE (repos_exp at e1, repos_iterexp at ie) $$ at % e.note
  | SubE (e1, t1, t2) -> 
    SubE (repos_exp at e1, repos_typ at t1, repos_typ at t2) $$ at % e.note
  | RuleE (id, mixop, e1) -> 
    RuleE (repos_id at id, repos_mixop at mixop, repos_exp at e1) $$ at % e.note
  | ForallE (bs, as_, e1) ->
    ForallE (repos_list repos_bind at bs, repos_list repos_arg at as_, repos_exp at e1) $$ at % e.note
  | ExistsE (bs, as_, e1) -> 
    ExistsE (repos_list repos_bind at bs, repos_list repos_arg at as_, repos_exp at e1) $$ at % e.note
  | TmplE _ ->
    error at "unexpected variable template expression"

and repos_expfield at (atom, e) : expfield = 
  (repos_atom at atom, repos_exp at e)

and repos_path at p : path =
  match p.it with
  | RootP -> p.it $$ at % p.note
  | IdxP (p1, e) -> 
    IdxP (repos_path at p1, repos_exp at e) $$ at % p.note
  | SliceP (p1, e1, e2) -> 
    SliceP (repos_path at p1, repos_exp at e1, repos_exp at e2) $$ at % p.note
  | DotP (p1, atom) -> 
    DotP (repos_path at p1, repos_atom at atom) $$ at % p.note

and repos_iterexp at (iter, bs) : iterexp =
  (repos_iter at iter, repos_list (repos_pair repos_id repos_typ) at bs)

and repos_arg at a : arg =
  match a.it with
  | ExpA e -> 
    ExpA (repos_exp at e) $ at
  | TypA t ->
    TypA (repos_typ at t) $ at

and repos_bind at b : bind = 
  match b.it with
  | ExpB (id, t, iter) ->
    ExpB (repos_id at id, repos_typ at t, repos_list repos_iter at iter) $ at
  | TypB id ->
    TypB (repos_id at id) $ at


(* Substitutions *)

let find_entry (substs : substs) s : slotentry =
  let subst = List.find (fun (s', _, _) -> eq_slot s s') substs in
  let (_, _, (bs, e)) = subst in
  bs, e

let subst_list f substs xs =
  let xs', bss = List.split (List.map (f substs) xs) in
  xs', List.flatten bss

let subst_pair f1 f2 substs (x, y) = 
  let x', bs1 = f1 substs x in
  let y', bs2 = f2 substs y in
  (x', y'), bs1 @ bs2

let subst_id substs id : id =
  let rec wild_ids s1 s2 =
    match s1.it, s2.it with
    | TopS id1', TopS id2' -> 
      assert (id1'.it = id2'.it);
      []
    | DotS (s1', id1'), DotS (s2', id2') -> 
      assert (id1'.it = id2'.it);
      wild_ids s1' s2'
    | WildS s1', DotS (s2', id2') -> 
      id2'.it :: wild_ids s1' s2'
    | _, _ -> assert false in

  let wids = substs
    |> List.map (fun (s, s', _) -> wild_ids s s')
    |> List.flatten in
  let sids = List.sort_uniq String.compare wids in
  let suffix = String.concat "" (List.map (fun id -> "_" ^ id) sids) in
  {id with it = id.it ^ suffix}

let rec subst_iter substs it : iter * bind list =
  match it with
  | Opt | List | List1 -> it, []
  | ListN (e, id) -> 
    let e', bs1 = subst_exp substs e in
    ListN (e', id), bs1

and subst_typ substs t : typ * bind list =
  match t.it with
  | VarT (id, as_) -> 
    let as', bs1 = subst_args substs as_ in
    VarT (id, as') $ t.at, bs1
  | BoolT 
  | NumT _
  | TextT -> t, []
  | TupT ets -> 
    let ets', bs3 = subst_list (subst_pair subst_exp subst_typ) substs ets in
    TupT ets' $ t.at, bs3
  | IterT (t1, it) ->
    let t1', bs1 = subst_typ substs t1 in
    let it', bs2 = subst_iter substs it in
    IterT (t1', it') $ t.at, bs1 @ bs2
  | BotT -> t, []

and subst_deftyp substs dt: deftyp * bind list =
  match dt.it with
  | AliasT t -> 
    let t', bs1 = subst_typ substs t in
    AliasT t' $ dt.at, bs1
  | StructT tfs ->
    let tfs', bs1 = subst_list subst_typfield substs tfs in
    StructT tfs' $ dt.at, bs1
  | VariantT tcs ->
    let tcs', bs1 = subst_list subst_typcase substs tcs in
    VariantT tcs' $ dt.at, bs1

and subst_typfield substs (atom, (bs, t, prems), hints) : typfield * bind list = 
  let t', bs1 = subst_typ substs t in
  let prems', bs2 = subst_list subst_prem substs prems in
  (atom, (bs, t', prems'), hints), bs1 @ bs2

and subst_typcase substs (mixop, (bs, t, prems), hints) : typcase * bind list =
  let t', bs1 = subst_typ substs t in
  let prems', bs2 = subst_list subst_prem substs prems in
  (mixop, (bs, t', prems'), hints), bs1 @ bs2

and subst_exp substs e : exp * bind list = 
  match e.it with
  | VarE _ -> e, []
  | BoolE _ | NatE _ | TextE _ -> e, []
  | UnE (op, e1) ->
    let e1', bs1 = subst_exp substs e1 in
    UnE (op, e1') $$ e.at % e.note, bs1
  | BinE (op, e1, e2) -> 
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    BinE (op, e1', e2') $$ e.at % e.note, bs1 @ bs2
  | CmpE (op, e1, e2) -> 
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    CmpE (op, e1', e2') $$ e.at % e.note, bs1 @ bs2
  | TupE es -> 
    let es', bs1 = subst_list subst_exp substs es in
    TupE es' $$ e.at % e.note, bs1
  | ProjE (e1, i) -> 
    let e1', bs1 = subst_exp substs e1 in
    ProjE (e1', i) $$ e.at % e.note, bs1
  | CaseE (mixop, e1) -> 
    let e1', bs1 = subst_exp substs e1 in
    CaseE (mixop, e1') $$ e.at % e.note, bs1
  | UncaseE (e1, mixop) -> 
    let e1', bs1 = subst_exp substs e1 in
    UncaseE (e1', mixop) $$ e.at % e.note, bs1
  | OptE None -> e, []
  | OptE (Some e1) -> 
    let e1', bs1 = subst_exp substs e1 in
    OptE (Some e1') $$ e.at % e.note, bs1
  | TheE e1 -> 
    let e1', bs1 = subst_exp substs e1 in
    TheE e1' $$ e.at % e.note, bs1
  | StrE efs -> 
    let efs', bs1 = subst_list subst_expfield substs efs in
    StrE efs' $$ e.at % e.note, bs1
  | DotE (e1, atom) ->
    let e1', bs1 = subst_exp substs e1 in
    DotE (e1', atom) $$ e.at % e.note, bs1
  | CompE (e1, e2) ->
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    CompE (e1', e2') $$ e.at % e.note, bs1 @ bs2
  | ListE es ->
    let es', bs1 = subst_list subst_exp substs es in
    ListE es' $$ e.at % e.note, bs1
  | LenE e1 ->
    let e1', bs1 = subst_exp substs e1 in
    LenE e1' $$ e.at % e.note, bs1
  | CatE (e1, e2) ->
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    CatE (e1', e2') $$ e.at % e.note, bs1 @ bs2
  | IdxE (e1, e2) ->
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    IdxE (e1', e2') $$ e.at % e.note, bs1 @ bs2
  | SliceE (e1, e2, e3) ->
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    let e3', bs3 = subst_exp substs e3 in
    SliceE (e1', e2', e3') $$ e.at % e.note, bs1 @ bs2 @ bs3
  | UpdE (e1, p1, e2) -> 
    let e1', bs1 = subst_exp substs e1 in
    let p1', bs2 = subst_path substs p1 in
    let e2', bs3 = subst_exp substs e2 in
    UpdE (e1', p1', e2') $$ e.at % e.note, bs1 @ bs2 @ bs3
  | ExtE (e1, p1, e2) ->
    let e1', bs1 = subst_exp substs e1 in
    let p1', bs2 = subst_path substs p1 in
    let e2', bs3 = subst_exp substs e2 in
    ExtE (e1', p1', e2') $$ e.at % e.note, bs1 @ bs2 @ bs3
  | CallE (id, as_) -> 
    let as', bs1 = subst_args substs as_ in
    CallE (id, as') $$ e.at % e.note, bs1
  | IterE (e1, ie) -> 
    let e1', bs1 = subst_exp substs e1 in
    let ie', bs2 = subst_iterexp substs ie in
    IterE (e1', ie') $$ e.at % e.note, bs1 @ bs2
  | SubE (e1, t1, t2) -> 
    let e1', bs1 = subst_exp substs e1 in
    let t1', bs2 = subst_typ substs t1 in
    let t2', bs3 = subst_typ substs t2 in
    SubE (e1', t1', t2') $$ e.at % e.note, bs1 @ bs2 @ bs3
  | RuleE (id, mixop, e1) -> 
    let e1', bs1 = subst_exp substs e1 in
    RuleE (id, mixop, e1') $$ e.at % e.note, bs1
  | ForallE (bs, as_, e1) | ExistsE (bs, as_, e1) -> 
    let as', bs1 = subst_args substs as_ in
    let e1', bs2 = subst_exp substs e1 in
    let bs1' = binds_of_args bs1 as' in
    let bs2' = diff_binds (bs1 @ bs2) bs1' in
    (match e.it with
    | ForallE _ -> ForallE (uniq_binds (bs @ bs1'), as', e1')
    | ExistsE _ -> ExistsE (uniq_binds (bs @ bs1'), as', e1')
    | _ -> assert false) $$ e.at % e.note, bs2'
  | TmplE {it = VarS _; _} ->
    error e.at "unexpected variable template expression"
  | TmplE s -> 
    let bs, e1 = find_entry substs s in
    let e1' = repos_exp e.at e1 in
    e1', bs

and subst_expfield substs (atom, e) : expfield * bind list = 
  let e', bs1 = subst_exp substs e in
  (atom, e'), bs1

and subst_path substs p : path * bind list =
  match p.it with
  | RootP -> p, []
  | IdxP (p1, e) -> 
    let p1', bs1 = subst_path substs p1 in
    let e', bs2 = subst_exp substs e in
    IdxP (p1', e') $$ p.at % p.note, bs1 @ bs2
  | SliceP (p1, e1, e2) -> 
    let p1', bs1 = subst_path substs p1 in
    let e1', bs2 = subst_exp substs e1 in
    let e2', bs3 = subst_exp substs e2 in
    SliceP (p1', e1', e2') $$ p.at % p.note, bs1 @ bs2 @ bs3
  | DotP (p1, atom) -> 
    let p1', bs1 = subst_path substs p1 in
    DotP (p1', atom) $$ p.at % p.note, bs1

and subst_iterexp substs (iter, bs) : iterexp * bind list =
  let iter', bs1 = subst_iter substs iter in
  let bs', bs2 = subst_list (subst_pair (fun _ id -> id, []) subst_typ) substs bs in
  (iter', bs'), bs1 @ bs2

and subst_prem substs prem : prem * bind list =
  match prem.it with
  | RulePr (id, mixop, e) -> 
    let e', bs1 = subst_exp substs e in
    RulePr (id, mixop, e') $ prem.at, bs1
  | IfPr e ->
    let e', bs1 = subst_exp substs e in
    IfPr e' $ prem.at, bs1
  | LetPr (e1, e2, ids) -> 
    let e1', bs1 = subst_exp substs e1 in
    let e2', bs2 = subst_exp substs e2 in
    LetPr (e1', e2', ids) $ prem.at, bs1 @ bs2
  | ElsePr -> 
    ElsePr $ prem.at, []
  | IterPr (prem1, iter) -> 
    let prem1', bs1 = subst_prem substs prem1 in
    let iter', bs2 = subst_iterexp substs iter in
    IterPr (prem1', iter') $ prem.at, bs1 @ bs2

and subst_arg substs a : arg list * bind list =
  match a.it with
  | ExpA {it = TmplE ({it = VarS s; _}); _} -> 
    let bs, e1 = find_entry substs s in
    let e1' = repos_exp a.at e1 in
    (match e1'.it with 
    | ListE es | TupE es -> 
      List.map (fun e -> ExpA e $ a.at) es, bs
    | _ -> error a.at "unexpected variable template expression")
  | ExpA e -> 
    let e', bs1 = subst_exp substs e in
    [ExpA e' $ a.at], bs1
  | TypA t ->
    let t', bs1 = subst_typ substs t in
    [TypA t' $ a.at], bs1 

and subst_args substs as_ : arg list * bind list =
  let ass, bs = subst_list subst_arg substs as_ in
  List.flatten ass, bs

and subst_param substs p : param * bind list = 
  match p.it with
  | ExpP (id, t) -> 
    let t', bs1 = subst_typ substs t in
    ExpP (id, t') $ p.at, bs1
  | TypP _ -> p, []

let subst_inst substs inst : inst * bind list =
  match inst.it with
  | InstD (bs, as_, dt) -> 
    let as', bs1 = subst_args substs as_ in
    let dt', bs2 = subst_deftyp substs dt in
    InstD (uniq_binds (bs @ bs1 @ bs2), as', dt') $ inst.at, []

let subst_rule substs rule : rule * bind list =
  match rule.it with
  | RuleD (id, bs, mixop, e, prems) ->
    let e', bs1 = subst_exp substs e in
    let prems', bs2 = subst_list subst_prem substs prems in
    RuleD (id, uniq_binds (bs @ bs1 @ bs2), mixop, e', prems') $ rule.at, []

let subst_clause substs clause : clause * bind list =
  match clause.it with
  | DefD (bs, as_, e, prems) ->
    let as', bs1 = subst_args substs as_ in
    let e', bs2 = subst_exp substs e in 
    let prems', bs3 = subst_list subst_prem substs prems in
    DefD (uniq_binds (bs @ bs1 @ bs2) @ bs3, as', e', prems') $ clause.at, []

let subst_def (substs : substs) d : def * bind list = 
  match d.it with
  | TypD (id, ps, insts) -> 
    let ps', bs1 = subst_list subst_param [] ps in
    let insts', bs2 = subst_list subst_inst substs insts in
    TypD (subst_id substs id, ps', insts') $ d.at, bs1 @ bs2
  | RelD (id, mixop, t, rules) -> 
    let t', bs1 = subst_typ [] t in
    let rules', bs2 = subst_list subst_rule substs rules in
    RelD (subst_id substs id, mixop, t', rules') $ d.at, bs1 @ bs2
  | DecD (id, ps, t, clauses) ->
    let ps', bs1 = subst_list subst_param [] ps in
    let t', bs2 = subst_typ [] t in
    let clauses', bs3 = subst_list subst_clause substs clauses in
    DecD (subst_id substs id, ps', t', clauses') $ d.at, bs1 @ bs2 @ bs3
  | ThmD (id, bs, e) ->
    let e', bs1 = subst_exp substs e in
    ThmD (subst_id substs id, uniq_binds (bs @ bs1), e') $ d.at, []
  | LemD (id, bs, e) -> 
    let e', bs1 = subst_exp substs e in
    LemD (subst_id substs id, uniq_binds (bs @ bs1), e') $ d.at, []
  (* hints are currently not substituted *)
  | HintD hdef -> HintD hdef $ d.at, []
  (* templates cannot be recurisve *)
  | RecD _ -> assert false
  | TmplD _ -> assert false


(* Simplification *)

let simpl_list f xs = List.map f xs

let simpl_pair f1 f2 (x, y) = (f1 x, f2 y)

let rec simpl_iter it : iter =
  match it with
  | Opt | List | List1 -> it
  | ListN (e, id) -> 
    ListN (simpl_exp e, id)
  
and simpl_typ t : typ =
  match t.it with
  | VarT (id, as_) -> 
    VarT (id, simpl_list simpl_arg as_) $ t.at
  | BoolT
  | NumT _
  | TextT -> t
  | TupT ets -> 
    TupT (simpl_list (simpl_pair simpl_exp simpl_typ) ets) $ t.at
  | IterT (t1, it) -> 
    IterT (simpl_typ t1, simpl_iter it) $ t.at
  | BotT -> t

and simpl_deftyp dt : deftyp =
  match dt.it with
  | AliasT t -> 
    AliasT (simpl_typ t) $ dt.at
  | StructT tfs -> 
    StructT (simpl_list simpl_typfield tfs) $ dt.at
  | VariantT tcs ->
    VariantT (simpl_list simpl_typcase tcs) $ dt.at

and simpl_typfield (atom, (bs, t, prems), hints) : typfield = 
  (atom, (bs, simpl_typ t, simpl_list simpl_prem prems), hints)
and simpl_typcase (mixop, (bs, t, prems), hints) : typcase =
  (mixop, (bs, simpl_typ t, simpl_list simpl_prem prems), hints)

and simpl_exp e : exp =
  (* hack by lazy eval *)
  let rec fsub () = simpl_expsub fsub in
  let rec fimpl () = simpl_expimpl fimpl in
  let rec fquant () = simpl_expquant fquant in
  e 
  |> simpl_expsub fsub
  |> simpl_expimpl fimpl
  |> simpl_expquant fquant

and simpl_exp' f e : exp = 
  let cont = f () in
  match e.it with
  | VarE _ -> e
  | BoolE _ | NatE _ | TextE _ -> e
  | UnE (op, e1) -> 
    UnE (op, cont e1) $$ e.at % e.note
  | BinE (op, e1, e2) ->
    BinE (op, cont e1, cont e2) $$ e.at % e.note
  | CmpE (op, e1, e2) -> 
    CmpE (op, cont e1, cont e2) $$ e.at % e.note
  | TupE es ->
    TupE (simpl_list cont es) $$ e.at % e.note
  | ProjE (e1, i) -> 
    ProjE (cont e1, i) $$ e.at % e.note
  | CaseE (mixop, e1) -> 
    CaseE (mixop, cont e1) $$ e.at % e.note
  | UncaseE (e1, mixop) -> 
    UncaseE (cont e1, mixop) $$ e.at % e.note
  | OptE None -> e
  | OptE (Some e1) -> 
    OptE (Some (cont e1)) $$ e.at % e.note
  | TheE e1 -> 
    TheE (cont e1) $$ e.at % e.note
  | StrE efs -> 
    StrE (simpl_list simpl_expfield efs) $$ e.at % e.note
  | DotE (e1, atom) ->
    DotE (cont e1, atom) $$ e.at % e.note
  | CompE (e1, e2) -> 
    CompE (cont e1, cont e2) $$ e.at % e.note
  | ListE es -> 
    ListE (simpl_list cont es) $$ e.at % e.note
  | LenE e1 ->
    LenE (cont e1) $$ e.at % e.note
  | CatE (e1, e2) -> 
    CatE (cont e1, cont e2) $$ e.at % e.note
  | IdxE (e1, e2) -> 
    IdxE (cont e1, cont e2) $$ e.at % e.note
  | SliceE (e1, e2, e3) ->
    SliceE (cont e1, cont e2, cont e3) $$ e.at % e.note
  | UpdE (e1, p1, e2) -> 
    UpdE (cont e1, simpl_path p1, cont e2) $$ e.at % e.note
  | ExtE (e1, p1, e2) -> 
    ExtE (cont e1, simpl_path p1, cont e2) $$ e.at % e.note
  | CallE (id, as_) -> 
    CallE (id, simpl_list simpl_arg as_) $$ e.at % e.note
  | IterE (e1, ie) -> 
    IterE (cont e1, simpl_iterexp ie) $$ e.at % e.note
  | SubE (e1, t1, t2) ->
    SubE (cont e1, simpl_typ t1, simpl_typ t2) $$ e.at % e.note
  | RuleE (id, mixop, e1) -> 
    RuleE (id, mixop, cont e1) $$ e.at % e.note
  | ForallE (bs, as_, e1) -> 
    ForallE (bs, simpl_list simpl_arg as_, cont e1) $$ e.at % e.note
  | ExistsE (bs, as_, e1) -> 
    ExistsE (bs, simpl_list simpl_arg as_, cont e1) $$ e.at % e.note
  | TmplE _ -> assert false

and simpl_expsub f e : exp = 
  let cont = f () in
  match e.it with
  | SubE (e1, {it = BotT; _}, t2) ->
    (* remove subsumptions from bottom type *)
    (* bottom types are temporarily assigned to templates *)
    let e1' = cont e1 in
    e1'.it $$ e1'.at % simpl_typ t2
  | _ -> simpl_exp' f e

and simpl_expimpl f e : exp =
  let cont = f () in
  match e.it with
  | BinE (ImplOp, {it = BoolE true; _}, e2) -> 
    (* simplifies redundant premises *)
    cont e2
  | BinE (ImplOp, {it = BinE (AndOp, e1, e1'); _}, e2) -> 
    (* linearises conjunction of premises *)
    (* assumes the rest of the conjunction is accumulated in e1' not e1 *)
    let e2' = BinE (ImplOp, e1', e2) $$ e.at % e.note in
    BinE (ImplOp, e1, cont e2') $$ e.at % e.note
  | _ -> simpl_exp' f e

and simpl_expquant f e : exp = 
  let cont = f () in
  match e.it with
  | ForallE (bs, as_, e1) ->
    (* removes redundant quantifiers *)
    if List.length as_ = 0 then e1 else
    ForallE (bs, simpl_list simpl_arg as_, cont e1) $$ e.at % e.note
  | ExistsE (bs, as_, e1) -> 
    if List.length as_ = 0 then e1 else
    ExistsE (bs, simpl_list simpl_arg as_, cont e1) $$ e.at % e.note
  | _ -> simpl_exp' f e

and simpl_expfield (atom, e) : expfield = 
  (atom, simpl_exp e)

and simpl_path p : path =
  match p.it with
  | RootP -> p
  | IdxP (p1, e) -> 
    IdxP (simpl_path p1, simpl_exp e) $$ p.at % p.note
  | SliceP (p1, e1, e2) ->
    SliceP (simpl_path p1, simpl_exp e1, simpl_exp e2) $$ p.at % p.note
  | DotP (p1, atom) -> 
    DotP (simpl_path p1, atom) $$ p.at % p.note

and simpl_iterexp (iter, bs) : iterexp =
  (simpl_iter iter, simpl_list (simpl_pair (fun id -> id) simpl_typ) bs)

and simpl_prem prem : prem =
  match prem.it with
  | RulePr (id, mixop, e) -> 
    RulePr (id, mixop, simpl_exp e) $ prem.at
  | IfPr e ->
    IfPr (simpl_exp e) $ prem.at
  | LetPr (e1, e2, ids) ->
    LetPr (simpl_exp e1, simpl_exp e2, ids) $ prem.at
  | ElsePr -> prem
  | IterPr (prem1, iter) -> 
    IterPr (simpl_prem prem1, simpl_iterexp iter) $ prem.at

and simpl_arg a : arg =
  match a.it with
  | ExpA e -> 
    ExpA (simpl_exp e) $ a.at
  | TypA t ->
    TypA (simpl_typ t) $ a.at

and simpl_param p : param = 
  match p.it with
  | ExpP (id, t) ->
    ExpP (id, simpl_typ t) $ p.at
  | TypP _ -> p

let simpl_inst inst : inst =
  match inst.it with
  | InstD (bs, as_, dt) -> 
    InstD (bs, simpl_list simpl_arg as_, simpl_deftyp dt) $ inst.at

let simpl_rule rule : rule =
  match rule.it with
  | RuleD (id, bs, mixop, e, prems) ->
    RuleD (id, bs, mixop, simpl_exp e, simpl_list simpl_prem prems) $ rule.at

let simpl_clause clause : clause =
  match clause.it with
  | DefD (bs, as_, e, prems) ->
    DefD (bs, simpl_list simpl_arg as_, simpl_exp e, simpl_list simpl_prem prems) $ clause.at

let rec simpl_def d = 
  match d.it with
  | TypD (id, ps, insts) -> 
    TypD (id, simpl_list simpl_param ps, simpl_list simpl_inst insts) $ d.at
  | RelD (id, mixop, t, rules) -> 
    RelD (id, mixop, simpl_typ t, simpl_list simpl_rule rules) $ d.at
  | DecD (id, ps, t, clauses) ->
    DecD (id, simpl_list simpl_param ps, simpl_typ t, simpl_list simpl_clause clauses) $ d.at
  | RecD ds -> 
    RecD (simpl_list simpl_def ds) $ d.at
  | ThmD (id, bs, e) ->
    ThmD (id, bs, simpl_exp e) $ d.at
  | LemD (id, bs, e) -> 
    LemD (id, bs, simpl_exp e) $ d.at
  (* hints are currently not simplified *)
  | HintD _ -> d
  | TmplD _ -> assert false


(* Transform *)

let partition ds = 
  List.filter (fun d -> 
    match d.it with TmplD _ -> false | _ -> true) ds,
  List.filter_map (fun d ->
    match d.it with TmplD d' -> Some d' | _ -> None) ds

let transform ds =
  let ntds, tds = partition ds in
  let env = env ntds in

  (* TODO: (lemmagen) Remove this line *)
  (* let td = List.hd tds in
  let slots = slots_def td in
  print_endline @@ "slots: " ^ String.concat ", " (List.map string_of_slot slots);
  let trie = make_trie slots in
  print_endline @@ "trie: " ^ string_of_slottrie trie;
  let comb = make_comb !(env.data) trie in
  print_endline @@ "comb: " ^ string_of_comb comb;
  let tds' = comb 
    |> List.map (fun substs -> 
      let d', bs = subst_def substs td in
      assert (bs = []); d') in
  print_endline @@ String.concat "\n" (List.map string_of_def tds');
  let () = failwith "success" in *)

  let tds' = tds
    |> List.map (fun d ->
      let slots = slots_def d in
      let trie = make_trie slots in
      let comb = make_comb !(env.data) trie in
      comb 
      |> List.map (fun substs -> 
        let d', bs = subst_def substs d in
        assert (bs = []); d'))
    |> List.flatten
    |> List.map (fun d -> 
      match d.it with
      | ThmD _ | LemD _ -> simpl_def d
      | _ -> d) in
  ntds @ tds'
