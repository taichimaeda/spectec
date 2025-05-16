open Prose
open Print
open Il
open Al.Al_util
open Il2al.Translate
open Util.Source
open Util.Error


(* Errors *)

let error at msg = error at "prose generation" msg

let print_yet_prem prem fname =
  let s = Il.Print.string_of_prem prem in
  print_yet prem.at fname ("`" ^ s ^ "`")

let print_yet_exp exp fname =
  let s = Il.Print.string_of_exp exp in
  print_yet exp.at fname ("`" ^ s ^ "`")


let cmpop_to_cmpop = function
| Ast.EqOp -> Eq
| Ast.NeOp -> Ne
| Ast.LtOp _ -> Lt
| Ast.GtOp _ -> Gt
| Ast.LeOp _ -> Le
| Ast.GeOp _ -> Ge

let swap = function Lt -> Gt | Gt -> Lt | Le -> Ge | Ge -> Le | op -> op

let transpile_expr =
  Al.Walk.walk_expr { Al.Walk.default_config with
    post_expr = Il2al.Transpile.simplify_record_concat
  }

let exp_to_expr e = translate_exp e |> transpile_expr
let exp_to_argexpr es = translate_argexp es |> List.map transpile_expr

let rec if_expr_to_instrs e =
  match e.it with
  | Ast.CmpE (op, e1, e2) ->
    let op = cmpop_to_cmpop op in
    let e1 = exp_to_expr e1 in
    let e2 = exp_to_expr e2 in
    [ match e2.it with LenE _ -> CmpI (e2, swap op, e1) | _ -> CmpI (e1, op, e2) ]
  | Ast.BinE (Ast.AndOp, e1, e2) ->
    if_expr_to_instrs e1 @ if_expr_to_instrs e2
  | Ast.BinE (Ast.OrOp, e1, e2) ->
    let neg_cond = if_expr_to_instrs e1 in
    let body = if_expr_to_instrs e2 in
    [ match neg_cond with
      | [ CmpI ({ it = IterE ({ it = VarE name; _ }, _, Opt); _ }, Eq, { it = OptE None; _ }) ] ->
        IfI (isDefinedE (varE name), body)
      | _ -> print_yet_exp e "if_expr_to_instrs"; YetI (Il.Print.string_of_exp e) ]
  | Ast.BinE (Ast.EquivOp, e1, e2) ->
      [ EquivI (exp_to_expr e1, exp_to_expr e2) ]
  | _ -> print_yet_exp e "if_expr_to_instrs"; [ YetI (Il.Print.string_of_exp e) ]

let rec prem_to_instrs prem = match prem.it with
  | Ast.LetPr (e1, e2, _) ->
    [ LetI (exp_to_expr e1, exp_to_expr e2) ]
  | Ast.IfPr e ->
    if_expr_to_instrs e
  | Ast.RulePr (id, _, e) when String.ends_with ~suffix:"_ok" id.it ->
    (match exp_to_argexpr e with
    | [c; e'; t] -> [ MustValidI (c, e', Some t) ]
    | [c; e'] -> [ MustValidI (c, e', None) ]
    | _ -> error e.at "unrecognized form of argument in rule_ok"
    )
  | Ast.RulePr (id, _, e) when String.ends_with ~suffix:"_sub" id.it ->
    (match exp_to_argexpr e with
    | [t1; t2] -> [ MustMatchI (t1, t2) ]
    | _ -> print_yet_prem prem "prem_to_instrs"; [ YetI "TODO: prem_to_instrs rule_sub" ]
    )
  | Ast.IterPr (prem, iter) ->
    (match iter with
    | Ast.Opt, [(id, _)] -> [ IfI (isDefinedE (varE id.it), prem_to_instrs prem) ]
    | Ast.(List | ListN _), [(id, _)] ->
        let name = varE id.it in
        [ ForallI (name, iterE (name, [id.it], Al.Ast.List), prem_to_instrs prem) ]
    | _ -> print_yet_prem prem "prem_to_instrs"; [ YetI "TODO: prem_to_intrs iter" ]
    )
  | _ ->
    let s = Il.Print.string_of_prem prem in
    print_yet_prem prem "prem_to_instrs"; [ YetI s ]

let get_proof_hint (env : Hint.env) id = 
  if not (Hint.bound !(env.proof_def) id) then None else
  let hints = Hint.find "definition" !(env.proof_def) id in
  let hexps = List.hd hints in
  Some (List.hd hexps)

let get_para_hint (env : Hint.env) id = 
  if not (Hint.bound !(env.para_def) id) then None else
  let hints = Hint.find "definition" !(env.para_def) id in
  let hexps = List.hd hints in
  Some hexps

let bind_to_exp b = 
  match b.it with
  | Ast.ExpB (id, t, iters) ->
    let e, _ = List.fold_left (fun (e, t) iter -> 
      (Ast.IterE (e, (iter, [])) $$ id.at % t, Ast.IterT (t, iter) $ t.at))
      (Ast.VarE id $$ id.at % t, t) iters in
    Some e
  | Ast.TypB _ -> None

let arg_to_exp a =
  match a.it with
  | Ast.ExpA e -> Some e
  | _ -> None

let rec formula_to_para env e : para = 
  match e.it with
  | Ast.CmpE (op, e1, e2) ->
    let op = cmpop_to_cmpop op in
    CmpP (op, exp_to_expr e1, exp_to_expr e2)
  | Ast.UnE (Ast.NotOp, e1) -> 
    NotP (formula_to_para env e1)
  | Ast.BinE (Ast.AndOp, e1, e2) -> 
    AndP (formula_to_para env e1, formula_to_para env e2)
  | Ast.BinE (Ast.OrOp, e1, e2) -> 
    OrP (formula_to_para env e1, formula_to_para env e2)
  | Ast.BinE (Ast.ImplOp, e1, e2) -> 
    IfP (formula_to_para env e1, formula_to_para env e2)
  | Ast.BinE (Ast.EquivOp, e1, e2) -> 
    IffP (formula_to_para env e1, formula_to_para env e2)
  | Ast.ForallE (bs, _, e1) -> 
    let es = bs
      |> List.filter_map bind_to_exp
      |> List.map exp_to_expr in
    ForallP (es, formula_to_para env e1)
  | Ast.ExistsE (bs, _, e1) ->
    let es = bs
      |> List.filter_map bind_to_exp
      |> List.map exp_to_expr in
    ExistsP (es, formula_to_para env e1)
  | Ast.RuleE (id, mixop, e1) ->
    let ss = List.map (fun atoms -> atoms 
      |> List.map Il.Print.string_of_atom 
      |> String.concat " ") mixop in
    let es = match e1.it with
      | Ast.TupE es -> List.map exp_to_expr es
      | _ -> assert false in
    RelP (id.it, (ss, es))
  | Ast.CallE (id, as_) when e.note.it = Ast.BoolT ->
    let es = as_
      |> List.filter_map arg_to_exp
      |> List.map exp_to_expr in
    let hint = get_para_hint env id in
    (match hint with
    | Some ss -> 
      CustomP (ss, es)
    | None ->
      PredP (id.it, es))
  | _ when e.note.it = Ast.BoolT ->
    ExpP (exp_to_expr e)
  | _ -> 
    let s = Il.Print.string_of_exp e in
    print_yet_exp e "formula_to_para"; YetP s

type vrule_group =
  string * (Ast.exp * Ast.exp * Ast.prem list * Ast.bind list) list

(** Main translation for typing rules **)
let vrule_group_to_prose ((_name, vrules): vrule_group) =
  let (winstr, t, prems, _tenv) = vrules |> List.hd in

  (* name *)
  let name = match winstr.it with
  | Ast.CaseE (({it = (Il.Atom.Atom _) as atom'; note; _}::_)::_, _) -> atom', note.def
  | _ -> assert false
  in
  (* params *)
  let params = get_params winstr |> List.map exp_to_expr in
  (* body *)
  let body = (List.concat_map prem_to_instrs prems) @ [ IsValidI (Some (exp_to_expr t)) ] in

  (* Predicate *)
  Pred (name, params, body)

let theorem_to_prose env d =
  match d.it with
  | Ast.ThmD (id, bs, e) | Ast.LemD (id, bs, e) ->
    let e' = match e.it with 
      | Ast.ForallE (bs', as_, e) -> {e with it = Ast.ForallE (bs @ bs', as_, e)}
      | Ast.ExistsE (bs', as_, e) -> {e with it = Ast.ExistsE (bs @ bs', as_, e)}
      | _ -> e in
    Thrm (id.it, formula_to_para env e')
  | _ -> assert false

let rec extract_vrules def =
  match def.it with
  | Ast.RecD defs -> List.concat_map extract_vrules defs
  | Ast.RelD (id, _, _, rules) when id.it = "Instr_ok" -> rules
  | _ -> []

let extract_theorems env d = 
  match d.it with
  | Ast.ThmD _ | Ast.LemD _ -> [d]
  | Ast.DecD (id, params, _, clauses) -> 
    let hint = get_proof_hint env id in
    (match hint with 
    | Some ("\"theorem\"" | "\"lemma\"" as s) ->
      if params <> [] then 
        error d.at "theorem takes no arguments";
      if List.length clauses <> 1 then
        error d.at "theorem takes exactly one clause";
      let clause = List.hd clauses in
      let DefD (bs, _, e, _) = clause.it in
      (match s with
      | "\"theorem\"" -> [Ast.ThmD (id, bs, e) $ d.at]
      | "\"lemma\"" -> [Ast.LemD (id, bs, e) $ d.at]
      | _ -> assert false)
    | Some _ -> error d.at "unsupported theorem style"
    | None -> [])
  | _ -> []

let pack_vrule vrule =
  match vrule.it with
  | Ast.RuleD (_, tenv, _, exp, prems) ->
    match exp.it with
    (* c |- e : t *)
    | Ast.TupE [ _c; e; t ] -> (e, t, prems, tenv)
    | _ -> error exp.at
      (Print.string_of_exp exp
      |> Printf.sprintf "exp `%s` cannot be typing rule")

(* group typing rules that have same name *)
(* Il.rule list -> vrule_group list *)
let rec group_vrules = function
  | [] -> []
  | h :: t ->
      let name = name_of_rule h in
      let same_rules, diff_rules =
        List.partition (fun rule -> name_of_rule rule = name) t in
      let group = (name, List.map pack_vrule (h :: same_rules)) in
      group :: group_vrules diff_rules

(** Entry for generating validation prose **)
let gen_validation_prose il =
  il
  |> List.concat_map extract_vrules
  |> group_vrules
  |> List.map vrule_group_to_prose

(** Entry for generating execution prose **)
let gen_execution_prose =
  List.map
    (fun algo ->
      let handle_state = match algo with
      | Al.Ast.RuleA _ -> Il2al.Transpile.insert_state_binding
      | Al.Ast.FuncA _ -> Il2al.Transpile.remove_state
      in
      let algo =
        handle_state algo
        |> Il2al.Transpile.remove_exit
        |> Il2al.Transpile.remove_enter
      in
      Prose.Algo algo)

let gen_theorem_prose il = 
  let env = Hint.new_env () in
  List.iter (Hint.env_def env) il;
  il
  |> List.concat_map (extract_theorems env)
  |> List.map (theorem_to_prose env)

(** Main entry for generating prose **)
let gen_prose il al =
  let validation_prose = gen_validation_prose il in
  let execution_prose = gen_execution_prose al in
  let theorem_prose = gen_theorem_prose il in
  validation_prose @ execution_prose @ theorem_prose

(** Main entry for generating stringified prose **)
let gen_string il al = string_of_prose (gen_prose il al)
