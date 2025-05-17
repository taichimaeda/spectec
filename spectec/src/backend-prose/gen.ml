open Prose
open Print
open Il
open Al.Al_util
open Il2al.Translate
open Util
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

let find_proof_hint (env : Hint.env) id = 
  if not (Hint.bound !(env.proof_def) id) then None else
  let hints = Hint.find "definition" !(env.proof_def) id in
  let hexps = List.hd hints in
  Some (Lib.String.unquote (List.hd hexps))

let find_desc_hint (env : Hint.env) id = 
  if Hint.bound !(env.desc_thm) id then
    let hints = Hint.find "theorem" !(env.desc_thm) id in
    let hexps = List.hd hints in
    Some (Lib.String.unquote (List.hd hexps))
  else if Hint.bound !(env.desc_def) id then
    let hints = Hint.find "definition" !(env.desc_def) id in
    let hexps = List.hd hints in
    Some (Lib.String.unquote (List.hd hexps))
  else 
    None

let find_prose_hint (env : Hint.env) id = 
  if not (Hint.bound !(env.prose_def) id) then None else
  let hints = Hint.find "definition" !(env.prose_def) id in
  let hexps = List.hd hints in
  Some (Lib.String.unquote (List.hd hexps))

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
    let para1 = formula_to_para env e1 in
    let para2 = formula_to_para env e2 in
    (match para2 with
    | AndP paras -> AndP (para1::paras)
    | _ -> AndP ([para1; para2]))
  | Ast.BinE (Ast.OrOp, e1, e2) -> 
    let para1 = formula_to_para env e1 in
    let para2 = formula_to_para env e2 in
    (match para2 with
    | OrP paras -> OrP (para1::paras)
    | _ -> OrP ([para1; para2]))
  | Ast.BinE (Ast.ImplOp, e1, e2) ->
    let para1 = formula_to_para env e1 in
    let para2 = formula_to_para env e2 in
    (match para2 with
    | IfP (paras, para) -> IfP (para1::paras, para)
    | _ -> IfP ([para1], para2))
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
  | Ast.RuleE (id, _, e1) when id.it = "Config_ok" ->
    (* TODO: (lemmagen) This is a hack *)
    (match exp_to_argexpr e1 with
    | [{ it = Al.Ast.TupE [{it = Al.Ast.TupE [s; c]; _}; e1']; _}; t] ->
      ValidP (Some s, Some c, e1', Some t)
    | _ -> error e.at "unrecognized form of argument in Config_ok")
  | Ast.RuleE (id, _, e1) when String.ends_with ~suffix:"_ok" id.it ->
    (match exp_to_argexpr e1 with
    | [s; c; e1'; t] -> ValidP (Some s, Some c, e1', Some t)
    | [c; e1'; t] -> ValidP (None, Some c, e1', Some t)
    | [c; e1'] -> ValidP (None, Some c, e1', None)
    | [e1'] -> ValidP (None, None, e1', None)
    | _ -> error e.at "unrecognized form of argument in rule_ok")
  | Ast.RuleE (id, _, e1) when String.starts_with ~prefix:"Step" id.it ->
    (match exp_to_argexpr e1 with
    | [e1'; e1''] -> StepP (e1', e1'')
    | _ -> error e.at "unrecognized form of argument in Step_rule")
  | Ast.RuleE (id, _, e1) ->
    let es = match e1.it with
      | Ast.TupE es -> List.map exp_to_expr es
      | _ -> [exp_to_expr e1] in
    RelP (id.it, es)
  | Ast.CallE (id, as_) when e.note.it = Ast.BoolT ->
    let es = as_
      |> List.filter_map arg_to_exp
      |> List.map exp_to_expr in
    let hint = find_prose_hint env id in
    (match hint with
    | Some fmt -> CustomP (fmt, es)
    | None -> PredP (id.it, es))
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
    let hint = find_desc_hint env id in
    let name = match hint with
      | Some desc -> desc
      | None -> id.it in
    let style = match d.it with
      | Ast.ThmD _ -> "theorem"
      | Ast.LemD _ -> "lemma"
      | _ -> assert false in
    let e' = match e.it with 
      | Ast.ForallE (bs', as_, e) -> {e with it = Ast.ForallE (bs @ bs', as_, e)}
      | Ast.ExistsE (bs', as_, e) -> {e with it = Ast.ExistsE (bs @ bs', as_, e)}
      | _ -> e in
    Stmt (name, style, id.it, formula_to_para env e')
  | _ -> assert false

let rec extract_vrules def =
  match def.it with
  | Ast.RecD defs -> List.concat_map extract_vrules defs
  | Ast.RelD (id, _, _, rules) when id.it = "Instr_ok" -> rules
  | _ -> []

(* TODO: (lemmagen) Handles theorems defined via proof hints *)
let extract_def_theorems style d = 
  match d.it with 
  | Ast.DecD (id, params, _, clauses) ->
    if params <> [] then 
      error d.at "theorem takes no arguments";
    if List.length clauses <> 1 then
      error d.at "theorem takes exactly one clause";
    let clause = List.hd clauses in
    let DefD (bs, _, e, _) = clause.it in
    (match style with
    | "theorem" -> [Ast.ThmD (id, bs, e) $ d.at]
    | "lemma" -> [Ast.LemD (id, bs, e) $ d.at]
    | _ -> error d.at "unsupported theorem style")
  | _ -> assert false

let extract_theorems env d = 
  match d.it with
  | Ast.ThmD _ | Ast.LemD _ -> [d]
  | Ast.DecD (id, _, _, _) -> 
    let hint = find_proof_hint env id in
    (match hint with 
    | Some style -> extract_def_theorems style d
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
