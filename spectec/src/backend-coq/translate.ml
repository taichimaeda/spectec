open Il.Ast
open Util.Source

let error at msg = Util.Error.error at "Coq generation" msg
module CoqAst = Ast

module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"] |> IdSet.of_list

let rec make_id s = 
  let s' = make_id' s.it in
  s' $ s.at

and make_id' s = match s with
 | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s

let translate_atom (a : atom) = a

let translate_binop (b : binop) =
  match b with
    | AndOp -> CoqAst.AndOp
    | OrOp -> CoqAst.OrOp
    | AddOp _ -> CoqAst.AddOp
    | SubOp _ -> CoqAst.SubOp
    | ImplOp -> CoqAst.ImplOp
    | MulOp _ -> CoqAst.MulOp
    | DivOp _ -> CoqAst.DivOp
    | ExpOp _ -> CoqAst.ExpOp
    | EquivOp -> CoqAst.EquivOp

let translate_unop (u : unop) =
  match u with
    | NotOp -> CoqAst.NotOp
    | PlusOp _ -> CoqAst.PlusOp
    | MinusOp _ -> CoqAst.MinusOp
    | PlusMinusOp _ -> CoqAst.PlusMinusOp
    | MinusPlusOp _ -> CoqAst.MinusPlusOp

let translate_cmpop (c : cmpop) =
  match c with
    | EqOp -> CoqAst.EqOp
    | NeOp -> CoqAst.NeOp
    | LtOp _ -> CoqAst.LtOp
    | GtOp _ -> CoqAst.GtOp
    | LeOp _ -> CoqAst.LeOp
    | GeOp _ -> CoqAst.GeOp

let rec translate_typ (t : typ) = 
  let t' = translate_typ' t in
  t' $ t.at
and translate_typ' (t: typ) =
  match t.it with
    | VarT (id, args) -> CoqAst.VarT (make_id id, List.map translate_arg args)
    | NumT _ -> CoqAst.NatT
    | TextT -> CoqAst.TextT
    | BoolT -> CoqAst.BoolT
    | TupT typs -> CoqAst.TupT (List.map (fun (e, t) -> (translate_exp e, translate_typ t)) typs)
    | IterT (typ, iter) -> CoqAst.IterT (translate_typ typ, translate_iter iter)

and translate_exp (e : exp) = 
  let e' = translate_exp' e in
  e' $ e.at

and translate_exp' (e : exp) =
  match e.it with
    | VarE id -> CoqAst.VarE (make_id id)
    | BoolE bool -> CoqAst.BoolE bool
    | NatE nat -> CoqAst.NatE nat
    | TextE text -> CoqAst.TextE ("\"" ^ String.escaped text ^ "\"")
    | UnE (op, exp) ->  CoqAst.UnE (translate_unop op, translate_exp exp)
    | BinE (binop, exp1, exp2) -> CoqAst.BinE (translate_binop binop, translate_exp exp1, translate_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> CoqAst.CmpE (translate_cmpop cmpop, translate_exp exp1, translate_exp exp2)
    | IdxE (exp1, exp2) -> CoqAst.CallE ("lookup_total" $ no_region, ([CoqAst.ExpA (translate_exp exp1) $ exp1.at ; CoqAst.ExpA (translate_exp exp2) $ exp2.at ])) 
    | SliceE (exp1, exp2, exp3) -> CoqAst.SliceE (translate_exp exp1, translate_exp exp2, translate_exp exp3)
    | UpdE (exp, path, exp2) -> CoqAst.UpdE (translate_exp exp, translate_path path, translate_exp exp2)
    | ExtE (exp1, path, exp2) -> CoqAst.ExtE (translate_exp exp1, translate_path path, translate_exp exp2)
    | StrE expfields -> CoqAst.StrE (List.map (fun (a, e) -> (translate_atom a, translate_exp e)) expfields)       
    | DotE (exp, atom) -> CoqAst.DotE (translate_exp exp, translate_atom atom)       
    | CompE (exp, exp2) -> CoqAst.CompE (translate_exp exp, translate_exp exp2)
    | LenE exp -> CoqAst.CallE ("List.length" $ no_region, [CoqAst.ExpA (translate_exp exp) $ exp.at])                 
    | TupE exps -> CoqAst.TupE (List.map (fun e -> translate_exp e) exps)
    | CallE (id, args) -> CoqAst.CallE (id, List.map (fun a -> translate_arg a) args)
    | IterE (exp, iexp) -> CoqAst.IterE (translate_exp exp, translate_iterexp iexp)
    | OptE None -> CoqAst.OptE (None)
    | OptE (Some exp) -> CoqAst.OptE (Some (translate_exp exp))
    | TheE exp -> CoqAst.TheE (translate_exp exp)   
    | ListE exps -> CoqAst.ListE (List.map (fun e -> translate_exp e) exps)
    | CatE (exp1, exp2) -> CoqAst.CatE (translate_exp exp1, translate_exp exp2)
    | CaseE (mixop, exp) -> CoqAst.CaseE (mixop, translate_exp exp)         
    | SubE (exp, typ1, typ2) -> CoqAst.SubE (translate_exp exp, translate_typ typ1, translate_typ typ2)
    | ProjE (exp, n) -> CoqAst.ProjE (translate_exp exp, n)
    | UncaseE (exp, mixop) -> CoqAst.UncaseE (translate_exp exp, mixop)

and translate_arg (a : arg) = 
  let a' = translate_arg' a in
  a' $ a.at

and translate_iterexp (iexp: iterexp) =
  let (iter, ids) = iexp in
  (translate_iter iter, List.map (fun (id, t) -> (id, translate_typ t)) ids)

and translate_arg' (a : arg) =
  match a.it with
    | ExpA e -> CoqAst.ExpA (translate_exp e)
    | TypA t -> CoqAst.TypA (translate_typ t)

and translate_path (p : path) =
  let p' = translate_path' p in
  p' $ p.at

and translate_path' (p : path) =
  match p.it with   
    | RootP -> CoqAst.RootP
    | IdxP (path, exp) -> CoqAst.IdxP (translate_path path, translate_exp exp)
    | SliceP (path, exp1, exp2) -> CoqAst.SliceP (translate_path path, translate_exp exp1, translate_exp exp2)
    | DotP (path, atom) -> CoqAst.DotP (translate_path path, translate_atom atom)

and translate_iter (it : iter) =
  match it with
    | Opt -> CoqAst.Opt
    | List -> CoqAst.List
    | List1 -> CoqAst.List1
    | ListN (exp, id) -> CoqAst.ListN (translate_exp exp, id)

let rec translate_param (p : param) = 
  let p' = translate_param' p in
  p' $ p.at

and translate_param' (p : param) = 
  match p.it with
    | ExpP (id, typ) -> CoqAst.ExpP (make_id id, translate_typ typ)
    | TypP id -> CoqAst.TypP (make_id id)
let rec translate_premise (p : prem) =
  let p' = translate_premise' p in
  p' $ p.at
and translate_premise' (p : prem) = 
  match p.it with
    | RulePr (id, mixop, exp) -> CoqAst.RulePr (id, mixop, translate_exp exp)
    | IfPr exp -> CoqAst.IfPr (translate_exp exp)
    | LetPr (exp1, exp2, ids) -> CoqAst.LetPr (translate_exp exp1, translate_exp exp2, ids)
    | ElsePr -> CoqAst.ElsePr
    | IterPr (premise, iexp) -> CoqAst.IterPr (translate_premise premise, translate_iterexp iexp)


let rec translate_inst (i : inst) =
  let i' = translate_inst' i in
  i' $ i.at

and translate_inst' (i : inst) =
  match i.it with
    | InstD (_, args, deftyp) -> CoqAst.InstD (List.map translate_arg args, 
      let deftyp' = (match deftyp.it with
        | AliasT typ -> CoqAst.AliasT (translate_typ typ)
        | StructT typfields -> CoqAst.StructT (List.map (fun (a, (_, typ, premises), _) -> (translate_atom a, (translate_typ typ, 
                                              List.map translate_premise premises))) typfields)
        | VariantT typcases -> CoqAst.VariantT (List.map (fun (m, (_, typ, premises), _) -> (m, (translate_typ typ, 
                                              List.map translate_premise premises))) typcases)
      ) in deftyp' $ deftyp.at
    )

let rec translate_rule (r : rule) =
  let r' = translate_rule' r in 
  r' $ r.at

and translate_rule' (r : rule) =
  match r.it with
    | RuleD (id, _binds, mixop, exp, premises) -> CoqAst.RuleD (make_id id, mixop, translate_exp exp, List.map translate_premise premises)


let rec translate_clause (c : clause) =
  let c' = translate_clause' c in
  c' $ c.at
and translate_clause' (c : clause) =
  match c.it with
    | DefD (_binds, args, exp2, premises) -> CoqAst.DefD (List.map translate_arg args, translate_exp exp2, List.map translate_premise premises)
let rec translate_def (d : def) : CoqAst.def =
  let d' = translate_def' d in
  d' $ d.at

and translate_def' (d : def) =
  match d.it with
    | TypD (id, params, insts) -> CoqAst.TypD (make_id id, List.map translate_param params, List.map translate_inst insts) 
    | RelD (id, mixop, typ, rules) -> CoqAst.RelD (make_id id, mixop, translate_typ typ, List.map translate_rule rules)
    | DecD (id, params, typ, clauses) -> CoqAst.DecD (make_id id, List.map translate_param params, translate_typ typ, List.map translate_clause clauses)
    | RecD defs -> CoqAst.RecD (List.map translate_def defs)
    (* Should not happen *)
    | HintD _ -> error d.at "Hints should not be in Coq Generation"
  
let is_not_hint_def (d : def) =
  match d.it with
    | HintD _ -> false
    | _ -> true

let translate_il (il: script) = 
  List.map translate_def (List.filter is_not_hint_def il)

