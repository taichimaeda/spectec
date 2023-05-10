(*
This transformation make explicit the following implicit side conditions
of terms in premises and conclusions:

 * Array access          a[i]         i < |a|
 * Joint iteration       e*{v1,v2}    |v1*| = |v2*|
 * Option projection     !(e)         e =!= null

(The option projection would probably be nicer by rewriting !(e) to a fresh
variable x and require e=?x. Maybe later.)
*)

open Util
open Source
open Il.Ast

(* Errors *)

let _error at msg = Source.error at "sideconditions" msg

module Env = Map.Make(String)

type env = {
  vars : typ Env.t;
  var_counter : int ref;
}

let is_null e = CmpE (EqOp, e, OptE None $$ no_region % e.note) $$ no_region % (BoolT $ e.at)
let iffE e1 e2 = IfPr (BinE (EquivOp, e1, e2) $$ no_region % (BoolT $ no_region)) $ no_region
let same_len e1 e2 = IfPr (CmpE (EqOp, LenE e1 $$ no_region % (NatT $ e1.at), LenE e2 $$ no_region % (NatT $ e2.at)) $$ no_region % (BoolT $ no_region)) $ no_region
let has_len ne e = IfPr (CmpE (EqOp, LenE e $$ no_region % (NatT $ e.at), ne) $$ no_region % (BoolT $ no_region)) $ no_region

(* Fresh name generation *)

let name i = "i" ^ string_of_int i (* no clash avoidance *)

let fresh_id env : id =
  let i = !(env.var_counter) in
  incr env.var_counter;
  name i $ no_region

let t_list t xs =
  let xs', extra_premss = List.split (List.map t xs) in
  xs', List.concat extra_premss

let iter_side_conditions env ((iter, vs) : iterexp) : (id option * premise) list =
  let iter' = if iter = Opt then Opt else List in
  let ves = List.map (fun v ->
    let t = Env.find v.it env.vars in
    IterE (VarE v $$ no_region % t, (iter, [v])) $$ no_region % (IterT (t, iter') $ no_region)) vs in
 match iter, ves with
  | _, [] -> []
  | Opt, (e::es) -> List.map (fun e' -> (None, iffE (is_null e) (is_null e'))) es
  | (List|List1), (e::es) -> List.map (fun e2 -> (None, same_len e e2)) es
  (* Note that even if ne is an expression, we do not generate side conditions for it, as in practice, it is atomic *)
  | ListN ne, es -> List.map (fun e -> (None, has_len ne e)) es

(* Expr traversal *)
let rec t_exp env e : exp * (id option * premise) list =
  let it, extra_prems = t_exp' env e.it in
  {e with it}, extra_prems

and t_exp' env = function
  (* First the conditions to be generated here *)
  | IdxE (e1, e2, _) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    let id = fresh_id env in
    let prem = IfPr (CmpE (LtOp, e2', LenE e1' $$ no_region % e2'.note) $$ no_region % (BoolT $ no_region)) $ no_region in
    IdxE (e1', e2', Some id), [(Some id, prem)] @ extra_prems1 @ extra_prems2
  | TheE e ->
    let e', extra_prems1 = t_exp env e in
    let prem = IfPr (CmpE (NeOp, e', OptE None $$ no_region % e'.note) $$ no_region % (BoolT $ no_region)) $ no_region in
    TheE e', [(None, prem)] @ extra_prems1
  | IterE (e, iter) ->
    let e', extra_prems1 = t_exp env e in
    let extra_prems2 = iter_side_conditions env iter in
    IterE (e', iter), extra_prems1 @ extra_prems2
  (* And now descend *)
  | (VarE _ | BoolE _ | NatE _ | TextE _) as e ->
    e, []
  | UnE (op, e1) ->
    let e1', extra_prems1 = t_exp env e1 in
    UnE (op, e1'), extra_prems1
  | BinE (op, e1, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    BinE (op, e1', e2'), extra_prems1 @ extra_prems2
  | CmpE (op, e1, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    CmpE (op, e1', e2'), extra_prems1 @ extra_prems2
  | SliceE (e1, e2, e3) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    let e3', extra_prems3 = t_exp env e3 in
    SliceE (e1', e2', e3'), extra_prems1 @ extra_prems2 @ extra_prems3
  | UpdE (e1, p, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let p', extra_prems2 = t_path env p in
    let e2', extra_prems3 = t_exp env e2 in
    UpdE (e1', p', e2'), extra_prems1 @ extra_prems2 @ extra_prems3
  | ExtE (e1, p, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let p', extra_prems2 = t_path env p in
    let e2', extra_prems3 = t_exp env e2 in
    ExtE (e1', p', e2'), extra_prems1 @ extra_prems2 @ extra_prems3
  | StrE efs ->
    let t_expfield (a, e) =
      let e', extra_prems = t_exp env e in
      (a, e'), extra_prems
    in
    let efs', extra_prems = t_list t_expfield efs in
    StrE efs', extra_prems
  | DotE (e1, atom) ->
    let e1', extra_prems1 = t_exp env e1 in
    DotE (e1', atom), extra_prems1
  | CompE (e1, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    CompE (e1', e2'), extra_prems1 @ extra_prems2
  | LenE e1 ->
    let e1', extra_prems1 = t_exp env e1 in
    LenE e1', extra_prems1
  | TupE es ->
    let es', extra_prems = t_list (t_exp env) es in
    TupE es', extra_prems
  | MixE (op, e1) ->
    let e1', extra_prems1 = t_exp env e1 in
    MixE (op, e1'), extra_prems1
  | CallE (id, e1) ->
    let e1', extra_prems1 = t_exp env e1 in
    CallE (id, e1'), extra_prems1
  | OptE None ->
    OptE None, []
  | OptE (Some e1) ->
    let e1', extra_prems1 = t_exp env e1 in
    OptE (Some e1'), extra_prems1
  | ListE es ->
    let es', extra_prems = t_list (t_exp env) es in
    ListE es', extra_prems
  | CatE (e1, e2) ->
    let e1', extra_prems1 = t_exp env e1 in
    let e2', extra_prems2 = t_exp env e2 in
    CatE (e1', e2'), extra_prems1 @ extra_prems2
  | CaseE (atom, e1) ->
    let e1', extra_prems1 = t_exp env e1 in
    CaseE (atom, e1'), extra_prems1
  | SubE (e1, t1, t2) ->
    let e1', extra_prems1 = t_exp env e1 in
    SubE (e1', t1, t2), extra_prems1

and t_iterexp env (iter, vs) =
  let iter', extra_prems = t_iter env iter in
  (iter', vs), extra_prems

and t_iter env = function
  | ListN e ->
      let e', extra_prems = t_exp env e in
      ListN e', extra_prems
  | (Opt | List | List1) as iter -> iter, []

and t_path env path =
  let it, extra_prems = t_path' env path.it in
  {path with it}, extra_prems

and t_path' env = function
  | RootP -> RootP, []
  | IdxP (path, e) ->
      let path', extra_prems = t_path env path in
      let e', extra_prems1 = t_exp env e in
      IdxP (path', e'), extra_prems @ extra_prems1
  | SliceP (path, e1, e2) ->
      let path', extra_prems = t_path env path in
      let e1', extra_prems1 = t_exp env e1 in
      let e2', extra_prems2 = t_exp env e2 in
      SliceP (path', e1', e2'), extra_prems @ extra_prems1 @ extra_prems2
  | DotP (path, a) ->
      let path', extra_prems = t_path env path in
      DotP (path', a), extra_prems


let rec t_prem env prem =
  let it, extra_prems = t_prem' env prem.it in
  {prem with it}, extra_prems
  
and t_prem' env = function
  | RulePr (id, op, e) ->
      let e', extra_prems = t_exp env e in
      RulePr (id, op, e'), extra_prems
  | IfPr e ->
      let e', extra_prems = t_exp env e in
      IfPr e', extra_prems
  | ElsePr -> ElsePr, []
  | IterPr (prem, iterexp) ->
      let prem', extra_prems1 = t_prem env prem in
      let iterexp', extra_prems2 = t_iterexp env iterexp in
      let iter_extra_prems1 = List.map (fun (id, pr) -> (id, IterPr (pr, iterexp') $ no_region)) extra_prems1 in
      IterPr (prem', iterexp'), iter_side_conditions env iterexp @ iter_extra_prems1 @ extra_prems2

let t_named_prem env (id, prem) =
  let prem', extra_prems = t_prem env prem in
  (id, prem'), extra_prems

let t_named_prems env = t_list (t_named_prem env)

(* Does prem1 obviously imply prem2? *)
let rec implies prem1 prem2 = Il.Eq.eq_prem prem1 prem2 ||
  match prem2.it with
  | IterPr (prem2', _) -> implies prem1 prem2'
  | _ -> false

let named_implies (_id1, prem1) (_id2, prem2) = implies prem1 prem2

let t_rule' = function
  | RuleD (id, binds, mixop, exp, named_prems) ->
    (* Counter for fresh variables *)
    let env = {
      vars = List.fold_left (fun env (v, t, _) -> Env.add v.it t env) Env.empty binds;
      var_counter = ref 0;
    } in
    let exp', extra_prems1 = t_exp env exp in
    let named_prems', extra_prems2 = t_named_prems env named_prems in
    let named_prems'' = Util.Lib.List.nub named_implies (extra_prems2 @ extra_prems1 @ named_prems') in
    RuleD (id, binds, mixop, exp', named_prems'')

let t_rule x = { x with it = t_rule' x.it }

let t_rules = List.map t_rule

let rec t_def' = function
  | RecD defs -> RecD (List.map t_def defs)
  | RelD (id, mixop, typ, rules) ->
    RelD (id, mixop, typ, t_rules rules)
  | def -> def

and t_def x = { x with it = t_def' x.it }

let transform (defs : script) =
  List.map t_def defs

