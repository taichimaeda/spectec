(*
This transformation removes uses of the `otherwise` (`ElsePr`) premise from
inductive relations.

It only supports binary relations.

1. It figures out which rules are meant by “otherwise”:

   * All previous rules
   * Excluding those that definitely can’t apply when the present rule applies
     (decided by a simple and conservative comparision of the LHS).

2. It creates an auxillary inductive unary predicate with these rules (LHS only).

3. It replaces the `ElsePr` with the negation of that rule.

*)

open Util
open Source
open Coqast

let neg_suffix = "_neg"

(* Brought from Apart.ml *)

(* Looks at an expression of type list from the back and chops off all
   known _elements_, followed by the list of all list expressions.
   Returns it all in reverse order.
 *)
 let rec to_snoc_list (e : coq_term) : coq_term list * coq_term list = match e with
  | T_list es -> List.rev es, []
  | T_app_infix (T_exp_basic T_concat, e1, e2) ->
    let tailelems2, listelems2 = to_snoc_list e2 in
    if listelems2 = []
    (* Second list is fully known? Can look at first list *)
    then let tailelems1, listelems1 = to_snoc_list e1 in
        tailelems2 @ tailelems1, listelems1
    (* Second list has unknown elements, have to stop there *)
    else tailelems2, listelems2 @ [e1]
  | _ -> [], [e]

(* We assume the expressions to be of the same type; for ill-typed inputs
  no guarantees are made. *)
let rec apart (e1 : coq_term) (e2: coq_term) : bool =
  (*
  (fun b -> if not b then Printf.eprintf "apart\n  %s\n  %s\n  %b\n" (Print.string_of_exp e1) (Print.string_of_exp e2) b; b)
  *)
  (match e1, e2 with
  (* A literal is never a literal of other type *)
  | T_exp_basic (T_nat n1), T_exp_basic (T_nat n2) -> not (n1 = n2)
  | T_exp_basic (T_int i1), T_exp_basic (T_int i2) -> not (i1 = i2)
  | T_exp_basic (T_bool b1), T_exp_basic (T_bool b2) -> not (b1 = b2)
  | T_exp_basic T_string t1, T_exp_basic T_string t2 -> not (t1 = t2)
  | T_app (a1, exp1), T_app (a2, exp2) ->
    not (a1 = a2) || List.exists2 apart exp1 exp2
  | T_exp_tuple es1, T_exp_tuple es2 when List.length es1 = List.length es2 ->
    List.exists2 apart es1 es2
  | (T_app_infix (T_exp_basic T_concat, _, _) | T_list _), (T_app_infix (T_exp_basic T_concat, _, _) | T_list _) ->
    list_exp_apart e1 e2
  | T_cast (e1, _), T_cast (e2, _) -> apart e1 e2
  (* We do not know anything about variables and functions *)
  | _ , _ -> false (* conservative *)
  )

(* Two list expressions are apart if either their manifest tail elements are apart *)
and list_exp_apart e1 e2 = snoc_list_apart (to_snoc_list e1) (to_snoc_list e2)

and snoc_list_apart (tailelems1, listelems1) (tailelems2, listelems2) =
 match tailelems1, listelems1, tailelems2, listelems2 with
 (* If the heads are apart, the lists are apart *)
 | e1 :: e1s, _, e2 :: e2s, _ -> apart e1 e2 || snoc_list_apart (e1s, listelems1) (e2s, listelems2)
 (* If one list is definitely empty and the other list definitely isn't *)
 | [], [], _ :: _, _ -> false
 | _ :: _, _, [], [] -> false
 (* Else, can't tell *)
 | _, _, _, _ -> false

(* Errors *)

let error at msg = Error.error at "else removal" msg


let is_else prem = prem = P_else

let replace_else aux_name lhs prem = match prem with
  | P_else -> P_neg (P_rule (aux_name, lhs))
  | _ -> prem

let unarize ((r_id, binds), prems, term) = 
    let lhs = match term with
      | T_exp_tuple [lhs; _] -> lhs
      | _ -> error no_region "expected manifest pair"
    in
    ((r_id, binds), prems, lhs)

let not_apart lhs (_, _, lhs2) = not (apart lhs lhs2)


let rec go id args typ1 prev_rules : relation_type_entry list -> coq_def list = function
  | [] -> [ InductiveRelationD (id, args, List.rev prev_rules) ]
  | ((r_id, binds), prems, term) as r :: rules -> 
      if List.exists is_else prems
      then
        let lhs = match term with
          | T_exp_tuple [lhs; _] -> lhs
          | _ -> error no_region "expected manifest pair"
        in
        let aux_name = id ^ "_before_" ^ r_id in
        let applicable_prev_rules = prev_rules
              |> List.map unarize
              |> List.filter (not_apart lhs)
              |> List.map (fun ((id', binds'), prems', term') -> ((id' ^ neg_suffix, binds'), prems', term'))
              |> List.rev in
        [ InductiveRelationD (aux_name, [typ1], List.rev applicable_prev_rules) ] @
        let prems' = List.map (replace_else aux_name lhs) prems in
        let rule' = ((r_id, binds), prems', term) in
        go id args typ1 (rule' :: prev_rules) rules
      else
        go id args typ1 (r :: prev_rules) rules

let rec t_def (def : coq_def) : coq_def list = match def with
  | MutualRecD defs -> [ MutualRecD (List.concat_map t_def defs) ]
  | InductiveRelationD (id, args, r_entry) -> begin match args with
    | [t1 ; _t2] ->
      go id args t1 [] r_entry
    | _ -> [def]
    end
  | _ -> [ def ]

let transform (defs : coq_script) =
  List.concat_map t_def defs