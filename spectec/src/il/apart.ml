open Util.Source
open Ast

(* Turns an expression of list with a know tail into the tail elements (reverse
   order), and the initial part
 *)
let rec to_snoc_list (e : exp) : exp list * exp = match e.it with
  | ListE es -> List.rev es, (ListE [] $ e.at)
  | CatE (e1, e2) ->
    let revtail2, init2 = to_snoc_list e2 in
    if init2.it = ListE []
    then let revtail1, init = to_snoc_list e1 in
         revtail2 @ revtail1, init
    else revtail2, CatE (e1, init2) $ e.at
  | _ -> [], e

(* Are these two open terms definitely apart? *)
(* We only care about expression of the same type, and do not bother
   returning true for different types. *)
let rec apart (e1 : exp) (e2: exp) : bool =
  if Eq.eq_exp e1 e2 then false else
  (*
  (fun b -> if not b then Printf.eprintf "apart\n  %s\n  %s\n  %b\n" (Print.string_of_exp e1) (Print.string_of_exp e2) b; b)
  *)
  (match e1.it, e2.it with
  (* A literal is never a literal of other type *)
  | NatE n1, NatE n2 -> not (n1 = n2)
  | BoolE b1, BoolE b2 -> not (b1 = b2)
  | TextE t1, TextE t2 -> not (t1 = t2)
  | CaseE (a1, exp1, _), CaseE (a2, exp2, _) ->
    not (a1 = a2) || apart exp1 exp2
  | TupE es1, TupE es2 when List.length es1 = List.length es2 ->
    List.exists2 apart es1 es2
  | (CatE _ | ListE _), (CatE _ | ListE _) ->
    list_exp_apart e1 e2
  | SubE (e1, _, _), SubE (e2, _, _) -> apart e1 e2
  | MixE (mixop1, e1), MixE (mixop2, e2) ->
    not (mixop1 = mixop2) || apart e1 e2
  (* We do not know anything about variables and functions *)
  | _ , _ -> false (* conservative *)
  )

and list_exp_apart e1 e2 =
  let revtail1, init1 = to_snoc_list e1 in
  let revtail2, init2 = to_snoc_list e2 in
  List.exists2 apart revtail1 revtail2 ||
  (if List.length revtail1 = List.length revtail2 && revtail1 != []
  then apart init1 init2
  else false)
