open Ast


(* Are these two open terms definitely apart? *)
(* We only care about expression of the same type, and do not bother
   returning true for different types. *)
let rec apart (e1 : exp) (e2: exp) : bool =
  match e1.it, e2.it with
  (* A literal is never a literal of other type *)
  | NatE n1, NatE n2 -> not (n1 = n2)
  | BoolE b1, BoolE b2 -> not (b1 = b2)
  | TextE t1, TextE t2 -> not (t1 = t2)
  | CaseE (a1, exp1, _), CaseE (a2, exp2, _) ->
    not (a1 = a2) || apart exp1 exp2
  | TupE es1, TupE es2 when List.length es1 = List.length es2 ->
    List.exists2 apart es1 es2
  | ListE es1, ListE es2 ->
    not (List.length es1 = List.length es2) || List.exists2 apart es1 es2
  | CatE (e1, es1), CatE (e2, es2) ->
    apart e1 e2 || apart es1 es2
  (* We do not know anything about variables and functions *)
  | _ , _ -> false (* conservative *)

