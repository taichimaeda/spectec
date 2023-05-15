open Util
open Ast
open Source

module Exp = struct
  module type TRAVERSAL = sig
    val exp : exp' * typ * Source.region -> 'acc -> exp * 'acc
    val var : id -> 'acc -> exp' * 'acc
    val bool : bool -> 'acc -> exp' * 'acc
    val nat : nat -> 'acc -> exp' * 'acc
    val text : text -> 'acc -> exp' * 'acc
    val un : unop * exp -> 'acc -> exp' * 'acc
    val bin : binop * exp * exp -> 'acc -> exp' * 'acc
    val cmp : cmpop * exp * exp -> 'acc -> exp' * 'acc
    val idx : exp * exp -> 'acc -> exp' * 'acc
    val slice : exp * exp * exp -> 'acc -> exp' * 'acc
    val upd : exp * path * exp -> 'acc -> exp' * 'acc
    val ext : exp * path * exp -> 'acc -> exp' * 'acc
    val str : expfield list -> 'acc -> exp' * 'acc
    val dot : exp * atom -> 'acc -> exp' * 'acc
    val comp : exp * exp -> 'acc -> exp' * 'acc
    val len : exp -> 'acc -> exp' * 'acc
    val tup : exp list -> 'acc -> exp' * 'acc
    val mix : mixop * exp -> 'acc -> exp' * 'acc
    val call : id * exp -> 'acc -> exp' * 'acc
    val iter : exp * iterexp -> 'acc -> exp' * 'acc
    val opt : exp option -> 'acc -> exp' * 'acc
    val the : exp -> 'acc -> exp' * 'acc
    val list : exp list -> 'acc -> exp' * 'acc
    val cat : exp * exp -> 'acc -> exp' * 'acc
    val case : atom * exp -> 'acc -> exp' * 'acc
    val sub : exp * typ * typ -> 'acc -> exp' * 'acc
  end

  module Id : TRAVERSAL = struct
    let exp (e, t, at) acc = ({ it = e; note = t; at }, acc)
    let var x acc = (VarE x, acc)
    let bool b acc = (BoolE b, acc)
    let nat n acc = (NatE n, acc)
    let text t acc = (TextE t, acc)
    let un (op, e) acc = (UnE (op, e), acc)
    let bin (op, e1, e2) acc = (BinE (op, e1, e2), acc)
    let cmp (op, e1, e2) acc = (CmpE (op, e1, e2), acc)
    let idx (e1, e2) acc = (IdxE (e1, e2), acc)
    let slice (e1, e2, e3) acc = (SliceE (e1, e2, e3), acc)
    let upd (e1, p, e2) acc = (UpdE (e1, p, e2), acc)
    let ext (e1, p, e2) acc = (ExtE (e1, p, e2), acc)
    let str es acc = (StrE es, acc)
    let dot (e, x) acc = (DotE (e, x), acc)
    let comp (e1, e2) acc = (CompE (e1, e2), acc)
    let len e acc = (LenE e, acc)
    let tup es acc = (TupE es, acc)
    let mix (op, e) acc = (MixE (op, e), acc)
    let call (x, e) acc = (CallE (x, e), acc)
    let iter (e, ie) acc = (IterE (e, ie), acc)
    let opt eo acc = (OptE eo, acc)
    let the e acc = (TheE e, acc)
    let list es acc = (ListE es, acc)
    let cat (e1, e2) acc = (CatE (e1, e2), acc)
    let case (x, e) acc = (CaseE (x, e), acc)
    let sub (e, t1, t2) acc = (SubE (e, t1, t2), acc)
  end

  module Run (T : TRAVERSAL) = struct
    let rec fold e acc =
      let e', acc' = fold' e.it acc in
      T.exp (e', e.note, e.at) acc'

    and fold' exp' acc =
      match exp' with
      | VarE x -> T.var x acc
      | BoolE b -> T.bool b acc
      | NatE n -> T.nat n acc
      | TextE t -> T.text t acc
      | UnE (op, e) ->
          let e', acc' = fold e acc in
          T.un (op, e') acc'
      | BinE (op, e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.bin (op, e1', e2') acc''
      | CmpE (op, e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.cmp (op, e1', e2') acc''
      | IdxE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.idx (e1', e2') acc''
      | SliceE (e1, e2, e3) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          let e3', acc''' = fold e3 acc'' in
          T.slice (e1', e2', e3') acc'''
      | UpdE (e1, p, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.upd (e1', p, e2') acc''
      | ExtE (e1, p, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.ext (e1', p, e2') acc''
      | StrE es ->
          let es', acc' = fold_fieldlist es acc in
          T.str es' acc'
      | DotE (e, x) ->
          let e', acc' = fold e acc in
          T.dot (e', x) acc'
      | CompE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.comp (e1', e2') acc''
      | LenE e ->
          let e', acc' = fold e acc in
          T.len e' acc'
      | TupE es ->
          let es', acc' = fold_list es acc in
          T.tup es' acc'
      | MixE (op, e) ->
          let e', acc' = fold e acc in
          T.mix (op, e') acc'
      | CallE (x, e) ->
          let e', acc' = fold e acc in
          T.call (x, e') acc'
      | IterE (e, ie) ->
          let e', acc' = fold e acc in
          T.iter (e', ie) acc'
      | OptE eo ->
          let eo', acc' = fold_option eo acc in
          T.opt eo' acc'
      | TheE e ->
          let e', acc' = fold e acc in
          T.the e' acc'
      | ListE es ->
          let es', acc' = fold_list es acc in
          T.list es' acc'
      | CatE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.cat (e1', e2') acc''
      | CaseE (x, e) ->
          let e', acc' = fold e acc in
          T.case (x, e') acc'
      | SubE (e, t1, t2) ->
          let e', acc' = fold e acc in
          T.sub (e', t1, t2) acc'

    and fold_list es acc =
      match es with
      | [] -> ([], acc)
      | e :: es ->
          let e', acc' = fold e acc in
          let es', acc'' = fold_list es acc' in
          (e' :: es', acc'')

    and fold_option eo acc =
      match eo with
      | None -> (None, acc)
      | Some e ->
          let e', acc' = fold e acc in
          (Some e', acc')

    and fold_fieldlist es acc =
      match es with
      | [] -> ([], acc)
      | (x, e) :: es ->
          let e', acc' = fold e acc in
          let es', acc'' = fold_fieldlist es acc' in
          ((x, e') :: es', acc'')
  end
end
