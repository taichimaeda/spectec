open Util
open Ast
open Source

module Exp = struct
  module type TRAVERSAL = sig
    type acc
    val exp : exp' * typ * Source.region -> acc -> exp * acc
    val var : typ -> Source.region -> id -> acc -> exp' * acc
    val bool : typ -> Source.region -> bool -> acc -> exp' * acc
    val nat : typ -> Source.region -> nat -> acc -> exp' * acc
    val text : typ -> Source.region -> text -> acc -> exp' * acc
    val un : typ -> Source.region -> unop * exp -> acc -> exp' * acc
    val bin : typ -> Source.region -> binop * exp * exp -> acc -> exp' * acc
    val cmp : typ -> Source.region -> cmpop * exp * exp -> acc -> exp' * acc
    val idx : typ -> Source.region -> exp * exp -> acc -> exp' * acc
    val slice : typ -> Source.region -> exp * exp * exp -> acc -> exp' * acc
    val upd : typ -> Source.region -> exp * path * exp -> acc -> exp' * acc
    val ext : typ -> Source.region -> exp * path * exp -> acc -> exp' * acc
    val str : typ -> Source.region -> expfield list -> acc -> exp' * acc
    val dot : typ -> Source.region -> exp * atom -> acc -> exp' * acc
    val comp : typ -> Source.region -> exp * exp -> acc -> exp' * acc
    val len : typ -> Source.region -> exp -> acc -> exp' * acc
    val tup : typ -> Source.region -> exp list -> acc -> exp' * acc
    val mix : typ -> Source.region -> mixop * exp -> acc -> exp' * acc
    val call : typ -> Source.region -> id * exp -> acc -> exp' * acc
    val iter : typ -> Source.region -> exp * iterexp -> acc -> exp' * acc
    val opt : typ -> Source.region -> exp option -> acc -> exp' * acc
    val the : typ -> Source.region -> exp -> acc -> exp' * acc
    val list : typ -> Source.region -> exp list -> acc -> exp' * acc
    val cat : typ -> Source.region -> exp * exp -> acc -> exp' * acc
    val case : typ -> Source.region -> atom * exp -> acc -> exp' * acc
    val sub : typ -> Source.region -> exp * typ * typ -> acc -> exp' * acc
    val iter_ : typ -> Source.region -> iter -> acc -> iter * acc
    val iterexp : typ -> Source.region -> iterexp -> acc -> iterexp * acc
    val path : typ -> Source.region -> path -> acc -> path * acc
  end

  let identity (type a) = (module struct
    type acc = a
    let exp (e, t, at) acc = ({ it = e; note = t; at }, acc)
    let var _t _at x acc = (VarE x, acc)
    let bool _t _at b acc = (BoolE b, acc)
    let nat _t _at n acc = (NatE n, acc)
    let text _t _at t acc = (TextE t, acc)
    let un _t _at (op, e) acc = (UnE (op, e), acc)
    let bin _t _at (op, e1, e2) acc = (BinE (op, e1, e2), acc)
    let cmp _t _at (op, e1, e2) acc = (CmpE (op, e1, e2), acc)
    let idx _t _at (e1, e2) acc = (IdxE (e1, e2), acc)
    let slice _t _at (e1, e2, e3) acc = (SliceE (e1, e2, e3), acc)
    let upd _t _at (e1, p, e2) acc = (UpdE (e1, p, e2), acc)
    let ext _t _at (e1, p, e2) acc = (ExtE (e1, p, e2), acc)
    let str _t _at es acc = (StrE es, acc)
    let dot _t _at (e, x) acc = (DotE (e, x), acc)
    let comp _t _at (e1, e2) acc = (CompE (e1, e2), acc)
    let len _t _at e acc = (LenE e, acc)
    let tup _t _at es acc = (TupE es, acc)
    let mix _t _at (op, e) acc = (MixE (op, e), acc)
    let call _t _at (x, e) acc = (CallE (x, e), acc)
    let iter _t _at (e, ie) acc = (IterE (e, ie), acc)
    let opt _t _at eo acc = (OptE eo, acc)
    let the _t _at e acc = (TheE e, acc)
    let list _t _at es acc = (ListE es, acc)
    let cat _t _at (e1, e2) acc = (CatE (e1, e2), acc)
    let case _t _at (x, e) acc = (CaseE (x, e), acc)
    let sub _t _at (e, t1, t2) acc = (SubE (e, t1, t2), acc)
    let iter_ _t _at ie acc = (ie, acc)
    let iterexp _t _at (ie, vs) acc = ((ie, vs), acc)
    let path _t _at p acc = (p, acc)
  end : TRAVERSAL with type acc = a)

  module Run (T : TRAVERSAL) = struct
    let rec fold e acc =
      let e', acc' = fold' e.it e.note e.at acc in
      T.exp (e', e.note, e.at) acc'

    and fold' exp' t at acc =
      match exp' with
      | VarE x -> T.var t at x acc
      | BoolE b -> T.bool t at b acc
      | NatE n -> T.nat t at n acc
      | TextE tx -> T.text t at tx acc
      | UnE (op, e) ->
          let e', acc' = fold e acc in
          T.un t at (op, e') acc'
      | BinE (op, e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.bin t at (op, e1', e2') acc''
      | CmpE (op, e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.cmp t at (op, e1', e2') acc''
      | IdxE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.idx t at (e1', e2') acc''
      | SliceE (e1, e2, e3) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          let e3', acc''' = fold e3 acc'' in
          T.slice t at (e1', e2', e3') acc'''
      | UpdE (e1, p, e2) ->
          let e1', acc' = fold e1 acc in
          let p', acc'' = fold_path p acc' in
          let e2', acc''' = fold e2 acc'' in
          T.upd t at (e1', p', e2') acc'''
      | ExtE (e1, p, e2) ->
          let e1', acc' = fold e1 acc in
          let p', acc'' = fold_path p acc' in
          let e2', acc''' = fold e2 acc'' in
          T.ext t at (e1', p', e2') acc'''
      | StrE es ->
          let es', acc' = fold_fieldlist es acc in
          T.str t at es' acc'
      | DotE (e, x) ->
          let e', acc' = fold e acc in
          T.dot t at (e', x) acc'
      | CompE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.comp t at (e1', e2') acc''
      | LenE e ->
          let e', acc' = fold e acc in
          T.len t at e' acc'
      | TupE es ->
          let es', acc' = fold_list es acc in
          T.tup t at es' acc'
      | MixE (op, e) ->
          let e', acc' = fold e acc in
          T.mix t at (op, e') acc'
      | CallE (x, e) ->
          let e', acc' = fold e acc in
          T.call t at (x, e') acc'
      | IterE (e, ie) ->
          let e', acc' = fold e acc in
          let ie', acc'' = fold_iterexp ie acc' in
          T.iter t at (e', ie') acc''
      | OptE eo ->
          let eo', acc' = fold_option eo acc in
          T.opt t at eo' acc'
      | TheE e ->
          let e', acc' = fold e acc in
          T.the t at e' acc'
      | ListE es ->
          let es', acc' = fold_list es acc in
          T.list t at es' acc'
      | CatE (e1, e2) ->
          let e1', acc' = fold e1 acc in
          let e2', acc'' = fold e2 acc' in
          T.cat t at (e1', e2') acc''
      | CaseE (x, e) ->
          let e', acc' = fold e acc in
          T.case t at (x, e') acc'
      | SubE (e, t1, t2) ->
          let e', acc' = fold e acc in
          T.sub t at (e', t1, t2) acc'

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

    and fold_iterexp (ie, vs) acc =
      let ie', acc' = fold_iter ie acc in
      ((ie', vs), acc')

    and fold_iter ie acc =
      match ie with
      | Opt -> (Opt, acc)
      | List -> (List, acc)
      | List1 -> (List1, acc)
      | ListN e ->
          let e', acc' = fold e acc in
          (ListN e', acc')
    
    and fold_path p acc =
      let p', acc' = fold_path' p.it acc in
      {p with it = p'}, acc'

    and fold_path' p acc =
      match p with
      | RootP -> RootP, acc
      | IdxP (p, e) -> 
          let p', acc' = fold_path p acc in
          let e', acc'' = fold e acc' in
          IdxP (p', e'), acc''
      | SliceP (p, e1, e2) ->
          let p', acc' = fold_path p acc in
          let e1', acc'' = fold e1 acc' in
          let e2', acc''' = fold e2 acc'' in
          SliceP (p', e1', e2'), acc'''
      | DotP (p, a) ->
          let p', acc' = fold_path p acc in
          DotP (p', a), acc'
      end
end
