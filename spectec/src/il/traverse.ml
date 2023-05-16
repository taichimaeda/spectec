open Util
open Ast
open Source

let id_fold x acc = (x, acc)

let traverse_phrase fold p acc =
  let it, acc' = fold p.it acc in
  ({ p with it }, acc')

let traverse2 tx1 tx2 acc =
  let x1', acc' = tx1 acc in
  let x2', acc'' = tx2 acc' in
  ((x1', x2'), acc'')

let traverse3 tx1 tx2 tx3 acc =
  let x1', acc' = tx1 acc in
  let x2', acc'' = tx2 acc' in
  let x3', acc''' = tx3 acc'' in
  ((x1', x2', x3'), acc''')

let traverse4 tx1 tx2 tx3 tx4 acc =
  let x1', acc' = tx1 acc in
  let x2', acc'' = tx2 acc' in
  let x3', acc''' = tx3 acc'' in
  let x4', acc'''' = tx4 acc''' in
  ((x1', x2', x3', x4'), acc'''')

let rec traverse_list f ds acc =
  match ds with
  | [] -> ([], acc)
  | d :: ds ->
      let d', acc' = f d acc in
      let ds', acc'' = traverse_list f ds acc' in
      (d' :: ds', acc'')

let traverse_option f eo acc =
  match eo with
  | None -> (None, acc)
  | Some e ->
      let e', acc' = f e acc in
      (Some e', acc')

let rec traverse_fieldlist f es acc =
  match es with
  | [] -> ([], acc)
  | (x, e) :: es ->
      let e', acc' = f e acc in
      let es', acc'' = traverse_fieldlist f es acc' in
      ((x, e') :: es', acc'')

module Exp = struct
  module type TRAVERSAL = sig
    type acc

    val exp : exp -> acc -> exp * acc
    val iter : iter -> acc -> iter * acc
    val iterexp : iterexp -> acc -> iterexp * acc
    val path : path -> acc -> path * acc
  end

  let id (type a) =
    (module struct
      type acc = a

      let exp = id_fold
      let iter = id_fold
      let iterexp = id_fold
      let path = id_fold
    end : TRAVERSAL
      with type acc = a)

  module Run (T : TRAVERSAL) = struct
    let rec traverse_exp e acc =
      let e', acc' = traverse_phrase traverse_exp' e acc in
      T.exp e' acc'

    and traverse_exp' exp' acc =
      match exp' with
      | VarE x -> (VarE x, acc)
      | BoolE b -> (BoolE b, acc)
      | NatE n -> (NatE n, acc)
      | TextE tx -> (TextE tx, acc)
      | UnE (op, e) ->
          let e', acc' = traverse_exp e acc in
          (UnE (op, e'), acc')
      | BinE (op, e1, e2) ->
          let (e1', e2'), acc' =
            traverse2 (traverse_exp e1) (traverse_exp e2) acc
          in
          (BinE (op, e1', e2'), acc')
      | CmpE (op, e1, e2) ->
          let (e1', e2'), acc' =
            traverse2 (traverse_exp e1) (traverse_exp e2) acc
          in
          (CmpE (op, e1', e2'), acc')
      | IdxE (e1, e2) ->
          let (e1', e2'), acc' =
            traverse2 (traverse_exp e1) (traverse_exp e2) acc
          in
          (IdxE (e1', e2'), acc')
      | SliceE (e1, e2, e3) ->
          let (e1', e2', e3'), acc' =
            traverse3 (traverse_exp e1) (traverse_exp e2) (traverse_exp e3) acc
          in
          (SliceE (e1', e2', e3'), acc')
      | UpdE (e1, p, e2) ->
          let (e1', p', e2'), acc' =
            traverse3 (traverse_exp e1) (traverse_path p) (traverse_exp e2) acc
          in
          (UpdE (e1', p', e2'), acc')
      | ExtE (e1, p, e2) ->
          let (e1', p', e2'), acc' =
            traverse3 (traverse_exp e1) (traverse_path p) (traverse_exp e2) acc
          in
          (ExtE (e1', p', e2'), acc')
      | StrE es ->
          let es', acc' = traverse_fieldlist traverse_exp es acc in
          (StrE es', acc')
      | DotE (e, x) ->
          let e', acc' = traverse_exp e acc in
          (DotE (e', x), acc')
      | CompE (e1, e2) ->
          let (e1', e2'), acc' =
            traverse2 (traverse_exp e1) (traverse_exp e2) acc
          in
          (CompE (e1', e2'), acc')
      | LenE e ->
          let e', acc' = traverse_exp e acc in
          (LenE e', acc')
      | TupE es ->
          let es', acc' = traverse_list traverse_exp es acc in
          (TupE es', acc')
      | MixE (op, e) ->
          let e', acc' = traverse_exp e acc in
          (MixE (op, e'), acc')
      | CallE (x, e) ->
          let e', acc' = traverse_exp e acc in
          (CallE (x, e'), acc')
      | IterE (e, ie) ->
          let (e', ie'), acc' =
            traverse2 (traverse_exp e) (traverse_iterexp ie) acc
          in
          (IterE (e', ie'), acc')
      | OptE eo ->
          let eo', acc' = traverse_option traverse_exp eo acc in
          (OptE eo', acc')
      | TheE e ->
          let e', acc' = traverse_exp e acc in
          (TheE e', acc')
      | ListE es ->
          let es', acc' = traverse_list traverse_exp es acc in
          (ListE es', acc')
      | CatE (e1, e2) ->
          let (e1', e2'), acc' =
            traverse2 (traverse_exp e1) (traverse_exp e2) acc
          in
          (CatE (e1', e2'), acc')
      | CaseE (x, e) ->
          let e', acc' = traverse_exp e acc in
          (CaseE (x, e'), acc')
      | SubE (e, t1, t2) ->
          let e', acc' = traverse_exp e acc in
          (SubE (e', t1, t2), acc')

    and traverse_iterexp (ie, vs) acc =
      let ie', acc' = traverse_iter ie acc in
      ((ie', vs), acc')

    and traverse_iter ie acc =
      match ie with
      | Opt -> (Opt, acc)
      | List -> (List, acc)
      | List1 -> (List1, acc)
      | ListN e ->
          let e', acc' = traverse_exp e acc in
          (ListN e', acc')

    and traverse_path p acc =
      let p', acc' = traverse_path' p.it acc in
      ({ p with it = p' }, acc')

    and traverse_path' p acc =
      match p with
      | RootP -> (RootP, acc)
      | IdxP (p, e) ->
          let (p', e'), acc' =
            traverse2 (traverse_path p) (traverse_exp e) acc
          in
          (IdxP (p', e'), acc')
      | SliceP (p, e1, e2) ->
          let (p', e1', e2'), acc' =
            traverse3 (traverse_path p) (traverse_exp e1) (traverse_exp e2) acc
          in
          (SliceP (p', e1', e2'), acc')
      | DotP (p, a) ->
          let p', acc' = traverse_path p acc in
          (DotP (p', a), acc')
  end
end

module Def = struct
  module type TRAVERSAL = sig
    type acc

    include Exp.TRAVERSAL with type acc := acc

    val def : def -> acc -> def * acc
  end

  let id (type a) =
    let module EI = (val Exp.id : Exp.TRAVERSAL with type acc = a) in
    (module struct
      type acc = a

      include (EI : module type of EI with type acc := acc)

      let def = id_fold
    end : TRAVERSAL
      with type acc = a)

  module Run (T : TRAVERSAL) = struct
    include Exp.Run (T)

    let traverse_bind (x, t, iters) acc =
      let iters', acc' = traverse_list traverse_iter iters acc in
      ((x, t, iters'), acc')

    let traverse_binds bs acc =
      let bs', acc' = traverse_list traverse_bind bs acc in
      (bs', acc')

    let rec traverse_def d acc =
      let d', acc' = traverse_phrase traverse_def' d acc in
      T.def d' acc'

    and traverse_def' def' acc =
      match def' with
      | SynD (x, t) -> (SynD (x, t), acc)
      | RelD (x, op, t, rs) ->
          let rs', acc' = traverse_list traverse_rule rs acc in
          (RelD (x, op, t, rs'), acc')
      | DecD (x, t1, t2, cs) ->
          let cs', acc' = traverse_list traverse_clause cs acc in
          (DecD (x, t1, t2, cs'), acc')
      | RecD ds ->
          let ds', acc' = traverse_list traverse_def ds acc in
          (RecD ds', acc')
      | HintD hd -> (HintD hd, acc)

    and traverse_rule r acc = traverse_phrase traverse_rule' r acc

    and traverse_rule' r acc =
      match r with
      | RuleD (x, bs, op, e, ps) ->
          let (bs', e', ps'), acc' =
            traverse3 (traverse_binds bs) (traverse_exp e)
              (traverse_list traverse_premise ps)
              acc
          in
          (RuleD (x, bs', op, e', ps'), acc')

    and traverse_clause c acc = traverse_phrase traverse_clause' c acc

    and traverse_clause' c acc =
      match c with
      | DefD (bs, e1, e2, ps) ->
          let (bs', e1', e2', ps'), acc' =
            traverse4 (traverse_binds bs) (traverse_exp e1) (traverse_exp e2)
              (traverse_list traverse_premise ps)
              acc
          in
          (DefD (bs', e1', e2', ps'), acc')

    and traverse_premise p acc = traverse_phrase traverse_premise' p acc

    and traverse_premise' p acc =
      match p with
      | RulePr (x, op, e) ->
          let e', acc' = traverse_exp e acc in
          (RulePr (x, op, e'), acc')
      | IfPr e ->
          let e', acc' = traverse_exp e acc in
          (IfPr e', acc')
      | ElsePr -> (ElsePr, acc)
      | IterPr (p, ie) ->
          let (p', ie'), acc' =
            traverse2 (traverse_premise p) (traverse_iterexp ie) acc
          in
          (IterPr (p', ie'), acc')

    and traverse_hintdef hd acc = traverse_phrase traverse_hintdef' hd acc

    and traverse_hintdef' hs acc =
      match hs with
      | SynH (x, hs) -> (SynH (x, hs), acc)
      | RelH (x, hs) -> (RelH (x, hs), acc)
      | DecH (x, hs) -> (DecH (x, hs), acc)
  end
end
