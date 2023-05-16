open Util
open Ast
open Source

let rec fold_list f ds acc =
  match ds with
  | [] -> ([], acc)
  | d :: ds ->
      let d', acc' = f d acc in
      let ds', acc'' = fold_list f ds acc' in
      (d' :: ds', acc'')

let fold_option f eo acc =
  match eo with
  | None -> (None, acc)
  | Some e ->
      let e', acc' = f e acc in
      (Some e', acc')

let rec fold_fieldlist f es acc =
  match es with
  | [] -> ([], acc)
  | (x, e) :: es ->
      let e', acc' = f e acc in
      let es', acc'' = fold_fieldlist f es acc' in
      ((x, e') :: es', acc'')

module Exp = struct
  module type TRAVERSAL = sig
    type acc

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

  let identity (type a) =
    (module struct
      type acc = a

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
    end : TRAVERSAL
      with type acc = a)

  module Run (T : TRAVERSAL) = struct
    let rec fold_exp e acc =
      let e', acc' = fold_exp' e.it e.note e.at acc in
      ({ e with it = e' }, acc')

    and fold_exp' exp' t at acc =
      match exp' with
      | VarE x -> T.var t at x acc
      | BoolE b -> T.bool t at b acc
      | NatE n -> T.nat t at n acc
      | TextE tx -> T.text t at tx acc
      | UnE (op, e) ->
          let e', acc' = fold_exp e acc in
          T.un t at (op, e') acc'
      | BinE (op, e1, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          T.bin t at (op, e1', e2') acc''
      | CmpE (op, e1, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          T.cmp t at (op, e1', e2') acc''
      | IdxE (e1, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          T.idx t at (e1', e2') acc''
      | SliceE (e1, e2, e3) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          let e3', acc''' = fold_exp e3 acc'' in
          T.slice t at (e1', e2', e3') acc'''
      | UpdE (e1, p, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let p', acc'' = fold_path p acc' in
          let e2', acc''' = fold_exp e2 acc'' in
          T.upd t at (e1', p', e2') acc'''
      | ExtE (e1, p, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let p', acc'' = fold_path p acc' in
          let e2', acc''' = fold_exp e2 acc'' in
          T.ext t at (e1', p', e2') acc'''
      | StrE es ->
          let es', acc' = fold_fieldlist fold_exp es acc in
          T.str t at es' acc'
      | DotE (e, x) ->
          let e', acc' = fold_exp e acc in
          T.dot t at (e', x) acc'
      | CompE (e1, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          T.comp t at (e1', e2') acc''
      | LenE e ->
          let e', acc' = fold_exp e acc in
          T.len t at e' acc'
      | TupE es ->
          let es', acc' = fold_list fold_exp es acc in
          T.tup t at es' acc'
      | MixE (op, e) ->
          let e', acc' = fold_exp e acc in
          T.mix t at (op, e') acc'
      | CallE (x, e) ->
          let e', acc' = fold_exp e acc in
          T.call t at (x, e') acc'
      | IterE (e, ie) ->
          let e', acc' = fold_exp e acc in
          let ie', acc'' = fold_iterexp ie acc' in
          T.iter t at (e', ie') acc''
      | OptE eo ->
          let eo', acc' = fold_option fold_exp eo acc in
          T.opt t at eo' acc'
      | TheE e ->
          let e', acc' = fold_exp e acc in
          T.the t at e' acc'
      | ListE es ->
          let es', acc' = fold_list fold_exp es acc in
          T.list t at es' acc'
      | CatE (e1, e2) ->
          let e1', acc' = fold_exp e1 acc in
          let e2', acc'' = fold_exp e2 acc' in
          T.cat t at (e1', e2') acc''
      | CaseE (x, e) ->
          let e', acc' = fold_exp e acc in
          T.case t at (x, e') acc'
      | SubE (e, t1, t2) ->
          let e', acc' = fold_exp e acc in
          T.sub t at (e', t1, t2) acc'

    and fold_iterexp (ie, vs) acc =
      let ie', acc' = fold_iter ie acc in
      ((ie', vs), acc')

    and fold_iter ie acc =
      match ie with
      | Opt -> (Opt, acc)
      | List -> (List, acc)
      | List1 -> (List1, acc)
      | ListN e ->
          let e', acc' = fold_exp e acc in
          (ListN e', acc')

    and fold_path p acc =
      let p', acc' = fold_path' p.it acc in
      ({ p with it = p' }, acc')

    and fold_path' p acc =
      match p with
      | RootP -> (RootP, acc)
      | IdxP (p, e) ->
          let p', acc' = fold_path p acc in
          let e', acc'' = fold_exp e acc' in
          (IdxP (p', e'), acc'')
      | SliceP (p, e1, e2) ->
          let p', acc' = fold_path p acc in
          let e1', acc'' = fold_exp e1 acc' in
          let e2', acc''' = fold_exp e2 acc'' in
          (SliceP (p', e1', e2'), acc''')
      | DotP (p, a) ->
          let p', acc' = fold_path p acc in
          (DotP (p', a), acc')
  end
end

module Def = struct
  module type TRAVERSAL = sig
    type acc

    include Exp.TRAVERSAL with type acc := acc

    val synD : Source.region -> id * deftyp -> acc -> def' * acc

    val relD :
      Source.region -> id * mixop * typ * rule list -> acc -> def' * acc

    val decD :
      Source.region -> id * typ * typ * clause list -> acc -> def' * acc

    val recD : Source.region -> def list -> acc -> def' * acc
    val hintD : Source.region -> hintdef -> acc -> def' * acc

    val ruleD :
      Source.region ->
      id * binds * mixop * exp * premise list ->
      acc ->
      rule' * acc

    val defD :
      Source.region -> binds * exp * exp * premise list -> acc -> clause' * acc

    val rulePr : Source.region -> id * mixop * exp -> acc -> premise' * acc
    val ifPr : Source.region -> exp -> acc -> premise' * acc
    val elsePr : Source.region -> acc -> premise' * acc
    val iterPr : Source.region -> premise * iterexp -> acc -> premise' * acc
    val synH : Source.region -> id * hint list -> acc -> hintdef' * acc
    val relH : Source.region -> id * hint list -> acc -> hintdef' * acc
    val decH : Source.region -> id * hint list -> acc -> hintdef' * acc
  end

  let identity (type a) =
    let module EI = (val Exp.identity : Exp.TRAVERSAL with type acc = a) in
    (module struct
      type acc = a

      include (EI : module type of EI with type acc := acc)

      let synD _at (x, t) acc = (SynD (x, t), acc)
      let relD _at (x, op, t, rs) acc = (RelD (x, op, t, rs), acc)
      let decD _at (x, t1, t2, cs) acc = (DecD (x, t1, t2, cs), acc)
      let recD _at ds acc = (RecD ds, acc)
      let hintD _at hd acc = (HintD hd, acc)
      let ruleD _at (x, bs, op, e, ps) acc = (RuleD (x, bs, op, e, ps), acc)
      let defD _at (bs, e1, e2, ps) acc = (DefD (bs, e1, e2, ps), acc)
      let rulePr _at (x, op, e) acc = (RulePr (x, op, e), acc)
      let ifPr _at e acc = (IfPr e, acc)
      let elsePr _at acc = (ElsePr, acc)
      let iterPr _at (p, ie) acc = (IterPr (p, ie), acc)
      let synH _at (x, hs) acc = (SynH (x, hs), acc)
      let relH _at (x, hs) acc = (RelH (x, hs), acc)
      let decH _at (x, hs) acc = (DecH (x, hs), acc)
    end : TRAVERSAL
      with type acc = a)

  module Run (T : TRAVERSAL) = struct
    include Exp.Run (T)

    let fold_bind (x, t, iters) acc =
      let iters', acc' = fold_list fold_iter iters acc in
      ((x, t, iters'), acc')

    let fold_binds bs acc =
      let bs', acc' = fold_list fold_bind bs acc in
      (bs', acc')

    let rec fold_def d acc =
      let d', acc' = fold_def' d.it d.at acc in
      ({ d with it = d' }, acc')

    and fold_def' def' at acc =
      match def' with
      | SynD (x, t) -> T.synD at (x, t) acc
      | RelD (x, op, t, rs) ->
          let rs', acc' = fold_list fold_rule rs acc in
          T.relD at (x, op, t, rs') acc'
      | DecD (x, t1, t2, cs) ->
          let cs', acc' = fold_list fold_clause cs acc in
          T.decD at (x, t1, t2, cs') acc'
      | RecD ds ->
          let ds', acc' = fold_list fold_def ds acc in
          T.recD at ds' acc'
      | HintD hd -> T.hintD at hd acc

    and fold_rule r acc =
      let r', acc' = fold_rule' r.it r.at acc in
      ({ r with it = r' }, acc')

    and fold_rule' r at acc =
      match r with
      | RuleD (x, bs, op, e, ps) ->
          let bs', acc' = fold_binds bs acc in
          let e', acc'' = fold_exp e acc' in
          let ps', acc''' = fold_list fold_premise ps acc'' in
          T.ruleD at (x, bs', op, e', ps') acc'''

    and fold_clause c acc =
      let c', acc' = fold_clause' c.it c.at acc in
      ({ c with it = c' }, acc')

    and fold_clause' c at acc =
      match c with
      | DefD (bs, e1, e2, ps) ->
          let bs', acc' = fold_binds bs acc in
          let e1', acc'' = fold_exp e1 acc' in
          let e2', acc''' = fold_exp e2 acc'' in
          let ps', acc'''' = fold_list fold_premise ps acc''' in
          T.defD at (bs', e1', e2', ps') acc''''

    and fold_premise p acc =
      let p', acc' = fold_premise' p.it p.at acc in
      ({ p with it = p' }, acc')

    and fold_premise' p at acc =
      match p with
      | RulePr (x, op, e) ->
          let e', acc' = fold_exp e acc in
          T.rulePr at (x, op, e') acc'
      | IfPr e ->
        let e', acc' = fold_exp e acc in
        T.ifPr at e' acc'
      | ElsePr -> T.elsePr at acc
      | IterPr (p, ie) ->
          let p', acc' = fold_premise p acc in
          let ie', acc'' = fold_iterexp ie acc' in
          T.iterPr at (p', ie') acc''

    and fold_hintdef hd acc =
      let hd', acc' = fold_hintdef' hd.it hd.at acc in
      ({ hd with it = hd' }, acc')

    and fold_hintdef' hs at acc =
      match hs with
      | SynH (x, hs) -> T.synH at (x, hs) acc
      | RelH (x, hs) -> T.relH at (x, hs) acc
      | DecH (x, hs) -> T.decH at (x, hs) acc
  end
end
