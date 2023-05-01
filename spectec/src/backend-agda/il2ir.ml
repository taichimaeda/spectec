module Translate = struct
  open Util.Source
  open Il

  let str i = Ir.Id i
  let tyid i = str ("ty-" ^ i.it)
  let id i = str i.it
  let funid i = str ("$" ^ i.it)
  let atom = function Ast.Atom a -> str a | _ -> failwith __LOC__

  let rec typ t =
    match t.it with
    | Ast.VarT n -> Ir.VarE (tyid n)
    | BoolT -> ConstE BoolC
    | NatT -> ConstE NatC
    | TextT -> ConstE TextC
    | TupT ts -> ProdE (List.map typ ts)
    | IterT (t, Opt) -> MaybeE (typ t)
    | IterT (t, (List | List1 | ListN _)) -> ListE (typ t)

  let rec exp e =
    match e.it with
    | Ast.VarE n -> Ir.VarE (id n)
    | BoolE b -> ConstE (Bool b)
    | NatE n -> ConstE (Nat n)
    | TextE t -> ConstE (Text t)
    | UnE (_op, _e2) -> YetE (Print.string_of_exp e)
    | BinE (_op, _e1, _e2) -> YetE (Print.string_of_exp e)
    | CmpE (_op, _e1, _e2) -> YetE (Print.string_of_exp e)
    | IdxE (_e1, _e2) -> YetE (Print.string_of_exp e)
    | SliceE (_e1, _e2, _e3) -> YetE (Print.string_of_exp e)
    | UpdE (_e1, _p, _e2) -> YetE (Print.string_of_exp e)
    | ExtE (_e1, _p, _e2) -> YetE (Print.string_of_exp e)
    | StrE _efs -> YetE (Print.string_of_exp e)
    | DotE (_e1, _atom) -> YetE (Print.string_of_exp e)
    | CompE (_e1, _e2) -> YetE (Print.string_of_exp e)
    | LenE _e1 -> YetE (Print.string_of_exp e)
    | TupE es -> TupleE (List.map exp es)
    | MixE (_op, e1) ->
        exp e1 (* mixops arise only from notations, so they are identities *)
    | CallE (_id, _e1) -> YetE (Print.string_of_exp e)
    | IterE (_e1, _iter) -> YetE (Print.string_of_exp e)
    | OptE _eo -> YetE (Print.string_of_exp e)
    | TheE _e1 -> YetE (Print.string_of_exp e)
    | ListE _es -> YetE (Print.string_of_exp e)
    | CatE (_e1, _e2) -> YetE (Print.string_of_exp e)
    | CaseE (_atom, _e1) -> YetE (Print.string_of_exp e)
    | SubE (_e1, _t1, _t2) -> YetE (Print.string_of_exp e)

  let rec pat e =
    match e.it with
    | Ast.VarE n -> Ir.VarP (id n)
    | BoolE b -> ConstP (Bool b)
    | NatE n -> ConstP (Nat n)
    | TextE t -> ConstP (Text t)
    | UnE (_op, _e2) -> YetP (Print.string_of_exp e)
    | BinE (_op, _e1, _e2) -> YetP (Print.string_of_exp e)
    | CmpE (_op, _e1, _e2) -> YetP (Print.string_of_exp e)
    | IdxE (_e1, _e2) -> YetP (Print.string_of_exp e)
    | SliceE (_e1, _e2, _e3) -> YetP (Print.string_of_exp e)
    | UpdE (_e1, _p, _e2) -> YetP (Print.string_of_exp e)
    | ExtE (_e1, _p, _e2) -> YetP (Print.string_of_exp e)
    | StrE _efs -> YetP (Print.string_of_exp e)
    | DotE (_e1, _atom) -> YetP (Print.string_of_exp e)
    | CompE (_e1, _e2) -> YetP (Print.string_of_exp e)
    | LenE _e1 -> YetP (Print.string_of_exp e)
    | TupE es -> TupleP (List.map pat es)
    | MixE (_op, e1) ->
        pat e1 (* mixops arise only from notations, so they are identities *)
    | CallE (_id, _e1) -> YetP (Print.string_of_exp e)
    | IterE (_e1, _iter) -> YetP (Print.string_of_exp e)
    | OptE _eo -> YetP (Print.string_of_exp e)
    | TheE _e1 -> YetP (Print.string_of_exp e)
    | ListE _es -> YetP (Print.string_of_exp e)
    | CatE (_e1, _e2) -> YetP (Print.string_of_exp e)
    | CaseE (_atom, _e1) -> YetP (Print.string_of_exp e)
    | SubE (_e1, _t1, _t2) -> YetP (Print.string_of_exp e)

  let typefield (a, t, _hints) = (atom a, typ t)

  let deftyp x deftyp =
    match deftyp.it with
    | Ast.AliasT ty -> Ir.DefD (tyid x, Some (ConstE SetC), [ ([], typ ty) ])
    | NotationT (_op, ty) -> Ir.DefD (tyid x, None, [ ([], typ ty) ])
    | StructT tfs -> Ir.RecordD (tyid x, ConstE SetC, List.map typefield tfs)
    | VariantT tcs ->
        DataD
          ( tyid x,
            ConstE SetC,
            List.map
              (fun (a, t, _hints) -> (atom a, [], [ typ t ], Ir.VarE (tyid x)))
              tcs )

  let clause cls =
    let (Ast.DefD (_binds, p, e, premises)) = cls.it in
    match premises with [] -> ([ pat p ], exp e) | _ :: _ -> failwith __LOC__

  let rule rel r =
    let (Ast.RuleD (x, bs, _op, e, ps)) = r.it in
    let binds bs = List.map (fun (x, t, _iter) -> (id x, typ t)) bs in
    let premise p =
      match p.it with
      | Ast.RulePr (x, _op, e) -> Ir.ApplyE (VarE (tyid x), exp e)
      | _ -> Ir.YetE "PREM"
    in
    let premises ps = List.map premise ps in
    ( (if x.it <> "" then id x else str "-"),
      binds bs,
      premises ps,
      Ir.ApplyE (rel, exp e) )
  (* match premises with [] -> ([ pat p ], exp e) | _ :: _ -> failwith __LOC__ *)

  let rec def d =
    match d.it with
    | Ast.SynD (id, dt) -> [ deftyp id dt ]
    | Ast.RelD (x, _op, ty, rules) ->
        [
          Ir.DataD
            ( tyid x,
              ArrowE (typ ty, ConstE SetC),
              List.map (rule (VarE (tyid x))) rules );
        ]
    | DecD (i, tin, tout, clss) ->
        [
          (match clss with
          | [] ->
              Ir.DefD
                ( funid i,
                  Some (ArrowE (typ tin, typ tout)),
                  [ ([], Ir.YetE "TODO") ] )
          | _ :: _ ->
              Ir.DefD
                ( funid i,
                  Some (ArrowE (typ tin, typ tout)),
                  List.map clause clss ));
        ]
    | RecD defs -> List.concat_map def defs
    | HintD _ -> []

  let script = List.concat_map def
end

let translate = Translate.script
