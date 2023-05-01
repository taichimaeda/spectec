module Translate = struct
  open Util.Source
  open Il

  let str i = Ir.Id i
  let id i = str i.it
  let atom = function Ast.Atom a -> str a | _ -> failwith __LOC__

  let rec typ t =
    match t.it with
    | Ast.VarT n -> Ir.VarE (id n)
    | BoolT -> BoolE
    | NatT -> NatE
    | TextT -> TextE
    | TupT ts -> ProdE (List.map typ ts)
    | IterT (t, Opt) -> MaybeE (typ t)
    | IterT (t, (List | List1 | ListN _)) -> ListE (typ t)

  let typecase (a, t, _hints) = (atom a, [ (None, typ t) ])
  let typefield (a, t, _hints) = (atom a, typ t)

  let deftyp x deftyp =
    match deftyp.it with
    | Ast.AliasT ty -> Ir.DefD (id x, Some SetE, typ ty)
    | NotationT (_op, ty) -> Ir.DefD (id x, None, typ ty)
    | StructT tfs -> Ir.RecordD (id x, SetE, List.map typefield tfs)
    | VariantT tcs -> DataD (id x, SetE, List.map typecase tcs)

  let rec def d =
    match d.it with
    | Ast.SynD (id, dt) -> [ deftyp id dt ]
    | Ast.RelD _ -> [ YetD (Print.string_of_def d) ]
    | DecD _ -> [ YetD (Print.string_of_def d) ]
    | RecD defs -> List.concat_map def defs
    | HintD _ -> []

  let script = List.concat_map def
end

let translate = Translate.script
