module Translate = struct
  open Util.Source
  open Il

  let id i = i.it

  let atom a = Print.string_of_atom a

  let typ t = Ir.YetE (Print.string_of_typ t)

  let typecase (a, t, _hints) =
    (atom a, [(None, typ t)])

  let deftyp x deftyp =
    match deftyp.it with
    | Ast.AliasT ty -> Ir.DefD (id x, typ ty)
    | NotationT _ -> YetD ("notation " ^ id x ^ " = " ^ Print.string_of_deftyp deftyp)
    | StructT _ -> YetD ("struct " ^ id x ^ " = " ^ Print.string_of_deftyp deftyp)
    | VariantT tcs ->
        DataD (id x, SetE, List.map typecase tcs) 

  let def d =
    match d.it with
    | Ast.SynD (id, dt) -> deftyp id dt
    | (Ast.RelD _ | DecD _ | RecD _ | HintD _) -> YetD (Print.string_of_def d)

  let script = List.map def
end


let translate = Translate.script
