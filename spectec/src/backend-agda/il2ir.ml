module Translate = struct
  open Util.Source
  open Il
  let _clause _c = failwith __LOC__

  let exp _e = failwith __LOC__

  let def d =
    match d.it with
    | Ast.SynD (id, deftyp) ->
      begin match deftyp.it with
        | Ast.AliasT ty ->
          Ir.DefD (id.it, exp ty)
        | NotationT (_mop, _ty) -> failwith __LOC__
        | VariantT _cases -> failwith __LOC__
        | StructT _fields -> failwith __LOC__

      end
    | DecD (_id, _typ1, _typ2, _clauses) -> failwith __LOC__
    | RecD _defs -> failwith __LOC__
    | _ -> failwith __LOC__

  let script = List.map def
end


let translate = Translate.script
