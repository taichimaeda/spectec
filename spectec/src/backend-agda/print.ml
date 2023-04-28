let comment s = "{- " ^ s ^ " -}"

module Render = struct
  let exp = function
  | Ir.VarE id -> id
  | Ir.SetE -> "Set"
  | Ir.YetE s -> "? " ^ comment s

  let cons_arg = function
  | (None, e) -> exp e
  | (Some x, e) -> "(" ^ x ^ " : " ^ exp e ^ ")"

  let cons t (id, args) = id ^ " : " ^ (String.concat " -> " ((List.map cons_arg args) @ [exp t]))
  let def =
    function
    | Ir.DefD (id, e) -> id ^ " = " ^ exp e
    | Ir.DataD (id, e, cs) ->
        "data " ^ id ^ " : " ^ exp e ^ " where\n  " ^ (cs |> List.map (cons (Ir.VarE id)) |> String.concat "\n  ")
    | Ir.YetD s -> comment s

  let program defs =
    List.map def defs |> String.concat "\n\n"
end

let string_of_program = Render.program
