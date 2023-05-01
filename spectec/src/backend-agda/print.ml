let comment s = "{- " ^ s ^ " -}"
let keywords = [ "in"; "module" ]

let id (Ir.Id str) =
  let str = String.map (function '.' -> '-' | c -> c) str in
  if List.mem str keywords then str ^ "'" else str

let _list strs = "[ " ^ String.concat " , " strs ^ " ]"

let fold_left op default str =
  match str with
  | [] -> default
  | hd :: tl -> List.fold_left (fun acc x -> op acc x) hd tl

module Render = struct
  let const = function
    | Ir.SetC -> "Set"
    | BoolC -> "Bool"
    | NatC -> "Nat"
    | TextC -> "String"

  let rec exp = function
    | Ir.VarE i -> id i
    | Ir.ConstE c -> const c
    | ProdE es -> fold_left (Format.sprintf "(%s × %s)") "⊤" (List.map exp es)
    | TupleE es ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "record { }" (List.map exp es)
    | MaybeE e -> "Maybe " ^ exp e
    | ListE e -> "List " ^ exp e
    | Ir.YetE s -> "? " ^ comment s

  let cons_arg = function
    | None, e -> exp e
    | Some x, e -> "(" ^ id x ^ " : " ^ exp e ^ ")"

  let cons t (i, args) =
    id i ^ " : " ^ String.concat " -> " (List.map cons_arg args @ [ exp t ])

  let field (i, arg) = id i ^ " : " ^ exp arg

  let def = function
    | Ir.DefD (i, None, e) -> id i ^ " = " ^ exp e
    | Ir.DefD (i, Some t, e) ->
        id i ^ " : " ^ exp t ^ "\n" ^ id i ^ " = " ^ exp e
    | Ir.DataD (i, e, cs) ->
        "data " ^ id i ^ " : " ^ exp e ^ " where\n  "
        ^ (cs |> List.map (cons (Ir.VarE i)) |> String.concat "\n  ")
    | Ir.RecordD (i, e, fs) ->
        "record " ^ id i ^ " : " ^ exp e ^ " where\n  field\n    "
        ^ (List.map field fs |> String.concat "\n    ")
    | Ir.YetD s -> comment s

  let program defs = List.map def defs |> String.concat "\n\n"
end

let string_of_program prog =
  String.concat "\n"
    [
      "open import Agda.Builtin.Bool";
      "open import Agda.Builtin.List";
      "open import Agda.Builtin.Maybe";
      "open import Agda.Builtin.Nat";
      "open import Agda.Builtin.String";
      "open import Agda.Builtin.Unit";
      "";
      "data _×_ (A B : Set) : Set where";
      "  ⟨_,_⟩ : A → B → A × B";
      "";
      Render.program prog;
    ]
