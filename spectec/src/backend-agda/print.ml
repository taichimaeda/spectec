let comment s = "{- " ^ s ^ " -}"
let keywords = [ "in"; "module" ]

let id (Ir.Id str) =
  let str =
    String.map (function '_' | '.' -> '-' | ';' -> ',' | c -> c) str
  in
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
    | Bool b -> string_of_bool b
    | Nat n -> string_of_int n
    | Text s -> s

  let rec pat = function
    | Ir.VarP i -> id i
    | Ir.ConstP c -> const c
    | Ir.TupleP ps ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "_" (List.map pat ps)
    | YetP s -> "_ " ^ comment s

  let rec exp = function
    | Ir.VarE i -> id i
    | Ir.ConstE c -> const c
    | ProdE es -> fold_left (Format.sprintf "(%s × %s)") "⊤" (List.map exp es)
    | TupleE es ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "record { }" (List.map exp es)
    | MaybeE e -> "Maybe " ^ exp e
    | ListE e -> "List " ^ exp e
    | ArrowE (e1, e2) -> exp e1 ^ " → " ^ exp e2
    | ApplyE (e1, e2) -> exp e1 ^ " " ^ exp e2
    | Ir.YetE s -> "? " ^ comment s

  let cons (i, bs, prems, t) =
    id i ^ " :\n    "
    ^ (if bs <> [] then
         String.concat " "
           (List.map (fun (i, ty) -> "(" ^ id i ^ " : " ^ exp ty ^ ")") bs)
         ^ " ->\n    "
       else "")
    ^ (if prems <> [] then
         String.concat " ->\n    " (List.map exp prems) ^ " ->\n    "
       else "")
    ^
    let conc = exp t in
    String.make (String.length conc) '-' ^ "\n    " ^ conc

  let field (i, arg) = id i ^ " : " ^ exp arg

  let clauses i cls =
    let clause (pats, e) =
      id i ^ " " ^ String.concat " " (List.map pat pats) ^ " = " ^ exp e
    in
    List.map clause cls |> String.concat "\n"

  let rec decl_def = function
    | Ir.DefD (_i, None, _cls) -> ""
    | Ir.DefD (i, Some t, _cls) -> id i ^ " : " ^ exp t
    | Ir.DataD (i, e, _cs) -> "data " ^ id i ^ " : " ^ exp e
    | Ir.RecordD (i, e, _fs) -> "record " ^ id i ^ " : " ^ exp e
    | Ir.MutualD defs -> String.concat "\n" (List.map decl_def defs)
    | Ir.YetD _s -> ""

  and def_def = function
    | Ir.DefD (i, _, cls) -> clauses i cls
    | Ir.DataD (i, _, cs) ->
        "data " ^ id i ^ " where\n  "
        ^ (cs |> List.map cons |> String.concat "\n  ")
    | Ir.RecordD (i, _, fs) ->
        "record " ^ id i ^ " where\n  field\n    "
        ^ (List.map field fs |> String.concat "\n    ")
    | Ir.MutualD defs -> String.concat "\n" (List.map def_def defs)
    | Ir.YetD s -> comment s

  let def d = decl_def d ^ "\n" ^ def_def d
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
