let comment s = "{- " ^ s ^ " -}"
let keywords = [ "in"; "module" ]
let id (Ir.Id str) = if List.mem str keywords then str ^ "'" else str

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
    | Ir.CaseP (i, p) -> id i ^ " " ^ atomic_pat p
    | (VarP _ | ConstP _ | TupleP _ | YetP _) as p -> atomic_pat p

  and atomic_pat = function
    | Ir.VarP i -> id i
    | ConstP c -> const c
    | TupleP ps ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "_" (List.map pat ps)
    | YetP s -> "_ " ^ comment s
    | CaseP _ as p -> "(" ^ pat p ^ ")"

  let rec exp = function
    | Ir.ProdE es ->
        fold_left (Format.sprintf "(%s × %s)") "⊤" (List.map atomic_exp es)
    | MaybeE e -> "Maybe " ^ atomic_exp e
    | ListE e -> "List " ^ atomic_exp e
    | ArrowE (e1, e2) -> atomic_exp e1 ^ " → " ^ atomic_exp e2
    | ApplyE (e1, e2) -> atomic_exp e1 ^ " " ^ atomic_exp e2
    | DotE (e, t, f) -> id t ^ "." ^ id f ^ " " ^ atomic_exp e
    | ConsE (e1, e2) -> atomic_exp e1 ^ " ∷ " ^ atomic_exp e2
    | (VarE _ | ConstE _ | TupleE _ | NilE | YetE _) as e -> atomic_exp e

  and atomic_exp = function
    | Ir.VarE i -> id i
    | ConstE c -> const c
    | TupleE es ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "record { }" (List.map exp es)
    | NilE -> "[]"
    | YetE s -> "? " ^ comment s
    | (ProdE _ | MaybeE _ | ListE _ | ArrowE _ | ApplyE _ | DotE _ | ConsE _) as
      e ->
        "(" ^ exp e ^ ")"

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
      id i ^ " " ^ String.concat " " (List.map atomic_pat pats) ^ " = " ^ exp e
    in
    List.map clause cls |> String.concat "\n"

  let rec decl_def = function
    | Ir.DefD (i, t, _cls) -> id i ^ " : " ^ exp t
    | Ir.DataD (i, e, _cs) -> "data " ^ id i ^ " : " ^ exp e
    | Ir.RecordD (i, e, _fs) -> "record " ^ id i ^ " : " ^ exp e
    | Ir.MutualD defs -> String.concat "\n" (List.map decl_def defs)

  and def_def = function
    | Ir.DefD (i, _, cls) -> clauses i cls
    | Ir.DataD (i, _, cs) ->
        "data " ^ id i ^ " where\n  "
        ^ (cs |> List.map cons |> String.concat "\n  ")
    | Ir.RecordD (i, _, fs) ->
        "record " ^ id i ^ " where\n  field\n    "
        ^ (List.map field fs |> String.concat "\n    ")
    | Ir.MutualD defs -> String.concat "\n" (List.map def_def defs)

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
      "data _===_ {A : Set} : A -> A -> Set where";
      "data _=/=_ {A : Set} : A -> A -> Set where";
      "data _<<_ {A : Set} : A -> A -> Set where";
      "data _>_ {A : Set} : A -> A -> Set where";
      "data _<=_ {A : Set} : A -> A -> Set where";
      "data _>=_ {A : Set} : A -> A -> Set where";
      "";
      Render.program prog;
    ]
