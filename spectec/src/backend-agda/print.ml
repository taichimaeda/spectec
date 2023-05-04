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
    | Ir.CaseP (i, (_ :: _ as ps)) ->
        id i ^ " " ^ String.concat " " (List.map atomic_pat ps)
    | (VarP _ | ConstP _ | TupleP _ | YetP _ | CaseP (_, [])) as p ->
        atomic_pat p

  and atomic_pat = function
    | Ir.VarP i -> id i
    | ConstP c -> const c
    | TupleP ps ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "_" (List.map pat ps)
    | YetP s -> "_ " ^ comment s
    | CaseP (i, []) -> id i
    | CaseP (_, _ :: _) as p -> "(" ^ pat p ^ ")"

  let rec exp = function
    | Ir.ProdE es ->
        fold_left (Format.sprintf "(%s × %s)") "⊤" (List.map atomic_exp es)
    | ArrowE (e1, e2) -> atomic_exp e1 ^ " → " ^ atomic_exp e2
    | ApplyE (e1, e2) -> atomic_exp e1 ^ " " ^ atomic_exp e2
    | DotE (e, t, f) -> id t ^ "." ^ id f ^ " " ^ atomic_exp e
    | FunE (x, e) -> "λ " ^ id x ^ " -> " ^ atomic_exp e
    | StrE es ->
        "record { "
        ^ String.concat " ; " (List.map (fun (f, e) -> id f ^ " = " ^ exp e) es)
        ^ " }"
    | UpdE (e1, f, e2) ->
        "record " ^ atomic_exp e1 ^ " { " ^ id f ^ " = " ^ atomic_exp e2 ^ " }"
    | InfixE (op, e1, e2) -> atomic_exp e1 ^ " " ^ id op ^ " " ^ atomic_exp e2
    | CaseE (i, (_ :: _ as es)) ->
        id i ^ " " ^ String.concat " " (List.map atomic_exp es)
    | (VarE _ | ConstE _ | TupleE _ | CaseE (_, []) | YetE _) as e ->
        atomic_exp e

  and atomic_exp = function
    | Ir.VarE i -> id i
    | ConstE c -> const c
    | TupleE es ->
        fold_left
          (Format.sprintf "⟨ %s , %s ⟩")
          "(record { })" (List.map exp es)
    | CaseE (i, []) -> id i
    | YetE s -> "? " ^ comment s
    | ( ProdE _ | ArrowE _ | ApplyE _ | DotE _ | FunE _ | StrE _ | UpdE _
      | InfixE _
      | CaseE (_, _ :: _) ) as e ->
        "(" ^ exp e ^ ")"

  let cons (i, bs, prems, t) =
    let prems' = List.map exp prems and t' = exp t in
    id i ^ " :\n    "
    ^ (if bs <> [] then
         String.concat " "
           (List.map (fun (i, ty) -> "(" ^ id i ^ " : " ^ exp ty ^ ")") bs)
         ^ " ->\n    "
       else "")
    ^ (if prems <> [] then String.concat " ->\n    " prems' ^ " ->\n    "
       else "")
    ^ String.make
        (List.fold_left max 0
           (List.map (fun s -> List.length (Util.Utf8.decode s)) (t' :: prems')))
        '-'
    ^ "\n    " ^ t'

  let field (i, arg) = id i ^ " : " ^ exp arg

  let clauses i cls =
    let clause (pats, e) =
      id i ^ " " ^ String.concat " " (List.map atomic_pat pats) ^ " = " ^ exp e
    in
    List.map clause cls |> String.concat "\n"

  let rec decl_def = function
    | Ir.DefD (i, t, _cls) -> id i ^ " : " ^ exp t
    | Ir.DataD (i, e, _cs) -> "data " ^ id i ^ " : " ^ exp e
    | Ir.RecordD (i, e, _fs) ->
        "record " ^ id i ^ " : " ^ exp e ^ "\n" ^ "_++" ^ id i ^ "_ : " ^ id i
        ^ " -> " ^ id i ^ " -> " ^ id i
    | Ir.MutualD defs -> String.concat "\n" (List.map decl_def defs)

  and def_def = function
    | Ir.DefD (i, _, cls) -> clauses i cls
    | Ir.DataD (i, _, cs) ->
        "data " ^ id i ^ " where\n  "
        ^ (cs |> List.map cons |> String.concat "\n  ")
    | Ir.RecordD (i, _, fs) ->
        "record " ^ id i ^ " where\n  field\n    "
        ^ (List.map field fs |> String.concat "\n    ")
        ^ "\n" ^ "_++" ^ id i ^ "_ = ?"
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
      "_++_ : {A : Set} -> List A -> List A -> List A";
      "[] ++ ys = ys";
      "(x ∷ xs) ++ ys = x ∷ (xs ++ ys)";
      "maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B";
      "maybeMap f (just x) = just (f x)";
      "maybeMap _ nothing = nothing";
      "maybeTrue : {A : Set} -> (A -> Set) -> Maybe A -> Set";
      "maybeTrue _ _ = {!   !}";
      "maybeThe : {A : Set} -> Maybe A -> A";
      "maybeThe _ = {!   !}";
      "map : {A B : Set} -> (A -> B) -> List A -> List B";
      "map f [] = []";
      "map f (x ∷ xs) = f x ∷ map f xs";
      "forAll : {A : Set} -> (A -> Set) -> List A -> Set";
      "forAll _ _ = {!   !}";
      "forAll2 : {A B : Set} -> (A -> B -> Set) -> List A -> List B -> Set";
      "forAll2 _ _ = {!   !}";
      "length : {A : Set} -> List A -> Nat";
      "length [] = 0";
      "length (x ∷ xs) = suc (length xs)";
      "idx : {A : Set} -> List A -> Nat -> A";
      "idx _ _ = {!   !}";
      "upd : {A : Set} -> List A -> Nat -> A -> List A";
      "upd _ _ _ = {!   !}";
      "";
      Render.program prog;
    ]
