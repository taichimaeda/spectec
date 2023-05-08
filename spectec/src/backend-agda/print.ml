let comment s = "{- " ^ s ^ " -}"
let keywords = [ "in"; "module" ]
let id (Agda.Id str) = if List.mem str keywords then str ^ "'" else str

let fold_left op default str =
  match str with
  | [] -> default
  | hd :: tl -> List.fold_left (fun acc x -> op acc x) hd tl

module Render = struct
  let const = function
    | Agda.SetC -> "Set"
    | BoolC -> "Bool"
    | NatC -> "ℕ"
    | TextC -> "String"
    | Bool b -> string_of_bool b
    | Nat n -> string_of_int n
    | Text s -> s

  let rec pat = function
    | Agda.CaseP (i, (_ :: _ as ps)) ->
        id i ^ " " ^ String.concat " " (List.map atomic_pat ps)
    | (VarP _ | ConstP _ | TupleP _ | YetP _ | CaseP (_, [])) as p ->
        atomic_pat p

  and atomic_pat = function
    | Agda.VarP i -> id i
    | ConstP c -> const c
    | TupleP ps ->
        fold_left (Format.sprintf "⟨ %s , %s ⟩") "_" (List.map pat ps)
    | YetP s -> "_ " ^ comment s
    | CaseP (i, []) -> id i
    | CaseP (_, _ :: _) as p -> "(" ^ pat p ^ ")"

  let mixfix op strs =
    let op_parts = String.split_on_char '_' op in
    match op_parts with
    | part :: parts ->
        part
        ^ String.concat " "
            (List.map2
               (fun str part -> if part = "" then str else str ^ " " ^ part)
               strs parts)
    | [] -> failwith "mixfix"

  let rec exp = function
    | Agda.ProdE es ->
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
    | MixfixE (op, es) -> mixfix (id op) (List.map atomic_exp es)
    | CaseE (i, (_ :: _ as es)) ->
        id i ^ " " ^ String.concat " " (List.map atomic_exp es)
    | (VarE _ | ConstE _ | TupleE _ | CaseE (_, []) | YetE _) as e ->
        atomic_exp e

  and atomic_exp = function
    | Agda.VarE i -> id i
    | ConstE c -> const c
    | TupleE es ->
        fold_left
          (Format.sprintf "⟨ %s , %s ⟩")
          "(record { })" (List.map exp es)
    | CaseE (i, []) -> id i
    | YetE s -> "{!   !} " ^ comment s
    | ( ProdE _ | ArrowE _ | ApplyE _ | DotE _ | FunE _ | StrE _ | UpdE _
      | MixfixE _
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
    | Agda.DefD (i, t, _cls) -> id i ^ " : " ^ exp t
    | Agda.DataD (i, e, _cs) -> "data " ^ id i ^ " : " ^ exp e
    | Agda.RecordD (i, e, _fs) ->
        "record " ^ id i ^ " : " ^ exp e ^ "\n" ^ "_++" ^ id i ^ "_ : " ^ id i
        ^ " -> " ^ id i ^ " -> " ^ id i
    | Agda.MutualD defs -> String.concat "\n" (List.map decl_def defs)

  and def_def = function
    | Agda.DefD (i, _, cls) -> clauses i cls
    | Agda.DataD (i, _, cs) ->
        "data " ^ id i ^ " where\n  "
        ^ (cs |> List.map cons |> String.concat "\n  ")
    | Agda.RecordD (i, _, fs) ->
        "record " ^ id i ^ " where\n  field\n    "
        ^ (List.map field fs |> String.concat "\n    ")
        ^ "\n" ^ "_++" ^ id i ^ "_ = {!   !}"
    | Agda.MutualD defs -> String.concat "\n" (List.map def_def defs)

  let def d = decl_def d ^ "\n" ^ def_def d
  let program defs = List.map def defs |> String.concat "\n\n"
end

let string_of_program prog =
  String.concat "\n"
    [
      "open import Data.Bool using (Bool; true; false)";
      "open import Data.Product using (_×_) renaming (_,_ to  ⟨_,_⟩)";
      "open import Data.List using (List; map; _∷_; []; length; _++_; lookup; \
       _[_]∷=_)";
      "open import Data.List.Relation.Unary.All using (All)";
      "open import Data.List.Relation.Binary.Pointwise using (Pointwise)";
      "open import Data.Maybe using (Maybe; just; nothing) renaming (map to \
       maybeMap)";
      "open import Data.String using (String)";
      "open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_; _≥_; \
       _>_)";
      "open import Data.Unit using (⊤; tt)";
      "open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)";
      "";
      "";
      Render.program prog;
      "";
    ]
