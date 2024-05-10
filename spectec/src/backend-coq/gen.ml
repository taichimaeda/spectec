open Il.Ast
open Util
open Source
open Case

let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"
let square_parens s = "[" ^ s ^ "]"
let error at msg = Error.error at "Coq Generation" msg

(* Function prefix (To avoid same name clash on types) *)
let func_prefix = "fun_"

(* variable prefix (To avoid same name clash on types) *)
let var_prefix = "v_"

module IdSet = Set.Make(String)

let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"; "nat"] |> IdSet.of_list

let rec list_split (f : 'a -> bool) (l : 'a list) = match l with
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

let gen_id' (s : text) = match s with
 | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s

let gen_id (s : id) = gen_id' s.it

let gen_atom_total (a : atom) = 
  match a.it with
    | Atom id -> Some (gen_id' id)
    | _ -> None

let gen_atom (a : atom) = 
  match gen_atom_total a with
    | Some id -> id
    | None -> ""

let gen_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> gen_id' a
    | mixop -> String.concat "" (List.map (
        fun atoms -> String.concat "" (List.filter_map gen_atom_total atoms)) mixop
      )

let gen_iter_typ (it : iter) =
  match it with
    | Opt -> "list" 
    | (List | List1 | ListN _) -> "list"

let is_dot (p : path) = match p.it with
  | DotP _ -> true
  | _ -> false

let rec _print_paths (paths : path list) = match paths with
  | [] -> ()
  | {it = DotP _; _} :: ps -> print_endline ("DotP"); _print_paths ps
  | {it = RootP; _} :: ps -> print_endline ("RootP"); _print_paths ps
  | {it = SliceP _; _} :: ps -> print_endline ("SliceP"); _print_paths ps
  | {it = IdxP _; _} :: ps -> print_endline ("IdxP"); _print_paths ps

let rec get_actual_case_name (env : env) (id : id) =
  let (n_id, num_args, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> let actual_id, final_args = get_actual_case_name env n_id in
    (actual_id, num_args + final_args)
    | Inductive -> (n_id, num_args)
    | _ -> error id.at "Should be a Variant type or type alias"
  )

let rec get_struct_type (env : env) (id : id) =
  let (n_id, _, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> get_struct_type env n_id
    | Inductive -> Inductive
    | Record -> Record
    | Terminal -> Terminal
  )

let gen_case_name (env : env) (t : typ) =
  match t.it with
    | VarT (id, _) -> get_actual_case_name env id
    | _ -> error t.at "Should not happen"

let gen_typ_name (t : typ) =
  match t.it with
    | VarT (id, _) -> gen_id id
    | _ -> error t.at "Should not happen"

let get_typ_name (t : typ) = 
  match t.it with
    | VarT (id, _) -> Some id
    | _ -> None

let gen_list_update_func (func_name: text) (list : text) (idx : text) (func : text) = 
  parens (func_name ^ " " ^ parens list ^ " " ^ parens idx ^ " " ^ parens func)

let gen_list_slice_update (list : text) (idx : text) (idx2 : text) (update_list : text) = 
  parens ("list_slice_update " ^ parens list ^ " " ^ parens idx ^ " " ^ parens idx2 ^ " " ^ parens update_list)


let gen_binop (b : binop) =
  match b with
    | AndOp -> " /\\ "
    | OrOp -> " \\/ "
    | AddOp _ -> " + "
    | SubOp _ -> " - "
    | ImplOp -> " -> "
    | MulOp _ -> " * "
    | DivOp _ -> " / "
    | ExpOp _ -> " ^ "
    | EquivOp -> " <-> "
let is_addop (b : binop) = 
  match b with
    | AddOp _ -> true
    | _ -> false
let gen_unop (u : unop) =
  match u with
    | NotOp -> "~"
    | PlusOp _ -> ""
    | MinusOp _ -> "0 - "
    | PlusMinusOp _ -> "0 - "
    | MinusPlusOp _ -> "0 - "

let gen_cmpop (c : cmpop) =
  match c with
    | EqOp -> " = "
    | NeOp -> " <> "
    | LtOp _ -> " < "
    | GtOp _ -> " > "
    | LeOp _ -> " <= "
    | GeOp _ -> " >= "

let get_num_from_exp (e : exp) =
  match e.it with
    | NatE nat -> nat
    | _ -> Z.zero

let rec gen_exp (env : env) (is_match : bool) (e : exp) =
  match e.it with
    | VarE id -> var_prefix ^ gen_id id
    | BoolE true -> "true"
    | BoolE false -> "false"
    | NatE nat -> Z.to_string nat
    | TextE text -> "\"" ^ String.escaped text ^ "\""
    | UnE (op, exp) ->  parens (gen_unop op ^ (gen_exp env is_match exp))
    | BinE (binop, exp1, exp2) -> let num2 = get_num_from_exp exp2 in 
      if is_match && is_addop binop && num2 <> Z.zero
      then (gen_succ env (Z.to_int num2) exp1)
      else parens (gen_exp env is_match exp1 ^ gen_binop binop ^ gen_exp env is_match exp2)
    | CmpE (cmpop, exp1, exp2) -> parens (gen_exp env is_match exp1 ^ gen_cmpop cmpop ^ gen_exp env is_match exp2)
    | SliceE (exp1, exp2, exp3) -> parens ("list_slice " ^ parens (gen_exp env is_match exp1) ^ " " ^ parens (gen_exp env is_match exp2) ^ " " ^ parens (gen_exp env is_match exp3)) (* TODO *)
    | UpdE (exp1, path, exp2) -> gen_path_start env path is_match exp1 exp2 "list_update"
    | ExtE (exp1, path, exp2) -> gen_path_start env path is_match exp1 exp2 "list_extend"
    | StrE expfields -> "{| " ^ String.concat "; " (List.map (fun (a, exp) -> 
      gen_typ_name e.note ^ "__" ^ gen_atom a ^ " := " ^ gen_exp env false exp) expfields) 
      ^ " |}"
    | DotE (exp, atom) -> parens (gen_typ_name exp.note ^ "__" ^ gen_atom atom ^  " " ^ gen_exp env is_match exp)
    | CompE (exp, exp2) -> parens (gen_exp env false exp ^ " ++ " ^ gen_exp env false exp2)
    | TupE [] -> "tt"
    | TupE exps -> String.concat " " (List.map (gen_exp env is_match) exps)
    | CallE (id, args) -> parens (func_prefix ^ gen_id id ^ " " ^ gen_call_args env args)
    | IterE (exp, (iter, ids)) -> 
      let exp1 = gen_exp env is_match exp in
      (match iter, ids, exp.it with
      | (List | List1 | ListN _), [], _ -> square_parens exp1 
      | (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
      | (List | List1 | ListN _ | Opt), [(v, _)], _ when not is_match -> parens ("List.map " ^ parens ("fun " ^ var_prefix ^ gen_id v ^ " => " ^ exp1) ^ " " ^ parens (var_prefix ^ gen_id v))
      | (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ when not is_match -> parens ("list_zipWith " ^
        parens ("fun " ^ var_prefix ^ gen_id v ^ " " ^ var_prefix ^ gen_id s ^ " => " ^ gen_tup_exp env exp) ^ " " ^ 
        parens (var_prefix ^ gen_id v) ^ " " ^ 
        parens (var_prefix ^ gen_id s))
      | _ -> exp1
    ) 
    | OptE None -> "[]"
    | OptE (Some exp) -> square_parens (gen_exp env is_match exp)
    | TheE exp -> parens ("the" ^ parens (gen_exp env is_match exp))
    | ListE exps -> (match exps with
      | [] -> "[]"
      | [e] -> if is_match then gen_exp env is_match e else square_parens (gen_exp env is_match e)
      | _ -> square_parens (String.concat ";" (List.map (gen_exp env false) exps)))
    | LenE exp -> "List.length(" ^ gen_exp env is_match exp ^ ")"
    | CatE (exp1, exp2) -> 
      let exp1_option = gen_exp env is_match exp1 in
      let exp2_option = gen_exp env is_match exp2 in      
      if is_match then parens (exp1_option ^ " :: " ^ exp2_option)  else parens (exp1_option ^ " ++ " ^ exp2_option) 
    | IdxE (exp1, exp2) -> parens ("lookup_total " ^ parens (gen_exp env is_match exp1) ^ " " ^ parens (gen_exp env is_match exp2))
    | CaseE (mixop, exp1) -> let actual_id, num_args = gen_case_name env e.note in 
      let gen_exp1 = (match exp1.it with 
        | TupE [] -> ""
        | _ -> gen_exp env is_match exp1) in
      parens (gen_id actual_id ^ "__" ^ gen_mixop mixop ^ " " ^ String.concat "" (List.init num_args (fun _ -> "_ ")) ^ gen_exp1)
    | SubE (exp, _typ1, _typ2) -> gen_exp env is_match exp
    | ProjE (_exp, n) -> string_of_int n (* TODO *)
    | UncaseE (_exp, _mixop) -> "2" (* TODO *)

and gen_tup_exp (env : env) (exp : exp) = 
  match exp.it with
    | TupE exps -> parens (String.concat " , " (List.map (gen_tup_exp env) exps))
    | _ -> gen_exp env false exp

and gen_numtyp (nt : numtyp) =
  match nt with
    | NatT -> "nat"
    | IntT -> "nat"
    | RatT -> "nat"
    | RealT -> "nat"


and gen_typ (env : env) (t: typ) =
  match t.it with
    | VarT (id, args) -> gen_id id ^ (gen_call_args env args)
    | NumT nt -> gen_numtyp nt
    | TextT -> "string"
    | BoolT -> "bool"
    | TupT [] -> "unit"
    | TupT typs -> String.concat " * " (List.map (fun (_, t) -> gen_typ env t) typs)
    | IterT (typ, iter) -> gen_iter_typ iter ^ " " ^ parens (gen_typ env typ)

and gen_exp_args (env : env) (is_match : bool) (e : exp) =
  match e.it with
    | TupE [] -> "_"
    | IterE (e, _binds) -> gen_exp_args env is_match e 
    | TupE exps -> let first_e = List.hd exps in gen_exp env is_match first_e
    | _ -> gen_exp env is_match e

and gen_typ_args (env : env) (t : typ) =
  match t.it with
    | TupT typs -> String.concat " " (List.map (fun (e, t) -> parens (gen_exp_args env true e ^ " : " ^ gen_typ env t)) typs)
    | _ -> parens (gen_typ env t)

and gen_typealias_args (env : env) (t : typ) =
  match t.it with
    | VarT (id, args) -> let genargs = (match args with
      | [] -> ""
      | args' -> String.concat " " (List.map (fun a -> match a.it with 
        | ExpA exp -> gen_exp env false exp
        | TypA typ -> gen_typ env typ) args')) in
      gen_id id ^ " " ^ genargs
    | _ -> gen_typ env t

and gen_relation_param_types (env : env) (t : typ) =
  match t.it with
    | TupT typs -> String.concat " -> " (List.map (fun (_, t) -> gen_typ env t) typs)
    | _ -> gen_typ env t

and gen_bind_typ (env : env) (b : bind) =
  match b.it with 
    | ExpB (_, typ, _) -> gen_typ env typ
    | TypB id -> gen_id id

and gen_bind (env : env) (b : bind) =
  match b.it with 
    | ExpB (id, typ, iters) -> let iter_typs = if iters == [] then "" else String.concat " " (List.map gen_iter_typ iters) ^ " " in
      parens (var_prefix ^ gen_id id ^ " : " ^ iter_typs ^ gen_typ env typ)
    | TypB id -> gen_id id

and gen_bind_arg (env : env) (b : bind) =
  match b.it with
    | ExpB (id, typ, _) -> parens (var_prefix ^ gen_id id ^ " : " ^ gen_typ env typ)
    | TypB id -> parens (gen_id id ^ " : Type")

and gen_inductive_args (env : env) (binds : bind list) =
  match binds with
    | [] -> ""
    | _ -> String.concat " " (List.map (gen_bind_arg env) binds)

and gen_arg_name (env : env) (is_match : bool) (a : arg) = 
  match a.it with
    | ExpA exp -> Some (gen_exp env is_match exp)
    | _ -> None

and gen_inductive_args_name (env : env) (is_match : bool) (a : arg) =
  match a.it with
    | ExpA exp -> gen_exp env is_match exp
    | TypA typ -> gen_typ env typ

and gen_call_args (env : env) (args : arg list) =
  match args with
  | [] -> ""
  | _ -> String.concat " " (List.map parens (List.filter_map (gen_arg_name env false) args))

and gen_match_args (env : env) (args : arg list) = 
  match args with
    | [] -> ""
    | _ -> parens (String.concat ", " (List.filter_map (gen_arg_name env true) args))

and gen_succ (env : env) (n : int) (e : exp) : text =
  match n with
    | 0 -> gen_exp env false e 
    | m -> "S" ^ parens (gen_succ env (m - 1) e)

and transform_path (env : env) (p : path) (is_match : bool) (e : exp) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', e') -> (IdxP (p', e') $$ (p.at, p.note)) :: transform_path env p' is_match e 
    | SliceP (p', _exp1, _exp2) -> (SliceP (p', _exp1, _exp2) $$ (p.at, p.note)) :: transform_path env p' is_match e
    | DotP (p', a) -> (DotP (p', a) $$ (p.at, p.note)) :: transform_path env p' is_match e

and _gen_path_name (env : env) (p : path) (is_match : bool) (e : exp) =
  match p.it with   
    | RootP -> gen_exp env is_match e
    | IdxP (path, exp) -> "lookup_total " ^ parens (_gen_path_name env path is_match e) ^ " " ^ parens (gen_exp env is_match exp) 
    | SliceP (_path, _exp1, _exp2) -> "default_val" (* TODO *)
    | DotP (path, atom) -> gen_typ_name path.note ^ "__" ^ gen_atom atom ^ " " ^ parens (_gen_path_name env path is_match e)

and gen_path (start_exp : exp option) (n : int) (env : env) (paths : path list) (is_match : bool) (update_exp : exp) (exp_name: text) = 
  match paths with
    | {it = DotP _; _} as p :: ps -> let (dot_paths, rest) = list_split is_dot (p :: ps) in 
      let (prefix, name) = (match start_exp with  
        | Some e -> let name = gen_exp env is_match e in (name, name)
        | None -> let name = var_prefix ^ string_of_int n in ("fun " ^ name ^ " => " ^ name, name)
      ) in
      let projection_map delim list_to_map = String.concat delim (List.map (fun p'' -> match p''.it with 
      | DotP (p, a') -> gen_typ_name p.note ^ "__" ^ gen_atom a'
      | _ -> ""
      ) list_to_map) in
      let projection_name = projection_map " " (List.rev dot_paths) ^ " " ^ name in
      let rest_gen = (match rest with
        | [] -> gen_exp env is_match update_exp 
        | {it = IdxP (_, idx_exp); _} :: [] -> gen_list_update_func exp_name projection_name 
        (gen_exp env is_match idx_exp) (gen_exp env is_match update_exp)
        | {it = IdxP (_, idx_exp); _} :: rest_tail -> gen_list_update_func "list_update_func" projection_name
        (gen_exp env is_match idx_exp) (gen_path None (n + 1) env rest_tail is_match update_exp exp_name)
        | [{it = SliceP (_, idx_exp1, idx_exp2); _}] -> gen_list_slice_update projection_name
          (gen_exp env is_match idx_exp1) 
          (gen_exp env is_match idx_exp2) 
          (gen_exp env is_match update_exp)
        | _ -> gen_path None (n + 1) env rest is_match update_exp exp_name
      ) in 
      prefix ^ " <|" ^ projection_map ";" dot_paths ^ " := " ^ rest_gen ^ "|>" 
    | {it = IdxP (_p', idx_exp); _} :: ps -> let list_name = var_prefix ^ string_of_int (n - 1) in ( match ps with 
      | [] -> gen_list_update_func exp_name list_name (gen_exp env is_match idx_exp) (gen_exp env is_match update_exp)
      | _ -> gen_list_update_func "list_update_func" list_name (gen_exp env is_match idx_exp) (gen_path None n env ps is_match update_exp exp_name)
      )
    | {it = SliceP (_p', e1, e2); _} :: _ps -> 
      (* Slice should always be at the end *) 
      gen_list_slice_update (var_prefix ^ string_of_int (n - 1)) 
        (gen_exp env is_match e1) 
        (gen_exp env is_match e2) 
        (gen_exp env is_match update_exp)
    | _ -> ""

and gen_path_start (env : env) (p : path) (is_match : bool) (e : exp) (update_exp : exp) (exp_name : text) =
  let path_list = List.rev (transform_path env p is_match e) in
  parens (gen_path (Some e) 0 env path_list is_match update_exp exp_name)

let rec gen_premises (env : env) (p : prem) =
  match p.it with
    | RulePr (id, _mixop, exp) -> gen_id id ^ " " ^ gen_exp env false exp
    | IfPr exp -> gen_exp env false exp
    | ElsePr -> ""
    | LetPr (_exp1, _exp2, _ids) -> "1"
    | IterPr (p, (iter, ids)) -> (match iter, ids with
      | Opt, [(i, _typ)] -> "List.Forall " ^ parens ( "fun " ^ var_prefix ^ gen_id i ^ " => " ^ gen_premises env p) ^ " " ^ parens (var_prefix ^ gen_id i) 
      | (List | List1 | ListN _), [(i, _typ)] -> "List.Forall " ^ parens ( "fun " ^ var_prefix ^ gen_id i ^ " => " ^ gen_premises env p) ^ " " ^ parens (var_prefix ^ gen_id i) 
      | (List | List1 | ListN _), [(i, _); (i2, _)] -> "List.Forall " ^ parens ("fun '(" ^ var_prefix ^ gen_id i ^ ", " ^ var_prefix ^ gen_id i2 ^ ") => " ^ gen_premises env p) ^ " " ^ 
        parens ("combine " ^ var_prefix ^ gen_id i ^ " " ^ var_prefix ^ gen_id i2)
      | _, _ -> gen_premises env p
    )

let gen_relation_premises (env : env) (premises : prem list) =
  let prems = List.filter (fun p -> p.it <> ElsePr) premises in
  let e = (match prems with
    | [] -> ""
    | _ -> " -> ") in
  String.concat " /\\ " (List.map (gen_premises env) prems) ^ e

let gen_param (env : env) (p : param) = 
  match p.it with
    | ExpP (id, typ) -> parens (var_prefix ^ gen_id id ^ " : " ^ gen_typ env typ)
    | TypP id -> curly_parens (gen_id id)

let gen_inductive_inhabitance_proof (env : env) (id : id) (typcases : typcase list) (binds : bind list) (arg_names: text) =
  let binders = (match binds with 
    | [] -> ""
    | _ -> " " ^ String.concat " " (List.map (fun b -> (match b.it with
      | ExpB (id, typ, _) -> parens (gen_id id ^ " : " ^ gen_typ env typ)
      | TypB id -> curly_parens (gen_id id ^ " : Type")
    )) binds))  in
  "Global Instance Inhabited__" ^ gen_id id ^ binders ^ " : Inhabited " ^ parens (gen_id id ^ arg_names) ^
  let simple_constructors = List.filter (fun (_, (_, typ, _), _) -> typ.it = TupT []) typcases in
  match simple_constructors with
  | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
          "  Admitted"
  | (m, _, _) :: _ -> " := { default_val := " ^ gen_id id ^ "__" ^ gen_mixop m ^ " }"

let gen_record_inhabitance_proof (id : id) (typfields : typfield list) : string =
  "Global Instance Inhabited_" ^ gen_id id ^ " : Inhabited " ^ gen_id id ^ " := \n" ^
  "{default_val := {|\n" ^
      String.concat "" (List.map (fun (a, _, _) -> 
        "\t" ^ gen_id id ^ "__" ^ gen_atom a ^ " := default_val ;\n"
        ) typfields) ^ "|} }"

let gen_record_append_proof (env : env) (ident: text) (typfields : typfield list) =
  "Definition _append_" ^ ident ^ " (arg1 arg2 : " ^ ident ^ ") :=\n" ^ 
  "{|\n\t" ^ String.concat "\t" (List.map (fun (a, (_, t, _), _) -> 
    let typ_name = get_typ_name t in
    let struct_type = Option.map (get_struct_type env) typ_name in 
    (match struct_type with 
      | Some Inductive -> ident ^ "__" ^ gen_atom a ^ " := " ^ "arg1.(" ^ ident ^ "__" ^ gen_atom a ^ "); (* FIXME: This type does not have a trivial way to append *)\n" 
      | _ -> ident ^ "__" ^ gen_atom a ^ " := " ^ "arg1.(" ^ ident ^ "__" ^ gen_atom a ^ ") ++ arg2.(" ^ ident ^ "__" ^ gen_atom a ^ ");\n" 
  )) typfields) ^ "|}.\n\n" ^ 
  "Global Instance Append_" ^ ident ^ " : Append " ^ ident ^ " := { _append arg1 arg2 := _append_" ^ ident ^ " arg1 arg2 }"

let gen_record_setter_instances (ident : text) (constructor_name : text) (typfields : typfield list) = 
  "#[export] Instance eta__" ^ ident ^ " : Settable _ := settable! " ^ constructor_name ^ " <" ^ 
  String.concat ";" (List.map (fun (a, _, _) -> ident ^ "__" ^ gen_atom a) typfields) ^ ">"  

let gen_deftyp (env : env) (binds : bind list) (args : arg list) (id : id) (d : deftyp) =
  match d.it with
    | AliasT typ -> "Definition " ^ gen_id id ^ gen_inductive_args env binds ^  " := " ^ gen_typealias_args env typ
    | StructT typfields -> 
      let type_ident = gen_id id in 
      let constructor_name = "mk" ^ type_ident in
      "Record " ^ type_ident ^ " := " ^ constructor_name ^ "\n{\t" ^
      String.concat "\n;\t" (List.map (fun (a, (_, t, _premises), _) -> 
        type_ident ^ "__" ^ gen_atom a ^ " : " ^ gen_typ env t
      ) typfields) ^ "\n}.\n\n" ^
      gen_record_inhabitance_proof id typfields ^ ".\n\n" ^
      gen_record_append_proof env type_ident typfields ^ ".\n\n" ^ 
      gen_record_setter_instances type_ident constructor_name typfields
    | VariantT typcases -> 
      let arg_names = match args with 
        | [] -> "" 
        | _ -> " " ^ String.concat " " (List.map (gen_inductive_args_name env false) args)
      in 
      "Inductive " ^ gen_id id ^ " " ^ gen_inductive_args env binds ^  " : Type :=\n" ^ 
      String.concat "\n" (List.map (fun (m, (_, t, _premises), _) -> 
      "\t| " ^ gen_id id ^ "__" ^ gen_mixop m ^ gen_typ_args env t ^ ": " ^
      gen_id id ^ arg_names) typcases) ^ ".\n\n" ^ gen_inductive_inhabitance_proof env id typcases binds arg_names

let gen_param_id_used (param : param) =
  match param.it with
    | ExpP (id, _) -> Some (var_prefix ^ gen_id id)
    | _ -> None

let gen_def_params (env : env) (params : param list) =
  let id_params = List.combine (List.init (List.length params) (fun i -> string_of_int i)) params in
  List.map (fun (i, p) -> (match p.it with
    | ExpP (id, typ) -> let var_i = var_prefix ^ (if (gen_id id) = "_" then i else gen_id id) in
      parens (var_i ^ " : " ^ gen_typ env typ)
    | TypP id -> curly_parens (gen_id id)
  )) id_params

let gen_match_clause (params : param list) =
  match params with
    | [] -> ""
    | _ -> let id_params = List.combine (List.init (List.length params) (fun i -> string_of_int i)) params in
    let match_names = List.filter_map (fun (i, p) -> (match p.it with
    | ExpP (id, _) -> Some (var_prefix ^ (if (gen_id id) = "_" then i else gen_id id)) 
    | TypP _ -> None
  )) id_params in 
    "\tmatch " ^ parens (String.concat ", " match_names) ^ " with\n"

let gen_instance (env : env) (id : id) (params : param list) (i : inst) =
  match i.it with
    | InstD (binds, args, deftyp) -> (match deftyp.it with
      | AliasT typ -> "\t\t| " ^ gen_match_args env args ^ " => " ^ gen_typealias_args env typ
      | VariantT typcases -> 
      let inductive_name = gen_id id ^ "__" ^ String.concat "__" (List.map (gen_bind_typ env) binds) 
      in 
      String.concat "\n" (List.map (fun (m, (_, t, _premises), _) -> 
      "\t| " ^ inductive_name ^ "__" ^ gen_mixop m ^ gen_typ_args env t ^ ": " ^ gen_id id ^ " " ^ String.concat " " (List.filter_map gen_param_id_used params)) 
      typcases)
      | _ -> gen_deftyp env binds args id deftyp
    )
let _get_instance_binds (i : inst) =
  match i.it with
    | InstD (binds, args, _) -> (binds, args)
    
let gen_instances (env : env) (params : param list) (id : id) (insts : inst list) =
  let i = List.hd insts in
  match i.it with
  | InstD (_, _, deftyp) -> (match deftyp.it with 
    | AliasT _ -> "Definition " ^ gen_id id ^ 
    String.concat " " (gen_def_params env params) ^ " :=\n"  ^
    gen_match_clause params ^ 
    String.concat "\n" (List.map (gen_instance env id params) insts) ^
    "\n\tend"
    | StructT _ -> "" (* Should not happen *)
    | VariantT _ -> 
    "Inductive " ^ gen_id id ^ 
    String.concat " " (gen_def_params env params) ^ ": Type :=\n" ^
    String.concat "\n" (List.map (gen_instance env id params) insts)
  ) 
  
let gen_clause (env : env) (c : clause) = 
  match c.it with
    | DefD (_binds, args, exp, _premises) -> "\t\t| " ^ gen_match_args env args ^ " => " ^ gen_tup_exp env exp

let gen_clauses (env : env) (params : param list) (clauses : clause list) =
  match clauses with
    | [{it = DefD (_, _, exp, _); _}] when params == [] -> " := " ^ gen_exp env false exp 
    | _ -> " :=\n" ^ gen_match_clause params ^ String.concat "\n" (List.map (gen_clause env) clauses) ^ "\n\tend"

let gen_ids_used (env : env) (binds : bind list) = 
  if binds == [] then "" else "forall " ^ String.concat " " (List.map (gen_bind env) binds) ^ ", "

let gen_rule (env : env) (id : id) (rule : rule) =
  match rule.it with
    | RuleD (rule_id, binds, mixop, exp, prems) -> let rule_id' = if String.empty <> rule_id.it then gen_id rule_id ^ "_" else "" in
    "\t| " ^ gen_id id ^ "__" ^ rule_id' ^ gen_mixop mixop ^ " : " ^ gen_ids_used env binds ^ gen_relation_premises env prems ^ gen_id id ^ " " ^ gen_exp env false exp

let gen_rules (env : env) (id : id) (rules : rule list) =
  String.concat "\n" (List.map (gen_rule env id) rules)

let gen_axiom (env : env) (id : id) (params : param list) (typ : typ) = 
  "Axiom " ^ func_prefix ^ gen_id id ^ " : forall " ^ String.concat " " (List.map (gen_param env) params) ^ ", " ^ gen_typ env typ

let is_inductive (d : def) =
  match d.it with
    | TypD _ |  RelD _ -> true
    | _ -> false

let is_not_hintdef (d : def) =
  match d.it with
    | HintD _ -> false
    | _ -> true

let rec gen_def (env : env) (is_recursive : bool) (d : def)=
  match d.it with
    | TypD (id, _params, [{it = InstD (binds, args, deftyp); _}]) -> gen_deftyp env binds args id deftyp
    | TypD (id, params, insts) -> gen_instances env params id insts
    | RelD (id, _mixop, typ, rules) -> let prefix = if is_recursive then "" else "Inductive " in 
      prefix ^ gen_id id ^ ": " ^ gen_relation_param_types env typ ^ " -> Prop := \n" ^ gen_rules env id rules
    | DecD (id, params, typ, clauses) -> let prefix = if is_recursive then "Fixpoint " else "Definition " in 
      if clauses == [] then
        (gen_axiom env id params typ)
      else 
        (prefix ^ func_prefix ^ gen_id id ^ " "
        ^ String.concat " " (gen_def_params env params)
        ^ ": " ^ gen_typ env typ
        ^ gen_clauses env params clauses)
    | RecD defs -> (match defs with
        | [] -> ""
        | [d] -> gen_def env (not (is_inductive d)) d
        | d :: ds -> let inductive_word = if is_inductive d then "with\n\n" else "" in
          gen_def env false d ^ "\n\n" ^ inductive_word ^ String.concat "\n\n" (List.map (gen_def env true) ds))  
    | _ -> ""

let gen_script (env : env) (il : script) =
  String.concat ".\n\n" (List.map (gen_def env false) (List.filter is_not_hintdef il)) ^ ".\n"

let gen_string (il : script) =
  let env = Case.get_case_env il in 
  "(* Exported Code *)\n" ^
  "From Coq Require Import String List Unicode.Utf8.\n" ^
  "From RecordUpdate Require Import RecordSet.\n" ^
  "Require Import NArith.\n" ^
  "Require Import Arith.\n" ^
  "Require Import BinNat.\n" ^
  "Require Import FloatClass.\n" ^
  "Require Import PrimFloat.\n" ^
  "Require Import SpecFloat.\n" ^
  "Require Import FloatOps.\n" ^
  "Require Import FloatAxioms.\n" ^
  "Require Import FloatLemmas.\n" ^
  "Declare Scope wasm_scope.\n\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Definition the {T : Type} {_ : Inhabited T} (arg : list T) : T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| nil => default_val\n" ^
	"\t\t| v :: vs => v\n" ^
	"\tend.\n\n" ^
  "Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=\n" ^
  "\tmap (fun '(x, y) => f x y) (combine xs ys).\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "\tmatch l, n with\n" ^
  "\t\t| nil, _ => nil\n" ^
  "\t\t| x :: l', 0 => y :: l'\n" ^
  "\t\t| x :: l', S n => x :: list_update l' n y\n" ^
  "\tend.\n\n" ^
  "Fixpoint list_update_func {α: Type} (l: list α) (n: nat) (y: α -> α): list α :=\n" ^
	"\tmatch l, n with\n" ^
	"\t\t| nil, _ => nil\n" ^
	"\t\t| x :: l', 0 => (y x) :: l'\n" ^
	"\t\t| x :: l', S n => x :: list_update_func l' n y\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice {α: Type} (l: list α) (i: nat) (j: nat): list α :=\n" ^
	"\tmatch l, i, j with\n" ^
	"\t\t| nil, _, _ => nil\n" ^
	"\t\t| x :: l', 0, 0 => nil\n" ^
	"\t\t| x :: l', S n, 0 => nil\n" ^
	"\t\t| x :: l', 0, S m => x :: list_slice l' 0 m\n" ^
	"\t\t| x :: l', S n, S m => list_slice l' n m\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=\n" ^
	"\tmatch l, i, j, update_l with\n" ^
	"\t\t| nil, _, _, _ => nil\n" ^
	"\t\t| l', _, _, nil => l'\n" ^
	"\t\t| x :: l', 0, 0, _ => nil\n" ^
	"\t\t| x :: l', S n, 0, _ => nil\n" ^
	"\t\t| x :: l', 0, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'\n" ^
	"\t\t| x :: l', S n, S m, _ => x :: list_slice_update l' n m update_l\n" ^
	"\tend.\n\n" ^
  "Definition list_extend {α: Type} (l: list α) (y: α): list α :=\n" ^
  "\ty :: l.\n\n" ^
  "Class Append (α: Type) := _append : α -> α -> α.\n\n" ^
  "Infix \"++\" := _append (right associativity, at level 60) : wasm_scope.\n\n" ^
  "Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.\n\n" ^
  "Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "\n" ^
  "Open Scope wasm_scope.\n" ^
  "Import ListNotations.\n" ^
  "Import RecordSetNotations.\n" ^
  "(* Generated Code *)\n" ^
  gen_script env il


let gen_file file il =
  let coq_code = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)

