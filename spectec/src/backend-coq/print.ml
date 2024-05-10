open Coqast

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"

let is_inductive (d : coq_def) = 
  match d with
    | (InductiveRelationD _ | InductiveD _) -> true
    | _ -> false

let rec string_of_terms (term : coq_term) =
  match term with
    | T_exp_basic (T_bool b) -> string_of_bool b
    | T_exp_basic (T_nat n) -> Z.to_string n
    | T_exp_basic (T_int _i) -> "" (* TODO Manage ints well *)
    | T_exp_basic (T_string s) -> "\"" ^ String.escaped s ^ "\""
    | T_exp_basic T_not -> "~"
    | T_exp_basic T_plusminus -> "" (* TODO *)
    | T_exp_basic T_minusplus -> "" (* TODO *)
    | T_exp_basic T_and -> " /\\ "
    | T_exp_basic T_or -> " \\/ "
    | T_exp_basic T_impl -> " -> "
    | T_exp_basic T_equiv -> " <-> "
    | T_exp_basic T_add -> " + "
    | T_exp_basic T_sub -> " - "
    | T_exp_basic T_mul -> " * "
    | T_exp_basic T_div -> " / "
    | T_exp_basic T_exp -> " ^ "
    | T_exp_basic T_eq -> " = "
    | T_exp_basic T_neq -> " <> "
    | T_exp_basic T_lt -> " < "
    | T_exp_basic T_gt -> " > "
    | T_exp_basic T_le -> " <= "
    | T_exp_basic T_ge -> " >= "
    | T_exp_basic T_some -> "Some"
    | T_exp_basic T_none -> "None"
    | T_exp_basic T_concat -> " ++ "
    | T_exp_basic T_listmatch -> " :: "
    | T_exp_basic T_listlength -> "List.length"
    | T_exp_basic T_listlookup -> "lookup_total"
    | T_exp_basic T_slicelookup -> "list_slice"
    | T_exp_basic T_the -> "the"
    | T_type_basic T_unit -> "unit"
    | T_type_basic T_bool -> "bool"
    | T_type_basic T_nat -> "nat"
    | T_type_basic T_int -> "Z"
    | T_type_basic T_string -> "string"
    | T_type_basic T_list -> "list"
    | T_type_basic T_opt -> "option"
    | T_ident ids -> String.concat "__" ids
    | T_update _ -> "" (* TODO *)
    | T_extend _ -> "" (* TODO *)
    | T_list [] -> "[]"
    | T_list entries -> square_parens (String.concat ";" (List.map string_of_terms entries))
    | T_match patterns -> parens (String.concat ", " (List.map string_of_terms patterns))
    | T_app (base_term, args) -> parens (string_of_terms base_term ^ " " ^ String.concat " " (List.map string_of_terms args))
    | T_app_infix (infix_op, term1, term2) -> parens (string_of_terms term1 ^ string_of_terms infix_op ^ string_of_terms term2)
    | T_tuple types -> String.concat "*" (List.map string_of_terms types)
    | T_unsupported str -> "(* Unsupported Term: " ^ str ^ " *)"

let string_of_binders (binds : binders) = 
  String.concat " " (List.map (fun (id, typ) -> 
    parens (id ^ " : " ^ string_of_terms typ)
  ) binds)

let string_of_binders_ids (binds : binders) = 
  String.concat " " (List.map (fun (id, _) -> id) binds)

let string_of_match_binders (binds : binders) =
  parens (String.concat "," (List.map (fun (id, _) -> id) binds))

let string_of_inferred_types (types : inferred_types) =
  String.concat " " (List.map (fun typ -> curly_parens (string_of_terms typ)) types)

let string_of_relation_args (args : relation_args) = 
  String.concat " -> " (List.map string_of_terms args)

let string_of_record (id: ident) (entries : record_entry list) = 
  let constructor_name = "mk" ^ id in

  (* Standard Record definition *)
  "Record " ^ id ^ " := " ^ constructor_name ^ "\n{\t" ^ 
  String.concat "\n;\t" (List.map (fun (record_id, typ) -> 
    record_id ^ " : " ^ string_of_terms typ) entries) ^ "\n}.\n\n" ^

  (* Inhabitance proof for default values *)
  "Global Instance Inhabited_" ^ id ^ " : Inhabited " ^ id ^ " := \n" ^
  "{default_val := {|\n\t" ^
      String.concat ";\n\t" (List.map (fun (record_id, _) -> 
        record_id ^ " := default_val") entries) ^ "|} }.\n\n" ^
  
  (* Record Append proof (TODO might need information on type to improve this) *)
  "Definition _append_" ^ id ^ " (arg1 arg2 : " ^ id ^ ") :=\n" ^ 
  "{|\n\t" ^ String.concat "\t" ((List.map (fun (record_id, _) -> 
    id ^ " := " ^ "arg1.(" ^ record_id ^ ") ++ arg2.(" ^ record_id ^ ");\n" 
  )) entries) ^ "|}.\n\n" ^ 
  "Global Instance Append_" ^ id ^ " : Append " ^ id ^ " := { _append arg1 arg2 := _append_" ^ id ^ " arg1 arg2 }.\n\n" ^

  (* Setter proof *)
  "#[export] Instance eta__" ^ id ^ " : Settable _ := settable! " ^ constructor_name ^ " <" ^ 
  String.concat ";" (List.map (fun (record_id, _) -> record_id) entries) ^ ">"  

let string_of_inductive_def (id : ident) (args : inductive_args) (entries : inductive_type_entry list) = 
  "Inductive " ^ id ^ " " ^ string_of_binders args ^ " : Type :=\n\t" ^
  String.concat "\n\t" (List.map (fun (case_id, binds) ->
    "| " ^ case_id ^ " " ^ string_of_binders binds ^ " : " ^ id ^ string_of_binders_ids args   
  )  entries) ^ ".\n\n" ^

  (* Inhabitance proof for default values *)
  let inhabitance_binders = string_of_binders args in 
  "Global Instance Inhabited__" ^ id ^ inhabitance_binders ^ " : Inhabited " ^ parens (id ^ string_of_binders_ids args) ^
  let simple_constructors = List.filter (fun (_, binders) -> binders = []) entries in
  match simple_constructors with
    | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
            "  Admitted"
    | (case_id, _) :: _ -> " := { default_val := " ^ case_id ^ " }"

let string_of_definition (prefix : string) (id : ident) (i_types : inferred_types) (binders : binders) (return_type : return_type) (clauses : clause_entry list) = 
  prefix ^ id ^ " " ^ string_of_inferred_types i_types ^ " " ^ string_of_binders binders ^ " : " ^ string_of_terms return_type ^ " :=\n" ^
  "\tmatch " ^ string_of_match_binders binders ^ " with\n\t\t" ^
  String.concat "\n\t\t" (List.map (fun (match_term, exp) -> 
    "| " ^ string_of_terms match_term ^ " => " ^ string_of_terms exp) clauses) ^
  "\n\tend"

let string_of_premises (_prems : coq_premises list) =
  ""
  
let string_of_typealias (id : ident) (binds : binders) (typ : coq_term) = 
  "Definition " ^ id ^ " " ^ string_of_binders binds ^ " := " ^ string_of_terms typ

let string_of_inductive_relation (prefix : string) (id : ident) (args : relation_args) (relations : relation_type_entry list) = 
  prefix ^ id ^ " " ^ string_of_relation_args args ^ " -> Prop :=\n\t" ^
  String.concat "\n\t" (List.map (fun ((case_id, binds), premises, end_term) ->
    "| " ^ case_id ^ " : forall " ^ string_of_binders binds ^ ", " ^ string_of_premises premises ^ " -> " ^ string_of_terms end_term
  ) relations)

let string_of_axiom (id : ident) (binds : binders) (r_type: return_type) =
  "Axiom " ^ id ^ " : forall " ^ string_of_binders binds ^ " , " ^ string_of_terms r_type


let rec string_of_def (recursive : bool) (def : coq_def) = 
  match def with
    | TypeAliasD (id, binds, typ) -> string_of_typealias id binds typ
    | RecordD (id, entries) -> string_of_record id entries
    | InductiveD (id, args, entries) -> string_of_inductive_def id args entries
    | MutualRecD defs -> (match defs with
      | [] -> ""
      | [d] -> string_of_def true d
      | d :: defs -> let prefix = if is_inductive d then "with\n\n" else "" in
        string_of_def false d ^ "\n\n" ^ prefix ^ String.concat "\n\n" (List.map (string_of_def true) defs)
      )
    | DefinitionD (id, inferred_types, binds, typ, clauses) -> let prefix = if recursive then "Fixpoint " else "Definition " in
      string_of_definition prefix id inferred_types binds typ clauses
    | InductiveRelationD (id, args, relations) -> let prefix = if recursive then "" else "Inductive " in
      string_of_inductive_relation prefix id args relations
    | AxiomD (id, binds, r_type) -> string_of_axiom id binds r_type 
    | UnsupportedD str -> "(* Unsupported Definition: " ^ str ^ "*)"

let string_of_script (coq_il : coq_script) =
  String.concat "\n\n" (List.map (string_of_def false) coq_il) 