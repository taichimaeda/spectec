open Coqast
open Case

let square_parens s = "[" ^ s ^ "]"
let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"

let comment_parens s = "(* " ^ s ^ " *)"

let family_type_suffix = "entry"
let is_inductive (d : coq_def) = 
  match d.it with
    | (InductiveRelationD _ | InductiveD _) -> true
    | _ -> false
let lst_update = "list_update"
let lst_extend = "list_extend"

let comment_desc_def (def: coq_def): string = 
  match def.it with
    | TypeAliasD _ -> "Type Alias Definition"
    | RecordD _ -> "Record Creation Definition"
    | InductiveD _ -> "Inductive Type Definition"
    | NotationD _ -> "Notation Definition"
    | MutualRecD _ -> "Mutual Recursion"
    | DefinitionD _ -> "Auxiliary Definition"
    | InductiveRelationD _ -> "Inductive Relations Definition"
    | AxiomD _ -> "Axiom Definition"
    | InductiveFamilyD _ -> "Family Type Definition"
    | CoercionD _ -> "Type Coercion Definition"
    | UnsupportedD _ -> ""


let rec string_of_terms (term : coq_term) =
  match term with
    | T_exp_basic (T_bool b) -> string_of_bool b
    | T_exp_basic (T_nat n) -> Z.to_string n
    | T_exp_basic (T_int _i) -> "" (* TODO Manage ints well *)
    | T_exp_basic (T_string s) -> "\"" ^ String.escaped s ^ "\""
    | T_exp_basic T_exp_unit -> "tt"
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
    | T_exp_basic T_mod -> " mod "
    | T_exp_basic T_eq -> " = "
    | T_exp_basic T_neq -> " <> "
    | T_exp_basic T_lt -> " < "
    | T_exp_basic T_gt -> " > "
    | T_exp_basic T_le -> " <= "
    | T_exp_basic T_ge -> " >= "
    | T_exp_basic T_some -> "Some"
    | T_exp_basic T_none -> "None"
    | T_exp_basic T_concat -> " ++ "
    | T_exp_basic T_listconcat -> "@app"
    | T_exp_basic T_listmatch -> " :: "
    | T_exp_basic T_listlength -> "List.length"
    | T_exp_basic T_slicelookup -> "list_slice"
    | T_exp_basic T_listlookup -> "lookup_total"
    | T_exp_basic T_the -> "the"
    | T_exp_basic T_succ -> "S"
    | T_type_basic T_unit -> "unit"
    | T_type_basic T_bool -> "bool"
    | T_type_basic T_nat -> "nat"
    | T_type_basic T_int -> "Z"
    | T_type_basic T_real -> "R"
    | T_type_basic T_string -> "string"
    | T_type_basic T_list -> "list"
    | T_type_basic T_opt -> "option"
    | T_ident ids -> String.concat "__" ids
    | T_update (paths, term1, term2) -> string_of_paths_start paths term1 true term2
    | T_extend (paths, term1, term2) -> string_of_paths_start paths term1 false term2
    | T_list [] -> "[]"
    | T_map (I_option, id, exp) -> parens ("option_map " ^ parens ("fun " ^ id ^ " => " ^ string_of_terms exp) ^ " " ^ parens id)
    | T_map (I_list, id, exp) -> parens ("List.map " ^ parens ("fun " ^ id ^ " => " ^ string_of_terms exp) ^ " " ^ parens id)
    | T_zipwith (I_option, id1, id2, exp) -> parens ("option_zipWith " ^ parens ("fun " ^ id1 ^ " " ^ id2 ^ " => " ^ string_of_terms exp) ^ " " ^ id1 ^ " " ^ id2)
    | T_zipwith (I_list, id1, id2, exp) -> parens ("list_zipWith " ^ parens ("fun " ^ id1 ^ " " ^ id2 ^ " => " ^ string_of_terms exp) ^ " " ^ id1 ^ " " ^ id2)
    | T_record_fields fields -> "{| " ^ (String.concat "; " (List.map (fun (id, term) -> id ^ " := " ^ string_of_terms term) fields)) ^ " |}"
    | T_list entries -> square_parens (String.concat ";" (List.map string_of_terms entries))
    | T_match [] -> ""
    | T_match patterns -> parens (String.concat ", " (List.map string_of_terms patterns))
    | T_app (base_term, args) -> parens (string_of_terms base_term ^ " " ^ String.concat " " (List.map string_of_terms args))
    | T_app_infix (infix_op, term1, term2) -> parens (string_of_terms term1 ^ string_of_terms infix_op ^ string_of_terms term2)
    | T_tuple types -> parens (String.concat " * " (List.map string_of_terms types))
    | T_cast (term, typ) -> parens (string_of_terms term ^ " : " ^ string_of_terms typ)
    | T_unsupported str -> comment_parens ("Unsupported term: " ^ str)

and string_of_ident_terms (term : coq_term) =
  match term with
    | T_app (base_term, args) -> (string_of_terms base_term, String.concat " " (List.map string_of_terms args))
    | _ -> (string_of_terms term, "")

and gen_projection id_list name = parens (String.concat "( " (id_list) ^ " " ^ name ^ String.concat "" (List.init (List.length id_list - 1) (fun _ -> ")")))

and string_of_paths (paths : coq_path_term list) (is_update : bool) (update_term : coq_term) =
  match paths, is_update with
    | [P_sliceupdate (id, term1, term2)], _ -> parens ("list_slice_update " ^ parens (id) ^ " " ^ 
      parens (string_of_terms term1) ^ " " ^ 
      parens (string_of_terms term2) ^ " " ^ 
      parens (string_of_terms update_term))
    | (* MEMO: coq-record-update allows nested indexing of records via ;
               For example: x <| b; c; n := n' |>. *)
      [P_recordlookup (ids, name)], true ->  parens ("fun " ^ name ^ " => " ^ name ^ " <|" ^ String.concat ";" ids ^ " := " ^ string_of_terms update_term ^ "|>")
    | [P_recordlookup (ids, name)], false ->  parens ("fun " ^ name ^ " => " ^ name ^ " <|" ^ String.concat ";" ids ^ " := " ^ lst_extend ^ " " ^ gen_projection ids name ^ " " ^ string_of_terms update_term ^ "|>")
    | [P_listlookup (id, term)], true -> parens (lst_update ^ " " ^ parens (id) ^ " " ^ parens (string_of_terms term) ^ " " ^ parens (string_of_terms update_term))
    | [P_listlookup (id, _)], false -> parens (lst_extend ^ " " ^ parens (id) ^ " " ^ parens (string_of_terms update_term))
    | P_recordlookup (ids, name) :: ps, _ -> parens ("fun " ^ name ^ " => " ^ name ^ " <|" ^ String.concat ";" ids ^ " := " ^ string_of_paths ps is_update update_term ^ "|>")
    | P_listlookup (id, term) :: ps, _ -> parens ("list_update_func " ^ parens (id) ^ " " ^ parens (string_of_terms term) ^ " " ^ parens (string_of_paths ps is_update update_term))
    | _ -> ""


and string_of_paths_start (paths : coq_path_term list) (start_term : coq_term) (is_update : bool) (update_term : coq_term) = 
  match paths, is_update with
    | P_recordlookup (ids, _n) :: ps, _ -> (parens (string_of_terms start_term ^ " <|" ^ String.concat ";" ids ^ " := " ^ 
    (if (ps <> []) 
      then string_of_paths ps is_update update_term
      else parens (lst_extend ^ " " ^ gen_projection ids (string_of_terms start_term) ^ " " ^ string_of_terms update_term) (* Has to be extend as no list lookup *)
    ) ^ "|>"))
    | P_listlookup (_, exp) :: [], true ->  parens (lst_update ^ " " ^ string_of_terms start_term ^ " " ^ string_of_terms exp ^ " " ^ string_of_terms update_term)
    | _ -> "" (* Can be extended to more cases if necessary *)

  

let string_of_binders (binds : binders) = 
  String.concat " " (List.map (fun (id, typ) -> 
    parens (id ^ " : " ^ string_of_terms typ)
  ) binds)

let string_of_binders_ids (binds : binders) = 
  String.concat " " (List.map (fun (id, _) -> id) binds)

let string_of_list_type (id : ident) (args : binders) =

  "Definition " ^ "list__" ^ id ^ " " ^ string_of_binders args ^  " := " ^ parens ("list " ^ parens (id ^ " " ^ string_of_binders_ids args))
  
let string_of_option_type (id : ident) (args : binders) =
  "Definition " ^ "option__" ^ id ^ " " ^ string_of_binders args ^  " := " ^ parens ("option " ^ parens (id ^ " " ^ string_of_binders_ids args))

let string_of_match_binders (binds : binders) =
  parens (String.concat ", " (List.map (fun (id, _) -> id) binds))

let string_of_inferred_types (types : inferred_types) =
  String.concat " " (List.map (fun typ -> curly_parens (string_of_terms typ)) types)

let string_of_relation_args (args : relation_args) = 
  String.concat " -> " (List.map string_of_terms args)

let string_of_record (id: ident) (entries : record_entry list) = 
  let constructor_name = "mk" ^ id in

  (* Standard Record definition *)
  "Record " ^ id ^ " := " ^ constructor_name ^ "\n{\t" ^ 
  String.concat "\n;\t" (List.map (fun (record_id, typ, _) -> 
    record_id ^ " : " ^ string_of_terms typ) entries) ^ "\n}.\n\n" ^

  (* Inhabitance proof for default values *)
  "Global Instance Inhabited_" ^ id ^ " : Inhabited " ^ id ^ " := \n" ^
  "{default_val := {|\n\t" ^
      String.concat ";\n\t" (List.map (fun (record_id, _, _) -> 
        record_id ^ " := default_val") entries) ^ "|} }.\n\n" ^

  string_of_list_type id [] ^ ".\n\n" ^
  string_of_option_type id [] ^ ".\n\n" ^
  (* Record Append proof (TODO might need information on type to improve this) *)
  "Definition _append_" ^ id ^ " (arg1 arg2 : " ^ id ^ ") :=\n" ^ 
  "{|\n\t" ^ String.concat "\t" ((List.map (fun (record_id, _, s_typ) -> (
    match s_typ with 
      | Some Inductive -> record_id ^ " := " ^ "arg1.(" ^ record_id ^ "); (* FIXME: This type does not have a trivial way to append *)\n" 
      | _ -> record_id ^ " := " ^ "arg1.(" ^ record_id ^ ") ++ arg2.(" ^ record_id ^ ");\n" 
    )
  )) entries) ^ "|}.\n\n" ^ 
  "Global Instance Append_" ^ id ^ " : Append " ^ id ^ " := { _append arg1 arg2 := _append_" ^ id ^ " arg1 arg2 }.\n\n" ^

  (* Setter proof *)
  "#[export] Instance eta__" ^ id ^ " : Settable _ := settable! " ^ constructor_name ^ " <" ^ 
  String.concat ";" (List.map (fun (record_id, _, _) -> record_id) entries) ^ ">"  

let string_of_inductive_def (id : ident) (args : inductive_args) (entries : inductive_type_entry list) = 
  "Inductive " ^ id ^ " " ^ string_of_binders args ^ " : Type :=\n\t" ^
  String.concat "\n\t" (List.map (fun (case_id, binds) ->
    "| " ^ case_id ^ " " ^ string_of_binders binds ^ " : " ^ id ^ " " ^ string_of_binders_ids args   
  )  entries) ^ ".\n\n" ^

  string_of_list_type id args ^ ".\n\n" ^
  string_of_option_type id args ^ ".\n\n" ^
  (* Inhabitance proof for default values *)
  let binders = string_of_binders args in 
  let binder_ids = string_of_binders_ids args in
  "Global Instance Inhabited__" ^ id ^ " " ^ binders ^ " : Inhabited " ^ parens (id ^ " " ^ binder_ids) ^
  match entries with
    | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
            "\tAdmitted"
    | (* MEMO: Uses the first constructor as default value *)
      (case_id, binds) :: _ -> " := { default_val := " ^ case_id ^ " " ^ binder_ids ^ 
      (* MEMO: Supply default value of arguments to case_id *)
      " " ^ (String.concat " " (List.map (fun _ -> "default_val" ) binds)) ^ " }.\n\n" ^
  (* TODO: e.g.
    Global Instance Inhabited__functype : Inhabited (functype) :=
      { default_val := functype__ default_val default_val }. *)
  (* TODO: e.g. 
    Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }. *)

  (* Decidable equality proof *)
  "Definition " ^ id ^ "_eq_dec : forall " ^ binders ^ " (v1 v2 : " ^ id ^ " " ^ binder_ids ^ "),\n" ^
    "{v1 = v2} + {v1 <> v2}.\n" ^
  "Proof. Admitted.\n\n" ^
  (* "Proof. decidable_equality. Defined.\n\n" ^ *)
  "Definition " ^ id ^ "_eqb " ^ binders ^ " (v1 v2 : " ^ id ^ " " ^ binder_ids ^ ") : bool :=\n" ^
    id ^ "_eq_dec " ^ binder_ids ^ " v1 v2.\n" ^  
  "Definition eq" ^ id ^ "P " ^ binders ^ " : Equality.axiom " ^ parens (id ^ "_eqb " ^ binder_ids) ^ " :=\n" ^
    "eq_dec_Equality_axiom " ^ parens (id ^ " " ^ binder_ids) ^ " " ^ parens (id ^ "_eq_dec " ^ binder_ids) ^ ".\n\n" ^
  "Canonical Structure " ^ id ^ "_eqMixin " ^ binders ^ " := EqMixin " ^ parens ("eq" ^ id ^ "P " ^ binder_ids) ^ ".\n" ^
  "Canonical Structure " ^ id ^ "_eqType " ^ binders ^ " :=\n" ^
    "Eval hnf in EqType " ^ parens (id ^ " " ^ binder_ids) ^ " " ^ parens (id ^ "_eqMixin " ^ binder_ids)
  (* TODO: e.g.
    Definition functype_eq_dec : forall (tf1 tf2 : functype),
      {tf1 = tf2} + {tf1 <> tf2}.
    Proof. decidable_equality. Defined.

    Definition functype_eqb v1 v2 : bool := functype_eq_dec v1 v2.
    Definition eqfunctypeP : Equality.axiom functype_eqb :=
      eq_dec_Equality_axiom functype functype_eq_dec.

    Canonical Structure functype_eqMixin := EqMixin eqfunctypeP.
    Canonical Structure functype_eqType :=
      Eval hnf in EqType functype functype_eqMixin. *)

let string_of_definition (prefix : string) (id : ident) (binders : binders) (return_type : return_type) (clauses : clause_entry list) = 
  match clauses with
    | [(_, exp)] when binders == [] -> prefix ^ id ^ " : " ^ string_of_terms return_type ^ " := " ^ string_of_terms exp
    | _ -> prefix ^ id ^ " " ^ string_of_binders binders ^ " : " ^ string_of_terms return_type ^ " :=\n" ^
  "\tmatch " ^ string_of_match_binders binders ^ " with\n\t\t" ^
  String.concat "\n\t\t" (List.map (fun (match_term, exp) -> 
    "| " ^ string_of_terms match_term ^ " => " ^ string_of_terms exp) clauses) ^
  "\n\tend"

let rec string_of_premise (prem : coq_premise) =
  match prem with
    | P_if term -> string_of_terms term
    | P_rule (id, terms) -> parens (id ^ " " ^ String.concat " " (List.map string_of_terms terms))
    | P_neg p -> parens ("~" ^ string_of_premise p)
    | P_else -> "otherwise" (* Will be removed by an else pass *)
    | P_listforall (iterator, p, ids) -> 
      let option_conversion = if iterator = I_option then "option_to_list " else "" in
      (match ids with
      | [v] -> "List.Forall " ^ parens ( "fun " ^ v ^ " => " ^ string_of_premise p) ^ " " ^ parens (option_conversion ^ v)
      | [v; s] -> "List.Forall2 " ^ parens ("fun " ^ v ^ " " ^ s ^ " => " ^ string_of_premise p) ^ " " ^ parens (option_conversion ^ v) ^ " " ^ parens (option_conversion ^ s)
      | _ -> assert false (* Should not happen *)
    )
    | P_unsupported str -> comment_parens ("Unsupported premise: " ^ str)
  
let string_of_typealias (id : ident) (binds : binders) (typ : coq_term) = 
  "Definition " ^ id ^ " " ^ string_of_binders binds ^ " := " ^ string_of_terms typ ^ ".\n\n" ^ 
  string_of_list_type id binds ^ ".\n\n" ^
  string_of_option_type id binds


let string_of_inductive_relation (prefix : string) (id : ident) (args : relation_args) (relations : relation_type_entry list) = 
  prefix ^ id ^ ": " ^ string_of_relation_args args ^ " -> Prop :=\n\t" ^
  String.concat "\n\t" (List.map (fun ((case_id, binds), premises, end_terms) ->
    let string_prems = String.concat " -> " (List.map string_of_premise premises) ^ (if premises <> [] then " -> " else "") in
    let forall_quantifiers = if binds <> [] then "forall " ^ string_of_binders binds ^ ", " else ""in
    "| " ^ case_id ^ " : " ^ forall_quantifiers ^ string_prems ^ id ^ " " ^ String.concat " " (List.map string_of_terms end_terms)
  ) relations)

let string_of_axiom (id : ident) (binds : binders) (r_type: return_type) =
  "Axiom " ^ id ^ " : forall " ^ string_of_binders binds ^ ", " ^ string_of_terms r_type

let is_typealias_familytype ((_, f_type) : family_entry) = 
  match f_type with
    | TypeAliasT _ -> true
    | _ -> false

(* TODO refactor this function so it is not necessary to look at the head of the list.
Extend this when necessary for inductive types to also have coercion*)
let string_of_family_types (id : ident) (entries : family_entry list) = 
  (* MEMO: Instances of InductiveFamilyD are printed as an individual InductiveD
           except for when each instance is type alias to another type *)
  if is_typealias_familytype (List.hd entries) then 
  (* MEMO: Assume all entries are type aliases and print them in a single inductive type definition *)
  (* TODO: e.g.
    Inductive val_: Type :=
    | val___inn__entry : iN -> val_
    | val___fnn__entry : fN -> val_. *)
  "Inductive " ^ id ^ ": Type :=\n\t" ^  
  String.concat "\n\t" (List.map (fun (entry_id, f_deftyp) -> match f_deftyp with
    | TypeAliasT term -> "| " ^ entry_id ^ "__" ^ family_type_suffix ^ " : " ^ string_of_terms term ^ " -> " ^ id   
    | _ -> ""
  ) entries) ^ ".\n\n" ^

  (* Inhabitance proof*)
  "Global Instance Inhabited__" ^ id ^ " : Inhabited " ^ id ^
  (match entries with
    | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
            "\tAdmitted"
    | (case_id, (TypeAliasT _)) :: _ -> " := { default_val := " ^ case_id ^ "__" ^ family_type_suffix ^ " default_val" ^ " }"
    | _ -> "(* FIXME: no inhabitant found! *) .\n" ^
           "\tAdmitted"
  ) ^ ".\n\n" ^
  
  (* Coercions (TODO make this work better (only really works for T_ident terms and constant dependent types)) *)
  string_of_list_type id [] ^ ".\n\n" ^
  string_of_option_type id [] ^ ".\n\n" ^
  String.concat ".\n\n" (List.map (fun (entry_id, f_deftyp) -> match f_deftyp with
  | TypeAliasT term -> 
    let (typealias_id, args) = string_of_ident_terms term in
    let opt_func = "option__" ^ typealias_id ^ "__" ^ id in
    "Coercion " ^ entry_id ^ "__" ^ family_type_suffix ^ " : " ^ typealias_id ^ " >-> " ^ id ^ ".\n\n" ^
    "Definition list__" ^ typealias_id ^ "__" ^ id ^ " : " ^ "list__" ^ typealias_id ^ " " ^ args ^ " -> " ^ "list__" ^ id ^ " := map " ^ entry_id ^ "__" ^ family_type_suffix ^ ".\n\n" ^
    "Coercion list__" ^ typealias_id ^ "__" ^ id ^ " : list__" ^ typealias_id ^ " >-> " ^ "list__" ^ id ^ ".\n\n" ^
    "Definition " ^ opt_func ^ " : option__" ^ typealias_id ^ " -> " ^ "option__" ^ id ^ " := option_map " ^ entry_id ^ "__" ^ family_type_suffix ^ ".\n\n" ^
    "Coercion " ^ opt_func ^ " : option__" ^ typealias_id ^ " >-> " ^ "option__" ^ id
  | _ -> ""
) entries)
  else
  (* MEMO: Otherwise print each instance as a standalone inductive type definition
           and add another definition to group them all *)
  String.concat ".\n\n" (List.map (fun (entry_id, f_deftyp) -> match f_deftyp with
    | InductiveT i_entry -> string_of_inductive_def entry_id [] i_entry
    | _ -> ""
  ) entries) ^ ".\n\n" ^
  (* TODO: e.g.
    Inductive unop_  : Type :=
    | unop___inn__entry (arg : unop___inn) : unop_ 
    | unop___fnn__entry (arg : unop___fnn) : unop_ . *)
  string_of_inductive_def id [] (List.map (fun (entry_id, _) -> (entry_id ^ "__" ^ family_type_suffix, [("arg" , T_ident [entry_id])])) entries)

let string_of_notation (id : ident) (term : coq_term) = 
  "Notation " ^ id ^ " := " ^ string_of_terms term ^ ".\n\n" ^
  string_of_list_type id [] ^ ".\n\n" ^
  string_of_option_type id []

let string_of_coercion (func_name : func_name) (typ1 : ident) (typ2 : ident) =
  let list_func = "list__" ^ typ1 ^ "__" ^ typ2 in
  let opt_func = "option__" ^ typ1 ^ "__" ^ typ2 in
  "Coercion " ^ func_name ^ " : " ^ typ1 ^ " >-> " ^ typ2 ^ ".\n\n" ^
  "Definition " ^ list_func ^ " : list__" ^ typ1 ^ " -> " ^ "list__" ^ typ2 ^ " := map " ^ func_name ^ ".\n\n" ^
  "Coercion " ^ list_func ^ " : list__" ^ typ1 ^ " >-> " ^ "list__" ^ typ2 ^ ".\n\n" ^
  "Definition " ^ opt_func ^ " : option__" ^ typ1 ^ " -> " ^ "option__" ^ typ2 ^ " := option_map " ^ func_name ^ ".\n\n" ^
  "Coercion " ^ opt_func ^ " : option__" ^ typ1 ^ " >-> " ^ "option__" ^ typ2

let rec string_of_def (recursive : bool) (def : coq_def) = 
  comment_parens (comment_desc_def def ^ " at: " ^ Util.Source.string_of_region (def.at)) ^ "\n" ^ 
  match def.it with
    | TypeAliasD (id, binds, typ) -> string_of_typealias id binds typ
    | RecordD (id, entries) -> string_of_record id entries
    | InductiveD (id, args, entries) -> string_of_inductive_def id args entries
    | NotationD (id, coq_term) -> string_of_notation id coq_term
    | MutualRecD defs -> (match defs with
      | [] -> ""
      | [d] -> string_of_def (not (is_inductive d)) d
      | d :: defs -> let prefix = if is_inductive d then "\n\nwith\n\n" else "\n\n" in
        string_of_def false d ^ prefix ^ String.concat prefix (List.map (string_of_def true) defs))
    | DefinitionD (id, binds, typ, clauses) -> let prefix = if recursive then "Fixpoint " else "Definition " in
      string_of_definition prefix id binds typ clauses
    | InductiveRelationD (id, args, relations) -> let prefix = if recursive then "" else "Inductive " in
      string_of_inductive_relation prefix id args relations
    | AxiomD (id, binds, r_type) -> string_of_axiom id binds r_type
    | InductiveFamilyD (id, entries) -> string_of_family_types id entries 
    | CoercionD (func_name, typ1, typ2) -> string_of_coercion func_name typ1 typ2
    | UnsupportedD str -> comment_parens ("Unsupported Definition: " ^ str)

(* TODO: Use multi-line string or read form a template file instead
         Use spaces for indentation rather than tabs *)
let exported_string = 
  "(* Exported Code *)\n" ^
  "From Coq Require Import String List Unicode.Utf8 Reals.\n" ^
  "From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool seq eqtype.\n" ^
  "From RecordUpdate Require Import RecordSet.\n" ^
  "Require Import NArith.\n" ^
  "Require Import Arith.\n" ^
  "Declare Scope wasm_scope.\n\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => default_val\n" ^
	"\t\t| Some v => v\n" ^
	"\tend.\n\n" ^
  "Definition list_zipWith {X Y Z : Type} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=\n" ^
  "\tmap (fun '(x, y) => f x y) (combine xs ys).\n\n" ^
  "Definition option_zipWith {α β γ: Type} (f: α → β → γ) (x: option α) (y: option β): option γ := \n" ^
  "\tmatch x, y with\n" ^
  "\t\t| Some x, Some y => Some (f x y)\n" ^
  "\t\t| _, _ => None\n" ^
  "\tend.\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "\tmatch l, n with\n" ^
  "\t\t| nil, _ => nil\n" ^
  "\t\t| x :: l', 0 => y :: l'\n" ^
  "\t\t| x :: l', S n => x :: list_update l' n y\n" ^
  "\tend.\n\n" ^
  "Definition option_append {α: Type} (x y: option α) : option α :=\n" ^
  "\tmatch x with\n" ^
  "\t\t| Some _ => x\n" ^
  "\t\t| None => y\n" ^
  "\tend.\n\n" ^
  "Definition option_map {α β : Type} (f : α -> β) (x : option α) : option β :=\n" ^
	"\tmatch x with\n" ^
	"\t\t| Some x => Some (f x)\n" ^
	"\t\t| _ => None\n" ^
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
	"\t\t| x :: l', S n, m => list_slice l' n m\n" ^
	"\tend.\n\n" ^
  "Fixpoint list_slice_update {α: Type} (l: list α) (i: nat) (j: nat) (update_l: list α): list α :=\n" ^
	"\tmatch l, i, j, update_l with\n" ^
	"\t\t| nil, _, _, _ => nil\n" ^
	"\t\t| l', _, _, nil => l'\n" ^
	"\t\t| x :: l', 0, 0, _ => nil\n" ^
	"\t\t| x :: l', S n, 0, _ => nil\n" ^
	"\t\t| x :: l', 0, S m, y :: u_l' => y :: list_slice_update l' 0 m u_l'\n" ^
	"\t\t| x :: l', S n, m, _ => x :: list_slice_update l' n m update_l\n" ^
	"\tend.\n\n" ^
  "Definition list_extend {α: Type} (l: list α) (y: α): list α :=\n" ^
  "\ty :: l.\n\n" ^
  "Class Append (α: Type) := _append : α -> α -> α.\n\n" ^
  "Infix \"++\" := _append (right associativity, at level 60) : wasm_scope.\n\n" ^
  "Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.\n\n" ^
  "Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.\n\n" ^
  "Global Instance Append_nat : Append (nat) := { _append n1 n2 := n1 + n2}.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_Z : Inhabited Z := { default_val := Z0 }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "Definition option_to_list {T: Type} (arg : option T) : list T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| None => nil\n" ^
  "\t\t| Some a => a :: nil\n" ^ 
	"\tend.\n\n" ^
  "Coercion option_to_list: option >-> list.\n\n" ^
  "Definition option_eq_dec (A : Type) (eq_dec : forall (x y : A), {x = y} + {x <> y}):\n" ^
  "  forall (x y : option A), {x = y} + {x <> y}.\n" ^
  "Proof.\n" ^
  "  move=> x y.\n" ^
  "  case: x; case: y; try by [left | right].\n" ^
  "  move => x' y'.\n" ^
  "  case: (eq_dec x' y') => H.\n" ^
  "  - left. by congr Some.\n" ^
  "  - right. move => [Hcontra]. by apply: H.\n" ^
  "Qed.\n\n" ^
  "Ltac decidable_equality_step :=\n" ^
  "  first [\n" ^
  "      by apply: eq_comparable\n" ^
  "    | apply: List.list_eq_dec\n" ^
  "    | apply: option_eq_dec\n" ^
  "    | apply: PeanoNat.Nat.eq_dec\n" ^
  "    | by eauto\n" ^
  "    | intros; apply: decP; by (exact _ || eauto)\n" ^
  "    | decide equality ].\n\n" ^
  "Ltac decidable_equality :=\n" ^
  "  repeat decidable_equality_step.\n\n" ^
  "Lemma eq_dec_Equality_axiom : forall t (eq_dec : forall x y : t, {x = y} + {x <> y}),\n" ^
  "  let eqb v1 v2 := is_left (eq_dec v1 v2) in\n" ^
  "  Equality.axiom eqb.\n" ^
  "Proof.\n" ^
  "  move=> t eq_dec eqb x y. rewrite /eqb. case: (eq_dec x y).\n" ^
  "  - move=> E. by apply/ReflectT.\n" ^
  "  - move=> E. by apply/ReflectF.\n" ^
  "Qed.\n\n" ^
  "Open Scope wasm_scope.\n" ^
  "Import ListNotations.\n" ^
  "Import RecordSetNotations.\n\n"
  

let string_of_script (coq_il : coq_script) =
  exported_string ^ 
  "(* Generated Code *)\n" ^
  String.concat ".\n\n" (List.map (string_of_def false) coq_il) ^ "."