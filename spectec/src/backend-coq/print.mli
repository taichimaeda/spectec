val string_of_terms : Coqast.coq_term -> string
val string_of_paths :
  Coqast.coq_path_term list -> string -> Coqast.coq_term -> string
val string_of_paths_start :
  Coqast.coq_path_term list ->
  Coqast.coq_term -> string -> Coqast.coq_term -> string
val string_of_binders : Coqast.binders -> string
val string_of_binders_ids : Coqast.binders -> string
val string_of_list_type : string -> Coqast.binders -> string
val string_of_match_binders : Coqast.binders -> string
val string_of_inferred_types : Coqast.inferred_types -> string
val string_of_relation_args : Coqast.relation_args -> string
val string_of_record : string -> Coqast.record_entry list -> string
val string_of_inductive_def :
  string -> Coqast.binders -> Coqast.inductive_type_entry list -> string
val string_of_definition :
  string ->
  string ->
  Coqast.binders -> Coqast.coq_term -> Coqast.clause_entry list -> string
val string_of_premise : Coqast.coq_premise -> string
val string_of_typealias :
  string -> Coqast.binders -> Coqast.coq_term -> string
val string_of_inductive_relation :
  string ->
  string -> Coqast.relation_args -> Coqast.relation_type_entry list -> string
val string_of_axiom : string -> Coqast.binders -> Coqast.coq_term -> string
val string_of_family_types : string -> Coqast.family_entry list -> string
val string_of_notation : string -> Coqast.coq_term -> string
val string_of_coercion : string -> string -> string -> string
val string_of_def : bool -> Coqast.coq_def -> string
val string_of_script : Coqast.coq_script -> string
