open Case
open Util.Source 


type nat = Z.t

type ident = string

(* binder names *)
type name = string
type func_name = string

type coq_basic_types = 
  | T_unit
  | T_bool
  | T_nat
  | T_int
  | T_string
  | T_list
  | T_opt

type coq_basic_term = 
  | T_bool of bool
  | T_nat of nat
  | T_int of int
  | T_string of string
  | T_exp_unit
  | T_not
  | T_plusminus
  | T_minusplus
  | T_and
  | T_or
  | T_impl
  | T_equiv
  | T_add
  | T_sub
  | T_mul
  | T_div
  | T_exp
  | T_mod
  | T_eq
  | T_neq
  | T_lt
  | T_gt
  | T_le
  | T_ge
  | T_some
  | T_none
  | T_concat
  | T_listconcat
  | T_listmatch
  | T_listlength
  | T_slicelookup
  | T_listlookup
  | T_succ 
  | T_the

and coq_path_term =
  | P_recordlookup of (ident list * ident)
  | P_listlookup of (ident * coq_term)
  | P_sliceupdate of (ident * coq_term * coq_term)

and iterator =
  | I_option
  | I_list

and coq_term = 
  | T_exp_basic of coq_basic_term
  | T_type_basic of coq_basic_types
  | T_ident of ident list
  | T_update of (coq_path_term list * coq_term * coq_term)
  | T_extend of (coq_path_term list * coq_term * coq_term)
  | T_list of (coq_term list)
  | T_map of (iterator * ident * coq_term)
  | T_zipwith of (iterator * ident * ident * coq_term)
  | T_record_fields of (ident * coq_term) list
  | T_match of (coq_term list)
  | T_app of (coq_term * (coq_term list))
  | T_app_infix of (coq_term * coq_term * coq_term) (* Same as above but first coq_term is placed in the middle *)
  | T_tuple of (coq_term list) 
  | T_cast of (coq_term * coq_term)
  | T_unsupported of string

and coq_premise =
  | P_if of coq_term
  | P_neg of coq_premise
  | P_rule of ident * coq_term list
  | P_else
  | P_listforall of iterator * coq_premise * ident list
  | P_unsupported of string

and binders = (ident * coq_term) list

and record_entry = (ident * coq_term * struct_type option)

(* MEMO: Denotes each constructor of the inductive type definition in Coq *)
and inductive_type_entry = (ident * binders)

(* MEMO: Denotes each constructor of the inductive type definition in Coq
         which may take premises in addition to inductive_type_entry *)
(* MEMO: The list of coq_term denotes the arguments to the relation
         in the conclusion of the corresponding constructor *)
and relation_type_entry = inductive_type_entry * coq_premise list * coq_term list

and inductive_args = binders

and relation_args = coq_term list

and inferred_types = coq_term list 

and return_type = coq_term

and clause_entry = coq_term * coq_term 

and family_deftype = 
  | TypeAliasT of coq_term
  | InductiveT of inductive_type_entry list

and family_entry = ident * family_deftype

and coq_def = coq_def' phrase
and coq_def' =
  | TypeAliasD of (ident * binders * coq_term)
  | NotationD of (ident * coq_term)
  | RecordD of (ident * record_entry list)
  | InductiveD of (ident * inductive_args * inductive_type_entry list)
  | MutualRecD of coq_def list
  | DefinitionD of (ident * binders * return_type * clause_entry list)
  | InductiveRelationD of (ident * relation_args * relation_type_entry list)
  | AxiomD of (ident * binders * return_type)
  | InductiveFamilyD of (ident * family_entry list)
  | CoercionD of (func_name * ident * ident)
  | UnsupportedD of string
  
type coq_script = coq_def list