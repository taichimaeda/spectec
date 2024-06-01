open Print
open Coqast
open Util
open Source



let error_gen msg = Error.error no_region "Lemma generation" msg

let proof_admitted = "Proof.\nAdmitted" 
let _lemma_prefix = "_lemma"
let preservation_prefix = "_preserves"
let instr_ok_relation = "Admin_instrs_ok"
let module_inst_relation = "Module_instance_ok"
let step_pure_relation = "Step_pure"
let step_read_relation = "Step_read"
let function_type_var = "v_func_type"
let inst_var = "v_minst"

let create_mapping (map : (name, coq_def) Hashtbl.t) (def : coq_def) : unit = 
  match def with
    | InductiveRelationD (id, _, _) -> Hashtbl.add map id def
    | _ -> ()
  
let get_inductive_relation (def : coq_def) = 
  match def with
    | InductiveRelationD (id, args, entries) -> (id, args, entries)
    | _ -> error_gen "Not a inductive relation"


(* Hack for now, ideally would want the DSL source to tell us which rules we want to generate lemmas for. 
  This assumes step pure relations are of the form: instructions list i -> instructions list i'*)

let split_config_reduction (term : coq_term list) =
  match term with
    | (T_app (_, [T_ident [_]; v_ais]) as x) :: y :: [] -> (string_of_terms v_ais, string_of_terms x, string_of_terms y)
    | _ -> error_gen "Cannot split config correctly"
let split_reduction (terms : coq_term list) = 
  match terms with
    | x :: y :: [] -> (string_of_terms x, string_of_terms y)
    | _ -> error_gen "Step reduction does not consist of one term reduction to another"
  


let lemma_gen_step_pure_preservation (relation_id_to_relation : (name, coq_def) Hashtbl.t) = 
  let (_, _, relation_entries) = get_inductive_relation (Hashtbl.find relation_id_to_relation step_pure_relation) in
  String.concat ".\n\n" (List.map (fun ((case_id, binds), premises, end_terms) ->
    let (before_redux, after_redux) = split_reduction end_terms in
    let premises_gen = if premises <> [] then String.concat " ->\n\t" (List.map string_of_premise premises) ^ " ->\n\t" else "" in
    "Lemma " ^ case_id ^ preservation_prefix ^ " : forall v_S v_C " ^ string_of_binders binds ^ " " ^ function_type_var ^ ",\n\t" ^ 
    instr_ok_relation ^ " v_S v_C " ^ before_redux ^ " " ^ function_type_var ^ " ->\n\t" ^ 
    premises_gen ^
    instr_ok_relation ^ " v_S v_C " ^ after_redux ^ " " ^ function_type_var ^ ".\n" ^ proof_admitted
  ) relation_entries) ^ ".\n\n"


let lemma_gen_step_read_preservation (relation_id_to_relation : (name, coq_def) Hashtbl.t) = 
  let (_, _, relation_entries) = get_inductive_relation (Hashtbl.find relation_id_to_relation step_read_relation) in
  String.concat ".\n\n" (List.map (fun ((case_id, binds), premises, end_terms) ->
    let (instrs, _, after_redux) = split_config_reduction end_terms in
    let premises_gen = if premises <> [] then String.concat " ->\n\t" (List.map string_of_premise premises) ^ " ->\n\t" else "" in
    "Lemma " ^ case_id ^ preservation_prefix ^ " : forall v_S v_F v_C " ^ string_of_binders binds ^ " " ^ function_type_var ^ " " ^ inst_var ^ ",\n\t" ^ 
    instr_ok_relation ^ " v_S v_C " ^ instrs ^ " " ^ function_type_var ^ " ->\n\t" ^ 
    module_inst_relation ^ " v_S " ^ inst_var ^ " v_C ->\n\t" ^
    "v_z = state__ v_S v_F ->\n\t" ^
    premises_gen ^
    instr_ok_relation ^ " v_S v_C " ^ after_redux ^ " " ^ function_type_var ^ ".\n" ^ 
    proof_admitted
  ) relation_entries) ^ ".\n\n"
  

let lemma_gen (coq_ast : coq_script) : string =
  let relation_id_to_relation = Hashtbl.create 16 in
  List.iter (create_mapping relation_id_to_relation) coq_ast;
  lemma_gen_step_pure_preservation relation_id_to_relation ^ 
  lemma_gen_step_read_preservation relation_id_to_relation