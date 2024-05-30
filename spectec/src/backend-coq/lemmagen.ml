open Print
open Coqast
open Util
open Source



let error_gen msg = Error.error no_region "Lemma generation" msg

let proof_admitted = "Proof.\nAdmitted" 
let _lemma_prefix = "_lemma"
let preservation_prefix = "_preserves"

let create_mapping (map : (name, coq_def) Hashtbl.t) (def : coq_def) : unit = 
  match def with
    | InductiveRelationD (id, _, _) -> Hashtbl.add map id def
    | _ -> ()


(* Hack for now, ideally would want the DSL source to tell us which rules we want to generate lemmas for. 
  This assumes step pure relations are of the form: instructions list i -> instructions list i'*)

let split_reduction (terms : coq_term list) = 
  match terms with
    | x :: y :: [] -> (string_of_terms x, string_of_terms y)
    | _ -> error_gen "Step reduction does not consist of one term reduction to another"
  


let lemma_gen_step_pure_preservation (relation_id_to_relation : (name, coq_def) Hashtbl.t) = 
  let relation = Hashtbl.find_opt relation_id_to_relation "Step_pure" in
  match relation with
    | Some InductiveRelationD (id, _, relation_entries) -> String.concat ".\n\n" (List.map (fun ((case_id, binds), _, end_terms) ->
      let (before_redux, after_redux) = split_reduction end_terms in
      let instr_ok_relation = "Admin_instrs_ok" in
      let function_type_var = "v_func_type" in 
      "Lemma " ^ case_id ^ preservation_prefix ^ " : forall v_S v_C " ^ string_of_binders binds ^ " " ^ function_type_var ^ ",\n\t" ^ 
      instr_ok_relation ^ " v_S v_C " ^ before_redux ^ " " ^ function_type_var ^ " ->\n\t" ^ 
      id ^ " " ^ before_redux ^ " " ^ after_redux ^ " ->\n\t" ^
      instr_ok_relation ^ " v_S v_C " ^ after_redux ^ " " ^ function_type_var ^ ".\n" ^ proof_admitted
    ) relation_entries) ^ ".\n\n"
    | _ -> ""
  

let lemma_gen (coq_ast : coq_script) : string =
  let relation_id_to_relation = Hashtbl.create 16 in
  List.iter (create_mapping relation_id_to_relation) coq_ast;
  lemma_gen_step_pure_preservation relation_id_to_relation