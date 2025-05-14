open Il.Ast
open Util
open Source

(* This file handles the expression CaseE with the env map vars, 
   and the expression SubE with the env map subs.
*)

module Env = Map.Make(String)



type struct_type =
    | Record
    | Inductive
    | TypeAlias
    | Terminal (* nat, bool, list, etc.*)

(* MEMO: vars in environment maps syntax definition id 
         to the number of arguments needed to index this type family,
         struct_type is used to generate record append proof in print.ml
         id corresponds to the aliased type name on the right hand side
         for type alias, and the original type name for others *)
type var_typ = id * int * struct_type

(* MEMO: subs in environment maps syntax definition id 
         to a single case of variant type 
         mixop * typ corresponds to the notation type in each case
         id corresponds to the original type name 
         since only information on variant types is collected *)
type sub_typ = (id * mixop * typ) list

type env =
{ mutable vars : var_typ Env.t;
  mutable subs : sub_typ Env.t;
}

let new_env () =
{ vars = Env.empty;
  subs = Env.empty;
}

let error at msg = Error.error at "Coq Generation" msg

let _case_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> a
    | _ -> ""

(* MEMO: space is "Sub pass" or "Case"
         space seems to be unused except for debugging purposes *)
let find space env' id =
  match Env.find_opt id.it env' with
  | None -> error id.at ("undeclared " ^ space ^ " `" ^ id.it ^ "`")
  | Some t -> t

let string_of_struct_type (t : struct_type) = match t with
  | Record -> "Record"
  | Inductive -> "Inductive"
  | Terminal -> "Terminal"
  | TypeAlias -> "Type Alias"

let _print_env (env: env) = 
  Env.iter (fun id (n_id , num_args, str_typ) -> print_endline (
    "Type Alias(Key): " ^ id ^ "\n" ^
    "Actual Type: " ^ n_id.it ^ "\n" ^
    "Num Args: " ^ string_of_int num_args ^ "\n" ^
    "Struct Type: " ^ string_of_struct_type str_typ ^ "\n")) env.vars

(* MEMO: Environment is only updated via this helper function *)
let bind env' id t =
  if id = "_" then env' else
    Env.add id t env'

let case_typ (t : typ) = 
  match t.it with
    | VarT (id, _) -> (id, TypeAlias)
    | _ -> ("Terminal Type" $ t.at, Terminal)

let case_deftyp (id : id) (args : arg list) (e : env) (dtyp : deftyp) =
  match dtyp.it with
  | AliasT typ -> 
    let (n_id, s_t) = case_typ typ in 
    (* MEMO: This is a record update syntax *)
    (* MEMO: Collects number of arguments required to index this type family
             n_id is the right hand side of the equality which is assumed to be
             a single variable id  *)
    e.vars <- bind e.vars id.it (n_id, List.length args, s_t)
  | StructT _ -> 
    e.vars <- bind e.vars id.it (id, List.length args, Record)
  | VariantT typcases -> 
    e.vars <- bind e.vars id.it (id, List.length args, Inductive);
    (* MEMO: Collects each case expression in the variant
             Not supported in case_instance yet for simplicity? *)
    e.subs <- bind e.subs id.it (List.map (fun (m, (_, t, _), _) -> 
      (id, m, t)
      ) typcases)

let case_instance (e : env) (id : id) (params : param list) (i : inst) =
  match i.it with
    | InstD (_, _, deftyp) -> 
        (match deftyp.it with
      (* MEMO: These cases are exactly the same as case_deftyp
               except that e.subs is not updated *)
      | AliasT typ -> 
        let (n_id, s_t) = case_typ typ in
        e.vars <- bind e.vars id.it (n_id, List.length params, s_t)
      | VariantT _ -> 
        e.vars <- bind e.vars id.it (id, List.length params, Inductive)
      | _ -> ()
    )
let rec case_def (e : env) (d : def) = 
  match d.it with
    | (* MEMO: This type family contains a single instance *)
      TypD (id, _params, [{it = InstD (_binds, args, deftyp); _}]) -> case_deftyp id args e deftyp
    | (* MEMO: This type family contains multiple instances 
               indexed by arguments of the syntax definition *)
      TypD (id, params, insts) -> List.iter (case_instance e id params) insts
    | (* MEMO: RecD group mutually recursive defs *)
      RecD defs -> List.iter (case_def e) defs
    | _ -> ()
