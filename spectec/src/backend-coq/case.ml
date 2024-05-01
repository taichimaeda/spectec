open Il.Ast
open Util
open Source


module Env = Map.Make(String)

type inst_env = 
{ mutable cases : id Env.t
}

type var_typ = id * int * bool * typ option * inst_env option 

type env =
{ mutable vars : var_typ Env.t
}

let new_env () =
{ vars = Env.empty;
}

let new_inst_env () =
{ cases = Env.empty;
}

let error at msg = Error.error at "Coq Generation" msg


let case_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> a
    | _ -> ""


let find space env' id =
  match Env.find_opt id.it env' with
  | None -> error id.at ("undeclared " ^ space ^ " `" ^ id.it ^ "`")
  | Some t -> t

let string_of_option_typ (typ : typ option) =
  match typ with
    | Some a -> Il.Print.string_of_typ a
    | None -> "None"

let print_env (env: env) = 
  Env.iter (fun id (n_id , num_args, is_inductive, typ, _inst_env) -> print_endline (
    "Type Alias(Key): " ^ id ^ "\n" ^
    "Actual Type: " ^ n_id.it ^ "\n" ^
    "Num Args: " ^ string_of_int num_args ^ "\n" ^
    "Type: " ^ string_of_option_typ typ ^ "\n" ^
    "Is Inductive Type?: " ^ string_of_bool is_inductive ^ "\n")) env.vars

let bind env' id t =
  if id = "_" then env' else
    Env.add id t env'

let rec case_typ (t : typ) = 
  match t.it with
    | VarT (id, args) -> (id, List.length args)
    | IterT (typ, _) -> case_typ typ
    | _ -> ("Terminal Type" $ t.at, 0)

let case_exp (e : exp) = 
  match e.it with
    | VarE id -> (id, 0)
    | _ -> ("" $ e.at, 0)
let case_arg (a : arg) = 
  match a.it with
    | ExpA e -> case_exp e
    | TypA t -> case_typ t

let case_deftyp (id : id) (args : arg list) (e : env) (dtyp : deftyp) =
  match dtyp.it with
  | AliasT typ -> 
    let next_id, num_args = case_typ typ in 
    e.vars <- bind e.vars id.it (next_id, num_args, false, Some typ, None)
  | StructT _ -> ()
  | VariantT _ -> 
    e.vars <- bind e.vars id.it (id, List.length args, true, None, None)

let case_instance (e : env) (inst_env : inst_env) (id : id) (params : param list) (i : inst) =
  match i.it with
    | InstD (_, args, deftyp) -> 
        (match deftyp.it with
      | VariantT typcases -> List.iter (fun (m, _, _) -> 
        List.iter (fun arg -> 
          let n_id, _ = case_arg arg in
          (inst_env.cases <- bind inst_env.cases (case_mixop m) n_id)) args) typcases;
          e.vars <- bind e.vars id.it (id, List.length params, true, None, Some inst_env)
      | _ -> ()
    )
let rec case_def (e : env) (d : def) = 
  match d.it with
    | TypD (id, _params, [{it = InstD (_binds, args, deftyp); _}]) -> case_deftyp id args e deftyp
    | TypD (id, params, insts) -> let inst_env = new_inst_env () in
    List.iter (case_instance e inst_env id params) insts
    | RecD defs -> List.iter (case_def e) defs
    | _ -> ()

let get_case_env (il : script) =
  let env = new_env () in 
  List.iter (case_def env) il;
  env