open Il.Ast

module Env : Map.S

type inst_env = 
{ mutable cases : id Env.t
}

type var_typ = id * int * bool * typ option * inst_env option 

type env =
{ mutable vars : var_typ Env.t
}

val get_case_env : Il.Ast.script -> env
val print_env : env -> unit