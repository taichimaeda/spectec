open Il.Ast

module Env : Map.S

type struct_type =
    | Record
    | Inductive
    | TypeAlias
    | Terminal (* nat, bool, list, etc.*)

type var_typ = id * int * struct_type

type env =
{ mutable vars : var_typ Env.t
}

val get_case_env : Il.Ast.script -> env
val print_env : env -> unit
val find : text -> 'a Env.t -> id -> 'a
val string_of_struct_type : struct_type -> text
val new_env : unit -> env