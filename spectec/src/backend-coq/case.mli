open Il.Ast

module Env : Map.S

type struct_type =
    | Record
    | Inductive
    | TypeAlias
    | Terminal (* nat, bool, list, etc.*)

type var_typ = id * int * struct_type
type sub_typ = (id * mixop * typ) list

type env =
{ mutable vars : var_typ Env.t;
    mutable subs : sub_typ Env.t
}

val find : text -> 'a Env.t -> id -> 'a
val new_env : unit -> env
val case_def : env -> def -> unit