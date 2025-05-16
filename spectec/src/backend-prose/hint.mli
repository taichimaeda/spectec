open Il.Ast

module Map : Map.S

type env =
  { para_def  : text list list Map.t ref;
    proof_def : text list list Map.t ref;
  }

val bound : 'a Map.t -> id -> bool
val find : text -> 'a Map.t -> id -> 'a
val new_env : unit -> env
val env_def : env -> def -> unit
