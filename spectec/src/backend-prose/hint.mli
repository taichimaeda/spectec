open Il.Ast

module Map : Map.S

type env =
  { desc_def  : text list list Map.t ref;
    desc_thm  : text list list Map.t ref;
    proof_def : text list list Map.t ref;
    prose_def : text list list Map.t ref;
  }

val bound : 'a Map.t -> id -> bool
val find : text -> 'a Map.t -> id -> 'a
val new_env : unit -> env
val env_def : env -> def -> unit
