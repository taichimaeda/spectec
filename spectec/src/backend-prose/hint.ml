open Il.Ast
open Util
open Source

module Set = Set.Make(String)
module Map = Map.Make(String)

let error at msg = Error.error at "prose generation" msg

let map_cons x y map =
  map := Map.update x
    (function None -> Some [y] | Some ys' -> Some (y::ys')) !map

type env =
  { desc_def  : text list list Map.t ref;
    desc_thm  : text list list Map.t ref;
    proof_def : text list list Map.t ref;
    prose_def  : text list list Map.t ref;
  }

let new_env () =
  { desc_def  = ref Map.empty;
    desc_thm  = ref Map.empty;
    prose_def  = ref Map.empty;
    proof_def = ref Map.empty;
  }

let bound env' id = Map.mem id.it env'

let find space env' id =
  match Map.find_opt id.it env' with
  | None -> error id.at ("undeclared hint " ^ space ^ " `" ^ id.it ^ "`")
  | Some t -> t

let env_hints name map id hints =
  List.iter (fun {hintid; hintexp} ->
    if hintid.it = name then map_cons id.it hintexp map
  ) hints

let env_hintdef env hd =
  match hd.it with
  | ThmH (id, hints) | LemH (id, hints) ->
    env_hints "desc" env.desc_thm id hints;
  | DecH (id, hints) -> 
    env_hints "desc" env.desc_def id hints;
    env_hints "proof" env.proof_def id hints;
    env_hints "prose" env.prose_def id hints
  | _ -> ()

let env_def env d =
  match d.it with
  | HintD hd -> env_hintdef env hd
  | _ -> ()
