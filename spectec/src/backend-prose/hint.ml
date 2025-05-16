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
  { para_def  : text list list Map.t ref;
    proof_def : text list list Map.t ref;
  }

let new_env () =
  { para_def  = ref Map.empty;
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
  | DecH (id, hints) -> 
    env_hints "para" env.para_def id hints;
    env_hints "proof" env.proof_def id hints
  | _ -> ()

let env_def env d =
  match d.it with
  | HintD hd -> env_hintdef env hd
  | _ -> ()
