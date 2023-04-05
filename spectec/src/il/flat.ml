(*
This transformation
 * replaces variant extension with copies of the constructors
 * generates functions for all occurring subtype coercions
 * uses these functions
 * duplicates cases in functions as needed
*)

open Util
open Source
open Ast

(* Errors *)

let error at msg = Source.error at "type" msg

(* Environment *)

module Env = Map.Make(String)

type env =
  { mutable variants : typcase list Env.t;
    mutable needed_pairs : (id * id) list;
    mutable available_pairs : (id * id) list;
  }

let new_env () : env =
  { variants = Env.empty;
    needed_pairs = [];
    available_pairs = [];
  }

let lookup_cons (env : env) (id : id) =
  match Env.find_opt id.it env.variants with
  | None -> error id.at ("undeclared variant `" ^ id.it ^ "`")
  | Some t -> t

let register_cons (env : env) (id :id) (cases : typcase list) =
  if Env.mem id.it env.variants then
    error id.at ("duplicate declaration for variant `" ^ id.it ^ "`")
  else
    env.variants <- Env.add id.it cases env.variants

let rec transform_def env (def : def) : def = match def.it with
  | RecD defs ->
    { def with it = RecD (List.map (transform_def env) defs) }
  | SynD (id, deftyp, hints) ->
    begin match deftyp.it with
    | VariantT (ids, cases) ->
      let cases' = List.concat_map (lookup_cons env) ids @ cases in
      register_cons env id cases';
      { def with it = SynD (id, { deftyp with it = VariantT ([], cases') }, hints) }
    | _ -> def
    end
  (* Giving up on this translation
  | DecD  (id, ty1, ty2, clauses, hints) -> 
    let clauses' = List.concat_map (fun clause ->
      match clause.it with
      | DefD ([(id1, ty1, [])],
              {it = SubE ({it = VarE id2} as ide, ty2, ty3)} as lhs,
              rhs, []) when id1.it = id2.it and Eq.eq_typ t1 t2 ->
        (* This clause has to be duplicated *)
        (* Lets assume nullary constructors only *)
        List.map (fun con ->
          { clause with it = DefD ([], { lhs with it = CaseE (con, 
   *)
  | _ ->  
  def (* TODO: look inside *)

let transform (defs : script) =
  let env = new_env () in
  List.map (transform_def env) defs

