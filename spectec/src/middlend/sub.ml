(*
This transformation
 * generates functions for all occurring subtype coercions
   (not yet: relies on hints so far)
 * uses these functions
   (not yet: done in the backend so far)
 * duplicates cases in functions as needed
   (not yet: $default_ rewritten in spec)
*)

open Util
open Source
open Il.Ast

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

let rec transform_def_rec env (def : def) : def * (def list) = match def.it with
  | RecD defs ->
    let defs', new_defs = List.split (List.map (transform_def_rec env) defs) in
    { def with it = RecD defs' },  List.concat new_defs
  | SynD (id, deftyp, hints) ->
    begin match deftyp.it with
    | VariantT cases ->
      register_cons env id cases;
      def,
      (* Also generate conversion functions *)
      let pairs =
        List.concat_map (fun {hintid; hintexp} ->
          (if hintid.it = "subtype" then List.map (fun s -> (id, s $ no_region)) hintexp else []) @
          (if hintid.it = "supertype" then List.map (fun s -> (s $ no_region, id)) hintexp else [])
        ) hints in
      List.map (fun (id, sid) ->
        let name = (id.it ^ "_" ^ sid.it) $ no_region in
        let ty = VarT id $ no_region in
        let sty = VarT sid $ no_region in
        let clauses = List.map (fun (a, arg_typ, _hints) ->
          if arg_typ.it = TupT []
          then DefD ([],
                CaseE (a, TupE [] $ no_region, sty) $ no_region,
                CaseE (a, TupE [] $ no_region, ty) $ no_region, []) $ no_region
          else
            let x = "x" $ no_region in
            DefD ([(x, arg_typ, [])],
                CaseE (a, VarE x $ no_region, sty) $ no_region,
                CaseE (a, VarE x $ no_region, ty) $ no_region, []) $ no_region
        ) (lookup_cons env sid) in
        DecD (name, VarT sid $ no_region, VarT id $ no_region, clauses, []) $ no_region
      ) pairs @
      List.concat_map (fun {hintid; hintexp} ->
        match hintid.it, hintexp with
        | "subtype_alias", [s1; s2] ->
          let id1 = s1 $ no_region in
          let id2 = s2 $ no_region in
          let name = (id.it ^ "_" ^ id1.it) $ no_region in
          let name2 = (id.it ^ "_" ^ id2.it) $ no_region in
          let x = "x" $ no_region in
          let clauses = [
            DefD ([(x, VarT id1 $ no_region, [])],
                  VarE x $ no_region,
                  CallE (name2, VarE x $ no_region) $ no_region, []) $ no_region
          ] in
          [ DecD (name, VarT id1 $ no_region, VarT id $ no_region, clauses, []) $ no_region ]
        | _, _ -> []
      ) hints
    | _ -> def, []
    end
  | _ ->
  def, [] (* TODO: look inside *)

and transform_def env (def : def) : def list =
  let def', new_defs = transform_def_rec env def in
  def' :: new_defs

let transform (defs : script) =
  let env = new_env () in
  List.concat_map (transform_def env) defs

