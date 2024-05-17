open Il.Ast
open Il.Print
open Coqast
open Util
open Source
open Case

(* Util functions for transform *)
module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"; "nat"] |> IdSet.of_list
let error at msg = Error.error at "Coq Generation" msg
let family_type_suffix = "entry"

let rec list_split (f : 'a -> bool) (l : 'a list) = match l with
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

(* Temporary workaround for fixing family matching (Only works for family types of one dependent type param) *)
let family_helper = Hashtbl.create 30

(* Case functions that handles case expressions and record appending*)
let env_ref = ref (Case.new_env())

let rec get_actual_case_name (env : env) (id : id) =
  let (n_id, num_args, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> let actual_id, final_args = get_actual_case_name env n_id in
    (actual_id, num_args + final_args)
    | Inductive -> (n_id, num_args)
    | _ -> error id.at "Should be a Variant type or type alias"
  )

let gen_case_name (env : env) (t : typ) =
  match t.it with
    | VarT (id, _) -> get_actual_case_name env id
    | _ -> error t.at "Should not happen"

let rec get_struct_type (env : env) (id : id) =
  let (n_id, _, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> get_struct_type env n_id
    | Inductive -> Inductive
    | Record -> Record
    | Terminal -> Terminal
  )

let var_prefix = "v_"
let func_prefix = "fun_"

let transform_id' (s : text) = match s with
  | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
  | s -> String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
     ) s

let transform_id (id : id) = transform_id' id.it

let transform_var_id (id : id) = var_prefix ^ transform_id' id.it

let transform_fun_id (id : id) = func_prefix ^ transform_id' id.it 

let transform_numtyp (typ : numtyp) = 
  match typ with
    | NatT -> T_type_basic T_nat
    | IntT -> T_type_basic T_nat
    | RatT -> T_type_basic T_nat (*T_unsupported "rat"*)
    | RealT -> T_type_basic T_nat (*T_unsupported "real"*)

let gen_typ_name (t : typ) =
  match t.it with
    | VarT (id, _) -> id.it
    | _ -> "" (* This should never happen (FIXME raise an actual error) *)

let gen_exp_name (e : exp) =
  match e.it with
    | VarE id -> id.it
    | _ -> "_" 

let get_typ_name (t : typ) = 
  match t.it with
    | VarT (id, _) -> Some id
    | _ -> None

let gen_bind_name (bind : bind) =
  match bind.it with
    | ExpB (id, _, _) -> transform_id id
    | TypB id -> transform_id id
    
let gen_arg_names (arg : arg) = 
  match arg.it with
    | ExpA e -> let rec gen_argexp_name exp = 
      (match exp.it with
        | CaseE (_, exp') -> gen_typ_name exp.note :: gen_argexp_name exp'
        | TupE tups -> List.concat_map gen_argexp_name tups
        | _ -> []
      ) in 
      gen_argexp_name e
    | TypA _ -> []
      
let infer_match_name (args : arg list) (binds: bind list) (type_name : text) =
  let rec infer_function lst =
    match lst with
      | [] -> None
      | l :: lst' -> (match (Hashtbl.find_opt family_helper (type_name ^ "__" ^ l)) with
      | Some a -> Some a
      | None -> infer_function lst'
    ) in

  let infer_match_name_from_binds bs = infer_function (List.map gen_bind_name bs) in
  let rec infer_match_name_from_args ags = 
    match ags with
      | [] -> None
      | a :: ags' -> let name_list = gen_arg_names a in 
        let inferred_name = infer_function name_list in
        if Option.is_none inferred_name 
          then infer_match_name_from_args ags' 
          else inferred_name
  in
  let result = infer_match_name_from_binds binds in
  if Option.is_none result 
    then infer_match_name_from_args args 
    else result


let is_terminal_type (typ : typ) =
  match typ.it with
    | VarT (_, args) -> args = [] 
    | (BoolT | NumT _ | TextT) -> true
    | _ -> false

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> transform_id' s
    | _ -> ""
let is_atomid (a : atom) =
  match a.it with
    | Atom _ -> true
    | _ -> false

let transform_mixop (m : mixop) = match m with
  | [{it = Atom a; _}] :: tail when List.for_all ((=) []) tail -> transform_id' a
  | mixop -> String.concat "" (List.map (
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_list (*T_opt*)
    | List | List1 | ListN _ -> T_type_basic T_list

let rec transform_type (typ : typ) =
  match typ.it with
    | VarT (id, []) -> T_ident [transform_id id]
    | VarT (id, args) -> T_app (T_ident [transform_id id], List.map transform_arg args)
    | BoolT -> T_type_basic T_bool
    | NumT nt -> transform_numtyp nt
    | TextT -> T_type_basic T_string 
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> transform_type t) typs)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_type typ])

(* Erases the dependent type for inductive families *)
and erase_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, iter) -> T_app (transform_itertyp iter, [erase_dependent_type t])
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> erase_dependent_type t) typs)
    | VarT (id, _) -> let inferred_opt = Hashtbl.find_opt family_helper (transform_id id) in      
      (match inferred_opt with 
        | Some family_id' -> T_ident [family_id']
        | _ -> transform_type typ
      )
    | _ -> transform_type typ

and check_family_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, _iter) -> check_family_dependent_type t
    | TupT typs -> List.fold_left (fun acc (_, t) -> acc || check_family_dependent_type t) false typs
    | VarT (id, _) -> Hashtbl.mem family_helper (transform_id id)
    | _ -> false

and transform_return_type (typ : typ) =
  match typ.it with
    (* Only works for 1-dimensional lists. (Which is fine since type coercing for higher dimensional lists is too much anyways)*)
    | IterT ({it = VarT (id, args); _}, _) -> 
      let inferred_opt = Hashtbl.find_opt family_helper (transform_id id) in      
      (match inferred_opt with 
        | Some family_id' -> T_ident ["list"; family_id'] 
        | _ -> T_app (T_ident ["list"; transform_id id], List.map transform_arg args)
      )
    | _ -> erase_dependent_type typ

and transform_typ_args (typ : typ) =
  match typ.it with
    | TupT [] -> []
    | TupT typs -> List.map (fun (e, t) -> (var_prefix ^ gen_exp_name e, erase_dependent_type t)) typs
    | _ -> [("_", erase_dependent_type typ)]


and gen_var_id (exp : exp) = 
  match exp.it with
    | VarE id -> transform_var_id id
    | _ -> error exp.at "Path start does not have an identifier as starter"

and transform_exp (exp : exp) =
  match exp.it with 
    | VarE id -> T_ident [transform_var_id id]
    | BoolE b -> T_exp_basic (T_bool b)
    | NatE n -> T_exp_basic (T_nat n)
    | TextE txt -> T_exp_basic (T_string txt)
    | UnE (unop, exp) -> transform_unop unop exp
    | BinE (binop, exp1, exp2) -> T_app_infix (transform_binop binop, transform_exp exp1, transform_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_exp exp1, transform_exp exp2)
    | TupE exps -> T_exp_tuple (List.map transform_exp exps) 
    | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, [transform_exp e; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (mixop, e) -> let actual_id, num_args = gen_case_name !env_ref exp.note in 
      T_app (T_ident [transform_id actual_id; transform_mixop mixop], List.append (List.init num_args (fun _ -> T_ident ["_ "])) [transform_exp e])
    | UncaseE (_e, _mixop) -> T_unsupported ("Uncase: " ^ string_of_exp exp)
    | OptE (Some e) -> T_list [transform_exp e] (*T_app (T_exp_basic T_some, [transform_exp e])*)
    | OptE None -> T_list [] (*T_exp_basic T_none*)
    | TheE e -> T_app (T_exp_basic T_the, [transform_exp e])
    | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (gen_typ_name exp.note ^ "__" ^ transform_atom a, transform_exp e)) expfields)
    | DotE (e, atom) -> T_app (T_ident [gen_typ_name e.note; transform_atom atom], [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, [transform_exp e])
    | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (exp1, path, exp2) -> T_update (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | ExtE (exp1, path, exp2) -> T_extend (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | CallE (id, args) -> T_app (T_ident [transform_fun_id id], List.map transform_arg args)
    | IterE (exp, (iter, ids)) ->  
        let exp1 = transform_exp exp in
        (match iter, ids, exp.it with
        | (List | List1 | ListN _), [], _ -> T_list [exp1] 
        | (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
        | (List | List1 | ListN _ | Opt), [(v, _)], _ -> T_listmap (transform_var_id v, exp1)
        | (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ -> T_listzipwith (transform_var_id v, transform_var_id s, transform_tuple_exp exp)
        | _ -> exp1
      ) 
    | SubE (e, _typ1, _typ2) -> transform_exp e

and transform_match_exp (args : arg list) (binds : bind list) (exp : exp) =
  match exp.it with
  | VarE id -> 
    (match (infer_match_name args binds (gen_typ_name exp.note)) with
    | Some new_id -> T_app (T_ident [new_id; family_type_suffix], [T_ident [transform_var_id id]])
    | _ -> transform_exp exp
  )
  | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listmatch, transform_match_exp args binds exp1, transform_match_exp args binds exp2)
  | IterE (exp, _) -> transform_match_exp args binds exp
  | ListE exps -> (match exps with
    | [e] -> transform_match_exp args binds e
    | _ -> transform_exp exp
  )
  | CaseE (m, e) -> (match (infer_match_name args binds (gen_typ_name exp.note)) with 
    | Some a -> T_app (T_ident [a; family_type_suffix], [T_app (T_ident [a; transform_mixop m], [transform_match_exp args binds e])])
    | _ -> transform_exp exp
  )
  | BinE (AddOp _, exp1, {it = NatE n ;_}) -> let rec get_succ n = (match n with
    | 0 -> transform_match_exp args binds exp1
    | m -> T_app (T_exp_basic T_succ, [get_succ (m - 1)])
  ) in get_succ (Z.to_int n)
  | _ -> transform_exp exp

and transform_tuple_exp (exp : exp) = 
  match exp.it with
    | TupE exps -> T_match (List.map transform_tuple_exp exps)
    | _ -> transform_exp exp 

and transform_unop (u : unop) (exp : exp) = 
  match u with
    | NotOp ->  T_app (T_exp_basic T_sub, [transform_exp exp])
    | PlusOp _ -> T_app_infix (T_exp_basic T_add, T_exp_basic (T_nat Z.zero), transform_exp exp)
    | MinusOp _ -> T_app_infix (T_exp_basic T_sub, T_exp_basic (T_nat Z.zero), transform_exp exp)
    | MinusPlusOp _ -> T_app (T_exp_basic T_minusplus, [transform_exp exp])
    | PlusMinusOp _ -> T_app (T_exp_basic T_plusminus, [transform_exp exp])

and transform_binop (b : binop) = 
  match b with
    | AndOp -> T_exp_basic T_and
    | OrOp -> T_exp_basic T_or
    | ImplOp -> T_exp_basic T_impl
    | EquivOp -> T_exp_basic T_equiv
    | AddOp _ -> T_exp_basic T_add
    | SubOp _ -> T_exp_basic T_sub
    | MulOp _ -> T_exp_basic T_mul
    | DivOp _ -> T_exp_basic T_div
    | ExpOp _ -> T_exp_basic T_exp

and transform_cmpop (c : cmpop) =
  match c with
    | EqOp -> T_exp_basic T_eq
    | NeOp -> T_exp_basic T_neq
    | LtOp _ -> T_exp_basic T_lt
    | GtOp _ -> T_exp_basic T_gt
    | LeOp _ -> T_exp_basic T_le
    | GeOp _ -> T_exp_basic T_ge
      
and transform_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_exp exp
    | TypA typ -> erase_dependent_type typ

and transform_match_arg (args : arg list) (binds : bind list) (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_match_exp args binds exp
    | TypA _ -> T_ident ["_"]

and transform_bind (bind : bind) =
  match bind.it with
    | ExpB (id, typ, _) -> (transform_var_id id, erase_dependent_type typ)
    | TypB id -> (transform_id id, T_ident ["Type"])

and transform_relation_bind (bind : bind) =
  match bind.it with
    | ExpB (id, typ, its) -> 
      let rec transform_iter_bind iters = (match iters with
      | [] -> typ
      | it :: its -> IterT (transform_iter_bind its, it) $ typ.at
    ) in
      (transform_var_id id, erase_dependent_type (transform_iter_bind its))
    | TypB id -> (transform_var_id id, T_ident ["Type"])

and transform_list_path (p : path) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', e') -> (IdxP (p', e') $$ (p.at, p.note)) :: transform_list_path p'
    | SliceP (p', _exp1, _exp2) -> (SliceP (p', _exp1, _exp2) $$ (p.at, p.note)) :: transform_list_path p'
    | DotP (p', a) -> (DotP (p', a) $$ (p.at, p.note)) :: transform_list_path p'

(* TODO: Improve this handling for the case of two listlookups in a row *)
and transform_path (paths : path list) (n : int) (name : string option) = 
  let list_name num = (match name with
    | Some id -> id
    | None -> var_prefix ^ string_of_int num
  ) in
  match paths with
    | {it = DotP _; _} :: _ -> 
      let is_dot p = (match p.it with
        | DotP _ -> true
        | _ -> false 
      ) in
      let (dot_paths, rest) = list_split is_dot paths in 
      let projection_list = List.map (fun p -> match p.it with 
        | DotP (p, a) -> gen_typ_name p.note ^ "__" ^ transform_atom a
        | _ -> "" (* Should not happen *)
      ) dot_paths in
      P_recordlookup (projection_list, var_prefix ^ string_of_int n) :: transform_path rest (n + 1) (Some (String.concat " " projection_list ^ " " ^ list_name n))
    | {it = IdxP (_p', idx_exp); _} :: ps ->  P_listlookup (list_name (n - 1), transform_exp idx_exp) :: transform_path ps n None
    | {it = SliceP (_p', e1, e2); _} :: _ps -> [P_sliceupdate (list_name (n - 1), transform_exp e1, transform_exp e2)]
    | _ -> []

and transform_path_start (p : path) (start_name : exp) = 
  let paths = List.rev (transform_list_path p) in
  match paths with
    | [] -> error p.at "Path should not be empty"
    | _ -> transform_path paths 0 (Some (gen_var_id start_name))

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
    | AliasT typ -> if is_terminal_type typ then NotationD (transform_id id, transform_type typ) 
    else TypeAliasD (transform_id id, List.map transform_bind binds, erase_dependent_type typ)
    | StructT typfields -> RecordD (transform_id id, List.map (fun (a, (_, t, _), _) -> 
      (transform_id id ^ "__" ^ transform_atom a, erase_dependent_type t, Option.map (get_struct_type !env_ref) (get_typ_name t))
      ) typfields)
    | VariantT typcases -> InductiveD (transform_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
        (transform_id id ^ "__" ^ transform_mixop m, transform_typ_args t)) typcases)

let transform_tuple_to_relation_args (t : typ) =
  match t.it with
    | TupT typs -> List.map (fun (_, t) -> erase_dependent_type t) typs
    | _ -> [erase_dependent_type t]

let rec transform_premise (p : prem) =
  match p.it with
    | IfPr exp -> P_if (transform_exp exp)
    | ElsePr -> P_else
    | LetPr _ -> P_unsupported ("LetPr: " ^ string_of_prem p)
    | IterPr (p, (_iter, id_types)) -> P_listforall (transform_premise p, List.map (fun (i, _typ) -> transform_var_id i) id_types)
    | RulePr (id, _mixop, exp) -> P_rule (transform_id id, transform_exp exp)

let transform_rule (id : id) (r : rule) = 
  match r.it with
    | RuleD (rule_id, binds, mixop, exp, premises) -> 
      ((transform_id id ^ "__" ^ transform_id rule_id ^ transform_mixop mixop, List.map transform_relation_bind binds), 
      List.map transform_premise premises, transform_exp exp)

let transform_clause (c : clause) =
  match c.it with
    | DefD (binds, args, exp, _prems) -> (T_match (List.map (transform_match_arg args binds) args), transform_tuple_exp exp)

let transform_param (p : param) =
  match p.it with
    | ExpP (id, typ) -> (transform_var_id id, erase_dependent_type typ)
    | TypP id -> transform_id id, T_ident ["Type"]
  
let transform_inst (id : id) (i : inst) =
  match i.it with
    | InstD (binds, _, deftyp) -> 
      let id_transformed = transform_id id in 
      let name = id_transformed ^ "__" ^ String.concat "__" (List.map gen_bind_name binds) in    
      Hashtbl.add family_helper id_transformed id_transformed;
      Hashtbl.add family_helper name name;
      (name, (match deftyp.it with
      | AliasT typ -> 
        TypeAliasT (erase_dependent_type typ)
      | StructT _ -> assert false
      | VariantT typcases -> 
        InductiveT (List.map (fun (m, (case_binds, _, _), _) -> (name ^ "__" ^ transform_mixop m, List.map transform_bind case_binds)) typcases))
    )

let rec transform_def (d : def) : coq_def =
  match d.it with
    | TypD (id, _, [{it = InstD (binds, _, deftyp);_}]) -> transform_deftyp id binds deftyp
    | TypD (id, _, insts) -> InductiveFamilyD (transform_id id, List.map (transform_inst id) insts)
    | RelD (id, _, typ, rules) -> InductiveRelationD (transform_id id, transform_tuple_to_relation_args typ, List.map (transform_rule id) rules)
    | DecD (id, params, typ, clauses) -> let binds = List.map transform_param params in 
      if (clauses == []) 
        then AxiomD (transform_fun_id id, binds, transform_return_type typ)
      else (
        let family_type_exists = List.fold_left (fun acc param -> acc || (match param.it with
          | ExpP (_, typ) -> check_family_dependent_type typ
          | TypP _ -> false 
        )) false params in
        let new_clause = if family_type_exists then [(T_ident ["_"], T_ident ["default_val"])] else [] in
        let return_type = if family_type_exists then transform_return_type typ else erase_dependent_type typ in 
        DefinitionD (transform_fun_id id, binds, return_type, List.append (List.map transform_clause clauses) new_clause)
      )
    | RecD defs -> MutualRecD (List.map transform_def defs)
    | HintD _ -> UnsupportedD ""

let is_not_hintdef (d : def) : bool =
  match d.it with
    | HintD _ -> false
    | _ -> true 

let transform (il : script) : coq_script =
  env_ref := Case.get_case_env il;
  List.map transform_def (List.filter is_not_hintdef il)