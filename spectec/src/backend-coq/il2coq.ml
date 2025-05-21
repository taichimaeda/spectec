open Il.Ast
open Il.Print
open Coqast
open Util
open Source
open Case
open Either

(* Util functions for transform *)
module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"; "nat"] |> IdSet.of_list
let error at msg = Error.error at "coq generation" msg
let family_type_suffix = "entry"
let coerce_prefix = "coec_"
let var_prefix = "v_"
let func_prefix = "fun_"

let rec list_split (f : 'a -> bool) (l : 'a list) = match l with
  | [] -> ([], [])
  | x :: xs when f x -> let x_true, x_false = list_split f xs in
    (x :: x_true, x_false)
  | xs -> ([], xs)

let rec partition_eitherlist (xs : ('a, 'b) Either.t list) = 
  match xs with
    | [] -> ([], [])
    | (Left x) :: xs' -> let (lefts, rights) = partition_eitherlist xs' in
      (x :: lefts, rights)
    | Right x :: xs' -> let (lefts, rights) = partition_eitherlist xs' in
      (lefts, x :: rights)

(* Temporary workaround for fixing family matching (Only works for family types of one dependent type param) *)
let family_helper = Hashtbl.create 30

(* Case functions that handles case expressions and record appending*)
let caseenv_ref = ref (Case.new_env())

let hintenv_ref = ref (Hint.new_env())

let find_proof_hint id = 
  let env = !hintenv_ref in
  if not (Hint.bound !(env.proof_def) id) then None else
  let hints = Hint.find "definition" !(env.proof_def) id in
  let hexps = List.hd hints in
  Some (Lib.String.unquote (List.hd hexps))
  
(* MEMO: Returns the newly aliased type name for type alias
         and the number of parameters used in the syntax definition *)
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

(* MEMO: Used to retrieve the underlying struct_type of each field 
         in record defintion which is required to generate auxiliary lemmas later *)
let rec get_struct_type (env : env) (id : id) =
  let (n_id, _, struct_type) = find "Case" env.vars id in
  (match struct_type with 
    | TypeAlias -> get_struct_type env n_id
    | Inductive -> Inductive
    | Record -> Record
    | Terminal -> Terminal
  )

(* Id transformation *)
let transform_id' (s : text) = match s with
  | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
  | s -> String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
     ) s

let transform_id (id : id) = transform_id' id.it

let transform_var_id (id : id) = 
  (* TODO: (lemmagen) Double underscores are used for escaping subscript in Latex *)
  let id' = Lib.String.replace "__" "_" id.it in
  var_prefix ^ transform_id' id'

let transform_fun_id (id : id) = 
  let id' = Lib.String.replace "__" "_" id.it in
  func_prefix ^ transform_id' id'

(* TODO: (lemmagen) This is only used for theorems defined via proof hints on def *)
let transform_thm_id (id : id) =
  let id' = Lib.String.replace "__" "_" id.it in
  transform_id' id'

(* Identifier generation *)
let gen_typ_name (t : typ) =
  match t.it with
    | VarT (id, _) -> id.it
    | _ -> "" (* Not an issue if this happens *)
  
let get_typ_args (t : typ) = 
  match t.it with
    | VarT (_, args) -> args
    | _ -> []

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
        (* MEMO: exp.note denotes the type of the expressions exp in IL
                 See elab_exp in elab.ml for more details *)
        (* MEMO: Generates list of type names of expressions by traversing
                 case expressions and tuples *)
        | VarE _ -> [gen_typ_name exp.note]
        | CaseE (_, exp') -> gen_typ_name exp.note :: gen_argexp_name exp'
        | TupE tups -> List.concat_map gen_argexp_name tups
        | _ -> []
      ) in 
      gen_argexp_name e
    | TypA _ -> []
      
(* Family types infer function *)

(* MEMO: Type families are represented in Coq by inserting 
         a parent inductive type definition like val_ or unop_
         that groups the child inductive types which correspond to their instances *)
(* MEMO: Given type expression VarT (type_name, args),
         this function assumes only one of args is used for matching against the child inductive types
         although technically transform_inst uses all of args or binds *)
(* MEMO: Given type expression VarT (type_name, args),
         this function returns the name of the child inductive type that matches args *)
let infer_match_name (args : arg list) (type_name : text) =
  let rec infer_function lst =
    match lst with
      | [] -> None
      | l :: lst' -> let name = (type_name ^ "__" ^ l) in 
      if (Hashtbl.mem family_helper name) then Some name else infer_function lst'
    in
  let rec infer_match_name_from_args ags = 
    match ags with
      | [] -> None
      | (* MEMO: gen_arg_names a produces a list of type names
                 of all sub-expressions within the argument a *)
        a :: ags' -> let name_list = gen_arg_names a in
        (* MEMO: infer_function name_list finds the name of some sub-expression
                 which is registered in transform_inst as an instance of
                 type family named type_name *) 
        let inferred_name = infer_function name_list in
        if Option.is_none inferred_name 
          then infer_match_name_from_args ags' 
          else inferred_name
  in
  infer_match_name_from_args args 

(* MEMO: Given type expression VarT (type_name, args),
         this function returns the child inductive type that matches args 
         See infer_match_name for more details *)
let find_typ (args : arg list) (type_name : text) =
  let rec infer_function lst =
    match lst with
      | [] -> None
      | l :: lst' -> let name = (type_name ^ "__" ^ l) in 
      match (Hashtbl.find_opt family_helper name) with 
        | Some typ -> Some typ 
        | _ -> infer_function lst'
    in
  let rec infer_match_name_from_args ags = 
    match ags with
      | [] -> None
      | (* MEMO: gen_arg_names a produces a list of type names
                 of all sub-expressions within the argument a *)
        a :: ags' -> let name_list = gen_arg_names a in 
        (* MEMO: infer_function name_list finds the type of some sub-expression
                 whose name is registered in transform_inst as an instance of
                 type family named type_name *)
        let inferred_name = infer_function name_list in
        if Option.is_none inferred_name 
          then infer_match_name_from_args ags' 
          else inferred_name in
  infer_match_name_from_args args 

(* Atom functions *)
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
      (* MEMO: This ignores all special characters in mixop using is_atomid
               In other words only uppercase identifiers in the mixop are used *)
      fun atoms -> String.concat "" (List.map transform_atom (List.filter is_atomid atoms))) mixop
    )

(* Type functions *)

let is_terminal_type (typ : typ) =
  match typ.it with
    | VarT (_, args) -> args = [] 
    | (BoolT | NumT _ | TextT) -> true
    | _ -> false

let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_opt
    | List | List1 | ListN _ -> T_type_basic T_list

let transform_numtyp (typ : numtyp) = 
  match typ with
    | NatT -> T_type_basic T_nat
    | IntT -> T_type_basic T_nat
    | RatT -> T_type_basic T_nat (*T_unsupported "rat"*)
    | RealT -> T_type_basic T_nat (*T_unsupported "real"*)

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
    | BotT -> error typ.at "unexpected bottom type"

(* Erases the dependent type for inductive families *)
(* MEMO: This is the same as transform_type except that it erases the dependent indices
         when the indexed type family is covered by IL2Coq *)
(* MEMO: This seems like a workaround that skips monomorphisation 
         which would involve evaluation and unification of dependent indices *)
and erase_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, iter) -> T_app (transform_itertyp iter, [erase_dependent_type t])
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> erase_dependent_type t) typs)
    | (* MEMO: This is the base case for this function
               Skips dependent args in VarT if the type family is declared 
               with the id otherwise defaults to transform_type *)
      VarT (id, _) -> let inferred_opt = Hashtbl.mem family_helper (transform_id id) in      
      if inferred_opt then T_ident [transform_id id] else transform_type typ
    | _ -> transform_type typ

and check_family_dependent_type (typ : typ) = 
  match typ.it with
    | IterT (t, _iter) -> check_family_dependent_type t
    | TupT typs -> List.fold_left (fun acc (_, t) -> acc || check_family_dependent_type t) false typs
    | (* MEMO: This is the base case for this function
               Returns true if the type expression contains variables 
               that refer to a type family declaration or instance definition *)
      VarT (id, _) -> Hashtbl.mem family_helper (transform_id id)
    | _ -> false

(* TODO: (lemmagen) Refactor this function *)
and check_formula (exp : exp) = 
  let module Arg =
    struct
      include Il.Iter.Skip
      let flag = ref false
      let visit_exp exp' = 
        match exp'.it with
        | RuleE _ | ForallE _ | ExistsE _ -> flag := true
        | _ -> ()  
    end in
  let module Acc = Il.Iter.Make(Arg) in
  Acc.exp exp;
  !Arg.flag

and transform_return_type (typ : typ) =
  match typ.it with
    (* Only works for 1-dimensional lists. 
    (Which is fine since type coercing for higher dimensional lists is too much anyways)*)
    | IterT ({it = VarT (id, args); _}, iter) -> 
      let inferred_opt = Hashtbl.mem family_helper (transform_id id) in
      let str = if iter = Opt then "option" else "list" in 
      if inferred_opt 
      then T_ident [str; transform_id id] 
      else T_app (T_ident [str; transform_id id], List.map transform_arg args)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_return_type typ])
    | _ -> erase_dependent_type typ

and transform_typ_args (typ : typ) =
  match typ.it with
    | TupT [] -> []
    | TupT typs -> List.map (fun (e, t) -> (var_prefix ^ gen_exp_name e, erase_dependent_type t)) typs
    | _ -> [("_", erase_dependent_type typ)]

and remove_iter_typ (typ : typ) = 
  match typ.it with
    | IterT (typ, _) -> typ
    | _ -> typ

and transform_tuple_to_relation_args (t : typ) =
  match t.it with
    | TupT typs -> List.map (fun (_, t) -> erase_dependent_type t) typs
    | _ -> [erase_dependent_type t]

(* Expression functions *)
(* TODO: Resolve inconsistent variable names in patterns *)
and transform_exp (exp : exp) =
  match exp.it with 
    | VarE id -> 
      (* MEMO: Need to case occurrences of variable identifiers
               if the type of the variable is an instance of type family
               because dependent indices in all typ expressions are erased in this implementation *)
      if (Hashtbl.mem family_helper (gen_typ_name exp.note)) 
      then T_cast (T_ident [transform_var_id id], erase_dependent_type exp.note) 
      else T_ident [transform_var_id id]
    | BoolE b -> T_exp_basic (T_bool b)
    | NatE n -> T_exp_basic (T_nat n)
    | TextE txt -> T_exp_basic (T_string txt)
    | UnE (NotOp as unop, exp) -> T_app (transform_unop unop, [transform_exp exp])
    | UnE ((PlusOp _ | MinusOp _) as unop, exp) -> T_app_infix (transform_unop unop, T_exp_basic (T_nat Z.zero), transform_exp exp)
    | UnE ((MinusPlusOp _ | PlusMinusOp _) as unop, exp) -> T_app (transform_unop unop, [transform_exp exp])
    | BinE (binop, exp1, exp2) -> T_app_infix (transform_binop binop, transform_exp exp1, transform_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_exp exp1, transform_exp exp2)
    | TupE [] -> T_exp_basic T_exp_unit
    | TupE exps -> T_match (List.map transform_exp exps) 
    | ProjE (e, n) -> T_app (T_exp_basic T_listlookup, [transform_exp e; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (mixop, e) ->
      (* MEMO: exp.note denotes the type of the expression *)
      (* MEMO: num_args is required to supply enough arguments
               to the constructor of the inductive definition in Coq *)
      (* MEMO: actual_id is the name of the newly aliased type for type alias *)
      let actual_id, num_args = gen_case_name !caseenv_ref exp.note in 
      T_app (T_ident [transform_id actual_id; transform_mixop mixop], List.append (List.init num_args (fun _ -> T_ident ["_ "])) (transform_tuple_exp transform_exp e))
    | UncaseE (_e, _mixop) -> T_unsupported ("Uncase: " ^ string_of_exp exp)
    | OptE (Some e) -> T_app (T_exp_basic T_some, [transform_exp e])
    | OptE None -> T_exp_basic T_none
    | TheE e -> T_app (T_exp_basic T_the, [transform_exp e])
    | StrE expfields -> T_record_fields (List.map (fun (a, e) -> (gen_typ_name exp.note ^ "__" ^ transform_atom a, transform_exp e)) expfields)
    | DotE (e, atom) -> T_app (T_ident [gen_typ_name e.note; transform_atom atom], [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, [transform_exp e])
    | CatE (exp1, exp2) -> T_app (T_exp_basic T_listconcat, [T_ident ["_"] ;transform_exp exp1; transform_exp exp2])
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (exp1, path, exp2) -> T_update (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | ExtE (exp1, path, exp2) -> T_extend (transform_path_start path exp1, transform_exp exp1, transform_exp exp2)
    | CallE (id, args) -> T_app (T_ident [transform_fun_id id], List.map transform_arg args)
    | (* MEMO: iter is the iteration symbol like */?
               ids is the list of index variables and their type *)
      IterE (exp, (iter, ids)) ->  
        let exp1 = transform_exp exp in
        let t_iter = if iter = Opt then I_option else I_list in
        let iter_str = if iter = Opt then "option" else "list" in
        (match iter, ids, exp.it with
        | (* MEMO: If no variable in exp is being iterated 
                   then the iteration must be a singleton list *)
          (List | List1 | ListN _), [], _ -> T_list [exp1] 
        | (* TODO: Is this case properly handled? *)
          (List | List1 | ListN _ | Opt), _, (VarE _ | IterE _) -> exp1 
        | (* MEMO: The following cases assume IterE contains a single index variables *)
          (* TODO: name and T_ident are being used inconsistently
                   Ideally string manipulation logic like concatenation of identifiers with "__"
                   should only appear in print.ml not in this module *)
          (List | List1 | ListN _ | Opt), [(v, _)], (SubE ({it = VarE _; _}, typ1, typ2)) ->
            (* MEMO: This T_ident refers to the list or option coercion function *)
            T_app (T_ident [iter_str; gen_typ_name typ1; gen_typ_name typ2], [T_ident [transform_var_id v]])
        | (List | List1 | ListN _ | Opt), [(v, _)], (SubE (e, typ1, typ2)) -> 
            (* MEMO: This T_ident refers to the list or option coercion function *)
            (* MEMO: Need to map first unlike the previous case
                     because the expression e being subsumed is not a variable identifier *)
            T_app (T_ident [iter_str; gen_typ_name typ1; gen_typ_name typ2], [T_map (t_iter, transform_var_id v, transform_exp e)])
        | Opt, [(_, _)], OptE (Some e) -> T_app (T_exp_basic T_some, [transform_exp e])
        | (List | List1 | ListN _ | Opt), [(v, _)], _ -> T_map (t_iter, transform_var_id v, exp1)
        | (* MEMO: The rest of the cases assume IterE contains at most two index variables *)
          (List | List1 | ListN _ | Opt), [(v, _); (s, _)], _ -> T_zipwith (t_iter, transform_var_id v, transform_var_id s, transform_exp exp)
        | _ -> exp1
      ) 
    | SubE (e, _, typ2) -> T_cast (transform_exp e, transform_type typ2)
    | RuleE _ | ForallE _ | ExistsE _ -> 
      error exp.at "unexpected formula"
    | TmplE _ -> 
      error exp.at "unexpected template expression"


(* MEMO: This produces terms to be pattern matched against in match expressions
         which requires special handling in addition to transform_exp *)
and transform_match_exp (exp : exp) =
  match exp.it with
  | VarE id -> 
    (* MEMO: infer_match_name returns the name of the child inductive type
             which corresponds to the matching instance of the type family named id_transformed *)
    (* MEMO: If there is a match then we want to pattern match against the inner value instead *)
    (match (infer_match_name (get_typ_args exp.note) (gen_typ_name exp.note)) with
    | Some new_id -> T_app (T_ident [new_id; family_type_suffix], [T_ident [transform_var_id id]])
    (* TODO: (lemmagen) Cannot apply T_cast in match pattern unlike transform_exp *)
    | _ -> T_ident [transform_var_id id])
  | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_listmatch, transform_match_exp exp1, transform_match_exp exp2)
  | IterE (exp, _) -> transform_match_exp exp
  | ListE exps -> (match exps with
    | (* TODO: Should this be T_list [transform_match_exp e]? *)
      [e] -> transform_match_exp e
    | (* TODO: Does this handle inner occurrence of IterE etc in exp
               properly for pattern matching? *)
      _ -> transform_exp exp)
  | CaseE (m, e) -> 
    (* MEMO: infer_match_name returns the name of the child inductive type
             which corresponds to the matching instance of the type family named id_transformed *)
    (* MEMO: If there is a match then we want to pattern match against the inner value instead *)
    (match (infer_match_name (get_typ_args exp.note) (gen_typ_name exp.note)) with 
    | Some a -> T_app (T_ident [a; family_type_suffix], [T_app (T_ident [a; transform_mixop m], transform_tuple_exp transform_match_exp e)])
    | _ -> 
      (* TODO: (lemmagen) Duplicate of transform_exp *)
      let actual_id, num_args = gen_case_name !caseenv_ref exp.note in 
      T_app (T_ident [transform_id actual_id; transform_mixop m], List.append (List.init num_args (fun _ -> T_ident ["_ "])) (transform_tuple_exp transform_match_exp e)))
  | (* MEMO: Allows matching against the addition of natural numbers n1 + n2
             if n2 is a natural number literal
             Prepends successor constructor S of nat repeatedly n2 times *)
    BinE (AddOp _, exp1, {it = NatE n ;_}) -> let rec get_succ n = (match n with
    | 0 -> transform_match_exp exp1
    | m -> T_app (T_exp_basic T_succ, [get_succ (m - 1)])
  ) in get_succ (Z.to_int n)
  | _ -> transform_exp exp

and transform_tuple_exp (transform_func : exp -> coq_term) (exp : exp) = 
  match exp.it with
    | TupE exps -> List.map transform_func exps
    | _ -> [transform_func exp]

and transform_formula_exp (exp : exp) = 
  match exp.it with
    | UnE (NotOp as unop, exp) -> T_app (transform_formula_unop unop, [transform_formula_exp exp])
    | BinE (binop, exp1, exp2) -> T_app_infix (transform_formula_binop binop, transform_formula_exp exp1, transform_formula_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> T_app_infix (transform_formula_cmpop cmpop, transform_formula_exp exp1, transform_formula_exp exp2)
    | RuleE (id, _, e1) -> 
      T_rule (transform_id id, transform_tuple_exp transform_exp e1)
    | ForallE (bs, _, e1) -> 
      (* TODO: (lemmagen) Change transform_relation_bind to a more generic name *)
      T_forall (List.map transform_relation_bind bs, transform_formula_exp e1)
    | ExistsE (bs, _, e1) ->
      T_exists (List.map transform_relation_bind bs, transform_formula_exp e1)
    | _ -> transform_exp exp

(* This is mainly a hack to make it coerce correctly with list types (only 1d lists) *)
(* This could be extended for other list expressions (and option), but for 1.0 this is fine *)
and transform_return_exp (r_typ : typ option) (exp : exp) = 
  if check_formula exp then 
    transform_formula_exp exp
  else 
    match r_typ with
    | None -> transform_exp exp
    | Some typ -> (match exp.it with
      | ListE exps -> T_list (List.map (fun e -> T_cast ((transform_exp e), erase_dependent_type (remove_iter_typ typ))) exps)
      | OptE (Some e) -> T_app (T_exp_basic T_some, [T_cast (transform_exp e, erase_dependent_type (remove_iter_typ typ))])
      | _ -> transform_exp exp
    )

and transform_unop (u : unop)= 
  match u with
    | NotOp -> T_exp_basic T_not
    | PlusOp _ -> T_exp_basic T_add
    | MinusOp _ -> T_exp_basic T_sub
    | MinusPlusOp _ -> T_exp_basic T_minusplus
    | PlusMinusOp _ -> T_exp_basic T_plusminus

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
    | ModOp _ -> T_exp_basic T_mod

and transform_cmpop (c : cmpop) =
  match c with
    | EqOp -> T_exp_basic T_eq
    | NeOp -> T_exp_basic T_neq
    | LtOp _ -> T_exp_basic T_lt
    | GtOp _ -> T_exp_basic T_gt
    | LeOp _ -> T_exp_basic T_le
    | GeOp _ -> T_exp_basic T_ge

and transform_formula_unop (u : unop) = 
  match u with
    | NotOp ->  T_exp_basic T_not_prop
    | _ -> transform_unop u

and transform_formula_binop (b : binop) = 
  match b with
    | AndOp -> T_exp_basic T_and_prop
    | OrOp -> T_exp_basic T_or_prop
    | ImplOp -> T_exp_basic T_impl_prop
    | EquivOp -> T_exp_basic T_equiv_prop
    | _ -> transform_binop b

and transform_formula_cmpop (c : cmpop) =
  match c with
    | EqOp -> T_exp_basic T_eq_prop
    | NeOp -> T_exp_basic T_neq_prop
    | _ -> transform_cmpop c

(* Binds, args, and params functions *)
and transform_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_exp exp
    | TypA typ -> erase_dependent_type typ

and transform_match_arg (arg : arg) =
  match arg.it with
    | ExpA exp -> transform_match_exp exp
    | (* MEMO: Cannot match against types in function definition in Coq *)
      TypA _ -> T_ident ["_"]

and transform_bind (bind : bind) =
  match bind.it with
    | (* MEMO: This ignores iter list because it suffices for Wasm 1.0? *)
      ExpB (id, typ, _) -> (transform_var_id id, erase_dependent_type typ)
    | TypB id -> (transform_id id, T_ident ["Type"])

(* MEMO: This returns binders in Coq IL for each bind in IL *)
and transform_relation_bind (bind : bind) =
  let rec transform_iter_bind iters typ = (match iters with
    | [] -> typ
    | it :: its -> IterT (transform_iter_bind its typ, it) $ typ.at
  ) in
  match bind.it with
    | ExpB (id, ({it = VarT (t_id, args); _} as t), its) -> 
      let id_transformed = transform_id t_id in 
      (* MEMO: find_typ returns the child inductive type
               which corresponds to the matching instance of the type family named id_transformed *)
      (* MEMO: If there is a match then we use the child inductive type
               otherwise we need to erase the dependent indices *)
      let a = find_typ args id_transformed in
        (transform_var_id id, (match a with
          | Some typ -> transform_type (transform_iter_bind (List.rev its) typ)
          | None -> erase_dependent_type (transform_iter_bind (List.rev its) t)
        ))
    | (* MEMO: This is the case where typ is not a VarT *)
      ExpB (id, typ, its) -> 
      (transform_var_id id, erase_dependent_type (transform_iter_bind (List.rev its) typ))
    | TypB id -> (transform_var_id id, T_ident ["Type"])

and transform_param (arg : int * param) =
  let (n, p) = arg in 
  match p.it with
    | ExpP (id, typ) -> 
      (transform_var_id id ^ "_" ^ string_of_int n, erase_dependent_type typ)
    | TypP id -> transform_id id, T_ident ["Type"]

(* PATH Functions *)

(* MEMO: This flattens a nested path construct into a list of paths
         which facilitates transform_path_start *)
and transform_list_path (p : path) = 
  match p.it with   
    | RootP -> []
    | IdxP (p', e') -> (IdxP (p', e') $$ (p.at, p.note)) :: transform_list_path p'
    | SliceP (p', _exp1, _exp2) -> (SliceP (p', _exp1, _exp2) $$ (p.at, p.note)) :: transform_list_path p'
    | DotP (p', a) -> (DotP (p', a) $$ (p.at, p.note)) :: transform_list_path p'

and gen_path_var_id (exp : exp) = 
  match exp.it with
    | VarE id -> Some (transform_var_id id)
    | _ -> None

(* TODO Improve this handling for the case of two listlookups in a row *)
(* MEMO: This is the helper function for transform_path_start *)
(* MEMO: n denotes the recursion depth which starts with 0
         name is Some id if the expression indexed by these paths is a variable identifier
         otherwise it is None *)
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
      (* MEMO: Takes all dot paths until non-dot path is encountered
               Generates a list of record lookup function names for this path fragment *)
      let (dot_paths, rest) = list_split is_dot paths in
      let projection_list = List.map (fun p -> match p.it with 
        | (* MEMO: p.note denotes the type of the struct type field *)
          DotP (p, a) -> gen_typ_name p.note ^ "__" ^ transform_atom a
        | _ -> "" (* Should not happen *)
      ) dot_paths in
      (* MEMO: var_prefix ^ string_of_int n is the parameter name of the continuation function
               that binds to the expression being indexed by this path fragment *)
      P_recordlookup (projection_list, var_prefix ^ string_of_int n) 
      (* MEMO: name passed to the next recursive call of transform_path is
               an expression that looks up the record by projection_list functions
               which is used by list_name (n - 1) in the next cases of IdxP and SliceP
               Note that P_listlookup and P_sliceupdate uses list_update and list_slice_update
               not the continuation functions like P_recordlookup *)
      (* TODO: This is tightly coupled with the printing logic of paths
               which makes this implementation very confusing *)
        :: transform_path rest (n + 1) (Some (String.concat " " projection_list ^ " " ^ list_name n))
    | {it = IdxP (_p', idx_exp); _} :: ps ->  P_listlookup (list_name (n - 1), transform_exp idx_exp) :: transform_path ps n None
    | {it = SliceP (_p', e1, e2); _} :: _ps -> [P_sliceupdate (list_name (n - 1), transform_exp e1, transform_exp e2)]
    | _ -> []

(* MEMO: This is the entrypoint function for path expressions *)
and transform_path_start (p : path) (start_name : exp) = 
  (* MEMO: Flattens the nested path p into a list
           and reverses the list to place the innermost path at the head *)
  let paths = List.rev (transform_list_path p) in
  match paths with
    | [] -> error p.at "Path should not be empty"
    | _ -> transform_path paths 0 (gen_path_var_id start_name)

(* Premises *)
let rec transform_premise (p : prem) =
  match p.it with
    | (* MEMO: This boolean expression is printed as a Coq term literally
               which gets coerced by is_true *)
      IfPr exp -> P_if (transform_formula_exp exp)
    | (* MEMO: P_else is handled by else removal pass later *)
      ElsePr -> P_else
    | LetPr (exp1, exp2, _) -> P_if (T_app_infix (T_exp_basic T_eq, transform_exp exp1, transform_exp exp2))
    | (* MEMO: This corresponds to iteration of premises over variables
               listed in id_types *)
      IterPr (p, (iter, id_types)) -> let t_iter = if iter = Opt then I_option else I_list in
      P_listforall (t_iter, transform_premise p, List.map (fun (i, _typ) -> transform_var_id i) id_types)
    | (* MEMO: This corresponds to premises invoking another relation *)
      RulePr (id, _mixop, exp) -> P_rule (transform_id id, transform_tuple_exp transform_exp exp)

let transform_deftyp (id : id) (binds : bind list) (deftyp : deftyp) =
  match deftyp.it with
    | (* MEMO: Type alias to terminal type is printed with Notation rather than Definition *)
      AliasT typ -> if is_terminal_type typ
        then NotationD (transform_id id, transform_type typ) 
        else TypeAliasD (transform_id id, List.map transform_bind binds, erase_dependent_type typ)
    | (* MEMO: Struct types are printed with Record *)
      StructT typfields -> RecordD (transform_id id, List.map (fun (a, (_, t, _), _) -> 
      (transform_id id ^ "__" ^ transform_atom a, erase_dependent_type t, Option.map (get_struct_type !caseenv_ref) (get_typ_name t))
      ) typfields)
    | (* MEMO: Variant types are printed with Inductive *)
      VariantT typcases -> InductiveD (transform_id id, List.map transform_bind binds, List.map (fun (m, (_, t, _), _) ->
        (transform_id id ^ "__" ^ transform_mixop m, transform_typ_args t)) typcases)

(* MEMO: This returns relation_type_entry in Coq IL for each rule in IL *)
let transform_rule (id : id) (r : rule) = 
  match r.it with
    | RuleD (rule_id, binds, mixop, exp, premises) -> 
      ((transform_id id ^ "__" ^ transform_id rule_id ^ transform_mixop mixop, List.map transform_relation_bind binds), 
      List.map transform_premise premises, transform_tuple_exp transform_exp exp)

(* MEMO: This returns clause_entry in Coq IL for each clause in IL *)
let transform_clause (return_type : typ option) (c : clause) =
  match c.it with
    | DefD (_binds, args, exp, _prems) -> (T_match (List.map transform_match_arg args), transform_return_exp return_type exp)

let transform_inst (id : id) (i : inst) =
  match i.it with
    | InstD (binds, _, deftyp) -> 
      let id_transformed = transform_id id in 
      let name = id_transformed ^ "__" ^ String.concat "__" (List.map gen_bind_name binds) in    
      (* MEMO: family_helper is only updated for transform_inst not transform_deftyp *)
      (* MEMO: Registers the syntax definition id
               to indicate that the type family is declared *)
      Hashtbl.add family_helper id_transformed (VarT (id, []) $ i.at); (* Putting a dummy value as memcheck is only needed*)
      (name, (match deftyp.it with
      | AliasT typ -> 
        (* MEMO: Registers the underlying type for type alias
                 to indicate that this instance of the type family is defined *)
        Hashtbl.add family_helper name typ;
        TypeAliasT (erase_dependent_type typ)
      | (* MEMO: Record types cannot take any parameters *)
        StructT _ -> error i.at "Family of records should not exist" (* This should never occur *)
      | VariantT typcases -> 
        (* MEMO: Registers a dummy value for variant type
                 to indicate that this instance of the type family is defined *)
        Hashtbl.add family_helper name (VarT (id, []) $ i.at); (* Putting a dummy value as memcheck is only needed*)
        (* MEMO: Defines constructors of inductive type definition in Coq
                 Only uses mixop and ignores type tuple in the notation type *)
        InductiveT (List.map (fun (m, (case_binds, _, _), _) -> (name ^ "__" ^ transform_mixop m, List.map transform_bind case_binds)) typcases))
    )

let transform_defthm (style : text) (d : def) = 
  match d.it with
  | DecD (id, params, _, clauses) -> 
    if params <> [] then 
      error d.at "theorem takes no arguments";
    if List.length clauses <> 1 then
      error d.at "theorem takes exactly one clause";
    let clause = List.hd clauses in
    let DefD (bs, _, _, _) = clause.it in
    let _as, ret = transform_clause None clause in
    (match style with
    | "theorem" -> TheoremD (transform_thm_id id, List.map transform_bind bs, ret)
    | "lemma" -> LemmaD (transform_thm_id id, List.map transform_bind bs, ret)
    | _ -> error d.at "unsupported theorem style")
  | _ -> assert false

let rec transform_def (d : def) : coq_def =
  (match d.it with
    | TypD (id, _, [{it = InstD (binds, _, deftyp);_}]) -> transform_deftyp id binds deftyp 
    | (* MEMO: Each instance in InductiveFamilyD 
               results in a single inductive type definition with the exception of type aliases *)
      TypD (id, _, insts) -> InductiveFamilyD (transform_id id, List.map (transform_inst id) insts)
    | (* MEMO: Relations are defined in terms of notation type
               typ is a tuple of types to be interspersed in the mixop which is ignored here *)
      RelD (id, _, typ, rules) -> InductiveRelationD (transform_id id, transform_tuple_to_relation_args typ, List.map (transform_rule id) rules)
    | DecD (id, params, typ, clauses) -> 
      let hint = find_proof_hint id in
      (match hint with
      | Some style ->
        transform_defthm style d
      | None when clauses = [] ->
        let binds = List.map transform_param (List.combine (List.init (List.length params) (fun i -> i)) params) in 
        AxiomD (transform_fun_id id, binds, transform_return_type typ)
      | None ->
        let binds = List.map transform_param (List.combine (List.init (List.length params) (fun i -> i)) params) in 
        let family_type_exists = List.fold_left (fun acc param -> acc || (match param.it with
          | ExpP (_, typ') -> check_family_dependent_type typ'
          | TypP _ -> false 
        )) false params in
        let new_clause = if family_type_exists then [(T_ident ["_"], T_ident ["default_val"])] else [] in
        let return_type = 
          let DefD (_, _, exp, _) = (List.hd clauses).it in
          if check_formula exp then T_type_basic T_prop else
          if check_family_dependent_type typ then transform_return_type typ else erase_dependent_type typ in 
        let base_return_type = if check_family_dependent_type typ then Some typ else None in 
        DefinitionD (transform_fun_id id, binds, return_type, (List.map (transform_clause base_return_type) clauses) @ new_clause)
      )
    | RecD defs -> MutualRecD (List.map transform_def defs)
    | ThmD (id, bs, e1) -> 
      TheoremD (transform_id id, List.map transform_relation_bind bs, transform_formula_exp e1)
    | LemD (id, bs, e1) -> 
      LemmaD (transform_id id, List.map transform_relation_bind bs, transform_formula_exp e1)
    | TmplD _ ->
      error d.at "unexpected template definition"
    | HintD _ -> UnsupportedD "") $ d.at

let is_not_hintdef (d : def) : bool =
  match d.it with
    | HintD _ -> false
    | _ -> true 

(* -------------- Sub pass ----------------- *)

let sub_hastable = Hashtbl.create 16

let rec get_sube_exp (exp : exp) =
  match exp.it with
    | UnE (_, e) -> get_sube_exp e
    | BinE (_, e1, e2) | CmpE (_, e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | TupE exps -> List.concat_map get_sube_exp exps
    | ProjE (e, _) -> get_sube_exp e
    | CaseE (_, e) -> get_sube_exp e
    | UncaseE (e, _) -> get_sube_exp e
    | OptE (Some e) -> get_sube_exp e
    | TheE e -> get_sube_exp e
    | StrE expfields -> List.concat_map (fun (_, e) -> get_sube_exp e) expfields
    | DotE (e, _) -> get_sube_exp e
    | CompE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ListE exps -> List.concat_map get_sube_exp exps 
    | LenE e -> get_sube_exp e
    | CatE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | IdxE (e1, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | SliceE (e1, e2, e3) -> List.concat_map get_sube_exp [e1; e2; e3]
    | UpdE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | ExtE (e1, _, e2) -> List.append (get_sube_exp e1) (get_sube_exp e2)
    | CallE (_, args) -> List.concat_map get_sube_arg args
    | IterE (e, _) -> get_sube_exp e
    (* MEMO: This seems like the only base case in get_sube_* functions *)
    (* MEMO: Collects subsumption expressions in the IL *)
    | SubE _ as e -> [e $$ (exp.at, exp.note)]
    | _ -> []

and get_sube_arg (arg : arg) = 
  match arg.it with
    | ExpA e -> get_sube_exp e
    | TypA _ -> []

let rec get_sube_prem (premise : prem) =
  match premise.it with
    | RulePr (_, _, e) -> get_sube_exp e
    | IfPr e -> get_sube_exp e
    | IterPr (p, _) -> get_sube_prem p
    | _ -> []

let get_sube_rule (r : rule) =
  match r.it with
    | RuleD (_, _, _, e, prems) -> List.append (get_sube_exp e) (List.concat_map get_sube_prem prems)

let is_id_type (typ : typ) = 
  match typ.it with
    | VarT (_, args) -> args = []
    | _ -> false

let gen_typ_id (t : typ) =
  match t.it with
    | VarT (id, _) -> id
    | _ -> "" $ t.at

let rec is_same_type (t1 : typ) (t2 : typ) =
  match (t1.it, t2.it) with
    | VarT (id1, _), VarT (id2, _) -> id1.it = id2.it
    | NumT nt1, NumT nt2 -> nt1 = nt2
    | BoolT, BoolT -> true
    | TextT, TextT -> true
    | TupT tups, TupT tups2 -> (List.length tups) = (List.length tups2) && List.for_all2 (fun (_, t1') (_, t2') -> is_same_type t1' t2') tups tups2
    | IterT (t1', iter1), IterT (t2', iter2) -> iter1 = iter2 && is_same_type t1' t2'
    | _ -> false

(* Assumes that tuple variables will be in same order, can be modified if necessary *)
(* TODO must also check if some types inside the type are subtyppable and as such it should also be allowed *)
let rec find_same_typing (at : region) (m1 : ident) (t1 : typ) (t2_cases : sub_typ) =
  match t2_cases with
    | [] -> None
    (* MEMO: Finds case expression in t2 variant type
             whose type and mixop matches the given case expression in t1 variant type *)
    | (_, m2, t2) as s_t :: _ when is_same_type t1 t2 && m1 = (transform_mixop m2) -> Some s_t
    | _ :: t2_cases' -> find_same_typing at m1 t1 t2_cases'

let get_num_tuple_typ (t : typ) = 
  match t.it with
    | TupT tups -> List.length tups 
    | _ -> 0

(* MEMO: Produces additional Coq constructs to model subtyping in Right *)
let transform_sub_types (at : region) (t1_id : id) (t2_id : id) (t1_cases : sub_typ) (t2_cases : sub_typ) =
  (* MEMO: Creates coercion function name *)
  let func_name = func_prefix ^ coerce_prefix ^ transform_id t1_id ^ "__" ^ transform_id t2_id in 
  (* MEMO: Defines function for the coercion *)
  [Right (DefinitionD (func_name, 
    (* MEMO: Defines argument name and its type of this function *)
    [(var_prefix ^ transform_id t1_id, T_ident [transform_id t1_id])],
    (* MEMO: Defines return type of this function *)
    T_ident [transform_id t2_id],
    (* MEMO: Defines clauses of this function *)
    List.map (fun (id, m1, t1) ->
      let s_t = find_same_typing at (transform_mixop m1) t1 t2_cases in
      match s_t with
        | Some (id2, m2, _) ->
          let var_list = List.init (get_num_tuple_typ t1) (fun i -> T_ident [var_prefix ^ string_of_int i]) in
          (* MEMO: Supplies elements of clause_entry list *)
          (* MEMO: Pattern matches on t1 constructor and re-constructs by corresponding t2 constructor *)
          (T_app (T_ident [transform_id id; transform_mixop m1], var_list),
          T_app (T_ident [transform_id id2; transform_mixop m2], var_list))
        | None -> (T_ident [""], T_ident [""])
    ) t1_cases) $ at  ); 
  (* MEMO: Registers the above function as coercion function *)
  Right (CoercionD (func_name, transform_id t1_id, transform_id t2_id) $ at )]

(* TODO can be extended to other defs if necessary *)
(* MEMO: Produces additional Coq constructs to model subtyping in Right *)
(* MEMO: This returns list of either def in IL or coq_def in Coq IL for each def in IL
         coq_def is prepended to the list if extra Coq constructs are generated *)
let rec transform_sub_def (d : def) = 
  match d.it with
    | RelD (_, _, _, rules) -> 
      (* MEMO: First get subsumption expressions from rules *)
      (* MEMO: Subtyping constructs are only generated for those that appear in 
               the subsumption expression for now *)
      let sub_expressions = List.concat_map get_sube_rule rules in
      List.append (List.concat_map (fun e -> match e.it with 
        | SubE (_, t1, t2) when is_id_type t1 && is_id_type t2 -> 
          let (t1_id, t2_id) = (gen_typ_id t1, gen_typ_id t2) in
          let combined_name = (t1_id.it ^ "__" ^ t2_id.it) in 
          (* MEMO: For each subsumption from type t1 to type t2,
                   if subsumption is not yet visited or registered in sub_hastable
                   then add additional construct by transform_sub_types *)
          if (Hashtbl.mem sub_hastable combined_name) then []
          else (
            (* MEMO: Looks up sub_typ values for each type from the environment *)
            (* MEMO: sub_typ contains a list of case expressions for that syntax definition
                     which corresponds to the constructors of the equivalent inductive type in Coq *)
            let env = !caseenv_ref in
            let typ1_cases = find "Sub pass" env.subs t1_id in
            let typ2_cases = find "Sub pass" env.subs t2_id in
            Hashtbl.add sub_hastable combined_name combined_name;
            transform_sub_types d.at t1_id t2_id typ1_cases typ2_cases)
        | _ -> []) sub_expressions) [Left d]
    | RecD defs -> let flat_list = List.concat_map transform_sub_def defs in
      let (defs, coq_defs) = partition_eitherlist flat_list in
      (* TODO: Why not just @ [Left d]? *)
      (List.map Either.right coq_defs) @ [Left (RecD defs $ d.at)]
    | _ -> [Left d]

let transform_sub (il : script) =
  List.concat_map transform_sub_def il

(* Main transformation function *)
let transform (il : script) : coq_script = 
  List.iter (Case.case_def !caseenv_ref) il;
  List.iter (Hint.env_def !hintenv_ref) il;
  let sub_transformed = transform_sub il in
  (* MEMO: Right stores additional Coq constructs produced by the subpass
           Left stores original IL constructs to be transformed by the main pass *)
  (* TODO: Why not just append the additional Coq constructs from the subpass? *)
  List.filter_map (fun d -> 
    match d with 
      (* MEMO: Skip the main pass if it is a standalone hint definition *)
      | Left def when is_not_hintdef def -> Some (transform_def def)
      | Right c_def -> Some c_def
      | _ -> None
  ) sub_transformed

