open Il.Ast
open Il.Print
open Coqast
open Util
open Source

module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"; "list"; "nat"] |> IdSet.of_list
let error at msg = Error.error at "Coq Generation" msg
let transform_id' (s : text) = match s with
  | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
  | s -> String.map (function
     | '.' -> '_'
     | '-' -> '_'
     | c -> c
     ) s

let transform_id (id : id) = transform_id' id.it

let transform_numtyp (typ : numtyp) = 
  match typ with
    | NatT -> T_type_basic T_nat
    | IntT -> T_type_basic T_int
    | RatT -> T_unsupported "rat"
    | RealT -> T_unsupported "real"

let transform_atom (a : atom) = 
  match a.it with
    | Atom s -> s
    | _ -> ""

let gen_typ_name (t : typ) =
  match t.it with
    | VarT (id, _) -> id.it
    | _ -> error t.at "Should not happen"


let transform_itertyp (it : iter) =
  match it with
    | Opt -> T_type_basic T_opt
    | List -> T_type_basic T_list
    | List1 | ListN _ -> T_unsupported ("(* Unsupported iter: " ^ string_of_iter it ^ "*)")
    
let rec transform_type (typ : typ) =
  match typ.it with
    | VarT (id, args) -> T_app (T_ident [transform_id id], List.map transform_arg args)
    | BoolT -> T_type_basic T_bool
    | NumT nt -> transform_numtyp nt
    | TextT -> T_type_basic T_string 
    | TupT [] -> T_type_basic T_unit
    | TupT typs -> T_tuple (List.map (fun (_, t) -> transform_type t) typs)
    | IterT (typ, iter) -> T_app (transform_itertyp iter, [transform_type typ])


and transform_exp (exp : exp) =
  match exp.it with 
    | VarE id -> T_ident [transform_id id]
    | BoolE b -> T_exp_basic (T_bool b)
    | NatE n -> T_exp_basic (T_nat n)
    | TextE txt -> T_exp_basic (T_string txt)
    | UnE (unop, exp) -> transform_unop unop exp
    | BinE (binop, exp1, exp2) -> T_app_infix (transform_binop binop, transform_exp exp1, transform_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> T_app_infix (transform_cmpop cmpop, transform_exp exp1, transform_exp exp2)
    | TupE _exps -> T_unsupported ""
    | ProjE (exp, n) -> T_app (T_exp_basic T_listlookup, [transform_exp exp; T_exp_basic (T_nat (Z.of_int n))])
    | CaseE (_mixop, _exp) -> T_unsupported ""
    | UncaseE (_exp, _mixop) -> T_unsupported ""
    | OptE (Some e) -> T_app (T_exp_basic T_some, [transform_exp e])
    | OptE None -> T_exp_basic T_none
    | TheE e -> T_app (T_exp_basic T_the, [transform_exp e])
    | StrE _expfields -> T_unsupported ""
    | DotE (e, atom) -> T_app (T_ident [gen_typ_name e.note; transform_atom atom], [transform_exp e])
    | CompE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | ListE exps -> T_list (List.map transform_exp exps)
    | LenE e -> T_app (T_exp_basic T_listlength, [transform_exp e])
    | CatE (exp1, exp2) -> T_app_infix (T_exp_basic T_concat, transform_exp exp1, transform_exp exp2)
    | IdxE (exp1, exp2) -> T_app (T_exp_basic T_listlookup, [transform_exp exp1; transform_exp exp2])
    | SliceE (exp1, exp2, exp3) -> T_app (T_exp_basic T_slicelookup, [transform_exp exp1; transform_exp exp2; transform_exp exp3])
    | UpdE (_exp1, _path, _exp2) -> T_unsupported ""
    | ExtE (_exp1, _path, _exp2) -> T_unsupported ""
    | CallE (id, args) -> T_app (T_ident [transform_id id], List.map transform_arg args)
    | IterE (_exp, _iterexp) -> T_unsupported ""
    | SubE (_e, _typ1, _typ2) -> T_unsupported ""

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
    | TypA typ -> transform_type typ

(* 
let transform_def (d : def) : coq_def =
  match d.it with
    | TypD (id, params, [{it = InstD (_binds, _args, deftyp);_}]) -> UnsupportedD ""
    | TypD (id, params, insts) -> UnsupportedD "" (* TODO FAMILY *)
    | RelD (id, mixop, typ, rules) -> UnsupportedD ""
    | DecD (id, params, typ, clauses) -> UnsupportedD ""
    | RecD defs -> UnsupportedD ""
    | _ -> UnsupportedD ""
let transform (il : script) : coq_script =
  List.map transform_def il *)