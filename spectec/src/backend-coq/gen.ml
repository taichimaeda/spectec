open Il.Ast
open Translate
open Util.Source

module CoqAst = Ast
module IdSet = Set.Make(String)

let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"

(* Hack for now for mixops, anonymous names with be a *)
let reserved_mixop_name = "a"

(* Function prefix *)
let func = "fun_"

let _gen_atom (a : CoqAst.atom) = Il.Atom.string_of_atom a
let gen_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> a
    | _ -> reserved_mixop_name

let rec _gen_exp_id_used (e : CoqAst.exp) =
  match e.it with
    | VarE id -> [id.it] |> IdSet.of_list
    | UnE (_op, exp) -> _gen_exp_id_used exp
    | BinE (_binop, exp1, exp2) -> IdSet.union (_gen_exp_id_used exp1) (_gen_exp_id_used exp2)
    | CmpE (_cmpop, exp1, exp2) -> IdSet.union (_gen_exp_id_used exp1) (_gen_exp_id_used exp2)
    | SliceE (exp1, exp2, exp3) -> IdSet.union (_gen_exp_id_used exp1) (IdSet.union (_gen_exp_id_used exp2) (_gen_exp_id_used exp3))
    | UpdE (exp, _path, exp2) -> IdSet.union (_gen_exp_id_used exp) (_gen_exp_id_used exp2)
    | ExtE (exp1, _path, exp2) -> IdSet.union (_gen_exp_id_used exp1) (_gen_exp_id_used exp2)
    | StrE expfields -> List.fold_left IdSet.union IdSet.empty (List.map (fun (_, e) -> _gen_exp_id_used e) expfields)
    | DotE (exp, _atom) -> _gen_exp_id_used exp  
    | CompE (exp1, exp2) -> IdSet.union (_gen_exp_id_used exp1) (_gen_exp_id_used exp2)       
    | TupE exps -> List.fold_left IdSet.union IdSet.empty (List.map _gen_exp_id_used exps)     
    | MixE (_mixop, exp) -> _gen_exp_id_used exp       
    | CallE (id, _args) -> [id.it] |> IdSet.of_list
    | IterE (exp, (_iter, _ids)) -> _gen_exp_id_used exp 
    | OptE (Some exp) -> _gen_exp_id_used exp  
    | TheE exp -> _gen_exp_id_used exp             
    | ListE exps -> List.fold_left IdSet.union IdSet.empty (List.map _gen_exp_id_used exps)          
    | CatE (exp1, exp2) -> IdSet.union (_gen_exp_id_used exp1) (_gen_exp_id_used exp2)    
    | CaseE (_mixop, exp) -> _gen_exp_id_used exp     
    | SubE (exp, _typ1, _typ2) -> _gen_exp_id_used exp
    | ProjE (exp, _n) -> _gen_exp_id_used exp
    | UncaseE (exp, _mixop) -> _gen_exp_id_used exp
    | LenE exp -> _gen_exp_id_used exp
    | _ -> IdSet.empty

let gen_iter (it : CoqAst.iter) =
  match it with
    | Opt -> "option"
    | List -> "list"
    | List1 -> "list"
    | ListN (_exp, _id) -> "list"



let gen_binop (b : CoqAst.binop) =
  match b with
    | AndOp -> " /\\ "
    | OrOp -> " \\/ "
    | AddOp -> " + "
    | SubOp -> " - "
    | ImplOp -> " -> "
    | MulOp -> " * "
    | DivOp -> " / "
    | ExpOp -> " ^ "
    | EquivOp -> " <-> "

let gen_unop (u : CoqAst.unop) =
  match u with
    | NotOp -> "~"
    | PlusOp -> ""
    | MinusOp -> "0 - "
    | PlusMinusOp -> "0 - "
    | MinusPlusOp -> "0 - "

let gen_cmpop (c : CoqAst.cmpop) =
  match c with
    | EqOp -> " = "
    | NeOp -> " <> "
    | LtOp -> " < "
    | GtOp -> " > "
    | LeOp -> " <= "
    | GeOp -> " >= "

let rec gen_exp (e : CoqAst.exp) =
  match e.it with
    | VarE id -> id.it
    | BoolE true -> "true"
    | BoolE false -> "false"
    | NatE nat -> Z.to_string nat
    | TextE text -> text
    | UnE (op, exp) ->  parens (gen_unop op ^ (gen_exp exp))
    | BinE (binop, exp1, exp2) -> parens (gen_exp exp1 ^ gen_binop binop ^ gen_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> parens (gen_exp exp1 ^ gen_cmpop cmpop ^ gen_exp exp2)
    | SliceE (_exp1, _exp2, _exp3) -> ""
    | UpdE (_exp, _path, _exp2) -> ""
    | ExtE (_exp1, _path, _exp2) -> ""
    | StrE _expfields -> ""       
    | DotE (_exp, _atom) -> ""   
    | CompE (_exp, _exp2) -> ""             
    | TupE _exps -> ""       
    | MixE (_mixop, _exp) -> ""        
    | CallE (id, args) -> func ^ id.it ^ gen_call_args args
    | IterE (exp, (_iter, _ids)) -> gen_exp exp  
    | OptE None -> "None"
    | OptE (Some exp) -> "Some " ^ gen_exp exp  
    | TheE exp -> gen_exp exp              
    | ListE _exps -> ""           
    | LenE exp -> "List.length(" ^ gen_exp exp ^ ")"
    | CatE (exp1, exp2) -> parens (gen_exp exp1 ^ " ++ " ^ gen_exp exp2)   
    | IdxE (exp1, exp2) -> "lookup_total(" ^ gen_exp exp1 ^ ", " ^ gen_exp exp2 ^ ")"  (* TODO: Haven't created lookup_total correctly yet*)
    | CaseE (mixop, exp) -> parens (gen_mixop mixop ^ " ++ " ^ gen_exp exp)      
    | SubE (exp, _typ1, _typ2) -> gen_exp exp
    | ProjE (_exp, _n) -> ""
    | UncaseE (_exp, _mixop) -> ""

and gen_typ (t: CoqAst.typ) =
  match t.it with
    | VarT (id, args) -> id.it ^ (gen_call_args args)
    | NatT -> "nat"
    | TextT -> "string"
    | BoolT -> "bool"
    | TupT typs -> String.concat " * " (List.map (fun (e, t) -> parens (gen_exp e ^ " : " ^ gen_typ t)) typs)
    | IterT (typ, iter) -> gen_iter iter ^ " " ^ gen_typ typ

and gen_typ_args (t : CoqAst.typ) =
  match t.it with
    | TupT typs -> String.concat " " (List.map (fun (e, t) -> parens (gen_exp e ^ " : " ^ gen_typ t)) typs)
    | _ -> parens (gen_typ t)

and gen_arg (a: CoqAst.arg) =
  match a.it with
    | ExpA exp -> let e = gen_exp exp in parens (e ^ " : " ^ e)
    | TypA typ -> curly_parens (gen_typ typ)

and gen_args (args: CoqAst.arg list) =
  match args with
    | [] -> ""
    | _ -> String.concat " " (List.map gen_arg args)

and gen_call_args (args: CoqAst.arg list) =
  match args with
  | [] -> ""
  | _ -> String.concat " " (List.map (fun x -> parens (gen_arg_name x)) args)

and gen_arg_name (a : CoqAst.arg) = 
  match a.it with
    | ExpA exp -> gen_exp exp
    | _ -> ""

and gen_match_args (args : CoqAst.arg list) = 
  match args with
    | [] -> ""
    | _ -> String.concat ", " (List.map (fun x -> gen_arg_name x) args)

(* and gen_path (p : CoqAst.path) =
  match p.it with   
    | RootP -> ""
    | IdxP (_path, _exp) -> ""
    | SliceP (path, exp1, exp2) -> ""
    | DotP (path, atom) -> ""*)




let gen_premises (p : CoqAst.premise) =
  match p.it with
    | IfPr exp -> gen_exp exp
    | _ -> ""

let gen_variant_premises (premises : CoqAst.premise list) (id : CoqAst.id) =
  let e = (match premises with
    | [] -> ""
    | _ -> " -> ") in
  String.concat " /\\ " (List.map gen_premises premises) ^ e ^ id.it

(* let gen_definition_premises (premises : CoqAst.premise list) =
  let prefix = (match premises with
  | [] -> ""
  | _ -> " when ") in
  String.concat " /\\ "  *)
(* 
let gen_inhabitance_proof (type_id : id) (typcases : CoqAst.typcase list) : string =
  "Global Instance Inhabited_" ^ type_id.it ^ " : Inhabited " ^ type_id.it ^ " := \n" ^
  "{default_val := {|\n" ^
    String.concat "" (List.map (fun (m, (_ty, _prems)) -> 
      "  " ^ type_id.it ^ "__" ^ gen_mixop m ^ " := default_val ;\n"
      ) typcases) ^ "|} }" *)

let gen_param (p : CoqAst.param) = 
  match p.it with
    | ExpP (id, typ) -> parens (id.it ^ " : " ^ gen_typ typ)
    | TypP id -> curly_parens id.it

let gen_deftyp (args : CoqAst.arg list) (id : CoqAst.id) (d : CoqAst.deftyp) =
  match d.it with
    | AliasT typ -> "Definition " ^ id.it ^ gen_args args ^  " := " ^ gen_typ typ
    | StructT _typfields -> ""
    | VariantT typcases -> 
    let arg_names = match args with 
      | [] -> "" 
      | _ -> " " ^ String.concat " " (List.map gen_arg_name args)
    in 
    "Inductive " ^ id.it ^ " " ^ gen_args args ^  " : Type :=\n" ^ 
    String.concat "\n" (List.map (fun (m, (t, premises)) -> 
    "\t| " ^ id.it ^ "__" ^ gen_mixop m ^ gen_typ_args t ^ ": " ^ gen_variant_premises premises id
    ^ arg_names) typcases)

let gen_instances (_id : CoqAst.id) (i : CoqAst.inst) =
  match i.it with
    | InstD (_args, deftyp) -> (match deftyp.it with
      | AliasT _typ -> ""
      | StructT _typfields -> ""
      | VariantT _typcases -> ""
    )

let gen_param_id_used (param : CoqAst.param) =
  match param.it with
    | ExpP (id, _) -> id.it
    | TypP id -> id.it

let gen_match_clause (params : CoqAst.param list) =
  match params with
   | [] -> ""
   | _ -> "\tmatch " ^ parens (String.concat ", " (List.map gen_param_id_used params)) ^ " with\n"

let gen_clause (c : CoqAst.clause) = 
  match c.it with
    | DefD (_binds, args, exp, _premises) -> "\t\t| " ^ gen_match_args args ^ " => " ^ gen_exp exp 

let gen_clauses (params : CoqAst.param list) (clauses : CoqAst.clause list) =
  match clauses with
    | [{it = DefD (_, _, exp, _); _}] -> gen_exp exp 
    | _ -> "\n" ^ gen_match_clause params ^ String.concat "\n" (List.map gen_clause clauses) ^ "\n\tend"

let gen_rules (id : CoqAst.id) (rules : CoqAst.rule list) =
  ""

let rec gen_def (d : CoqAst.def) (is_recursive : bool)=
  match d.it with
    | TypD (id, _params, [{it = InstD (args, deftyp); _}]) -> gen_deftyp args id deftyp
    | TypD (_id, _params, _insts) -> ""
    | RelD (id, mixop, typ, rules) -> "Inductive " ^ id.it ^ gen_mixop mixop ^ ": " ^ gen_typ typ ^ gen_rules id rules
    | DecD (id, params, typ, clauses) -> let prefix = if is_recursive then "Fixpoint " else "Definition " in 
      prefix ^ func ^ id.it 
      ^ String.concat " " (List.map gen_param params) 
      ^ ": " ^ gen_typ typ ^ " := "
      ^ gen_clauses params clauses
    | RecD defs -> String.concat "" (List.map (fun d -> gen_def d true) defs)

let gen_script (il : CoqAst.script) =
  String.concat "\n" (List.filter (fun s -> s <> ".\n") (List.map (fun d -> gen_def d false ^ ".\n") il)) 

let gen_string (il : script) =
  let translated_il = translate_il il in
  "From Coq Require Import String List Unicode.Utf8.\n" ^
  "Require Import NArith.\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "\n" ^
  "(* Generated Code *)\n" ^
  gen_script translated_il

let gen_file file il =
  let coq_code = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)

