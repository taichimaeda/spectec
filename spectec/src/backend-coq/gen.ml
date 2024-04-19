open Il.Ast
open Translate
open Util.Source

module CoqAst = Ast
module IdSet = Set.Make(String)

let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"

(* Function prefix (To avoid same name clash on types) *)
let func_prefix = "fun_"

(* variable prefix (To avoid same name clash on types) *)
let var_prefix = "v_"

let gen_atom_total (a : CoqAst.atom) = 
  match a.it with
    | Atom id -> Some id
    | _ -> None
let gen_atom (a : CoqAst.atom) = 
  match gen_atom_total a with
    | Some id -> id
    | None -> ""
let gen_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> a
    | mixop -> String.concat "" (List.map (
        fun atoms -> String.concat "" (List.filter_map gen_atom_total atoms)) mixop
      )
    

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

let gen_iter_typ (it : CoqAst.iter) =
  match it with
    | Opt -> "option"
    | List -> "list"
    | List1 -> "list"
    | ListN (_exp, _id) -> "list"

let gen_typ_name (t : CoqAst.typ) =
  match t.it with
    | VarT (id, _) -> id.it
    | _ -> assert false

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

let get_num_from_exp (e : CoqAst.exp) =
  match e.it with
    | NatE nat -> nat
    | _ -> Z.zero

let rec gen_exp ?(is_match : bool = false) (e : CoqAst.exp) =
  match e.it with
    | VarE id -> var_prefix ^ id.it
    | BoolE true -> "true"
    | BoolE false -> "false"
    | NatE nat -> Z.to_string nat
    | TextE text -> text
    | UnE (op, exp) ->  parens (gen_unop op ^ (gen_exp ~is_match exp))
    | BinE (binop, exp1, exp2) -> let num2 = get_num_from_exp exp2 in 
      if is_match && binop == AddOp && num2 <> Z.zero 
      then (gen_succ (Z.to_int num2) exp1) (* NOTE: Hack for nat matches *)
      else parens (gen_exp ~is_match exp1 ^ gen_binop binop ^ gen_exp ~is_match exp2)
    | CmpE (cmpop, exp1, exp2) -> parens (gen_exp ~is_match exp1 ^ gen_cmpop cmpop ^ gen_exp ~is_match exp2)
    | SliceE (_exp1, _exp2, _exp3) -> "8"
    | UpdE (_exp, _path, _exp2) -> "7"
    | ExtE (_exp1, _path, _exp2) -> "6"
    | StrE _expfields -> "5"       
    | DotE (exp, atom) -> gen_exp ~is_match exp ^ "." ^ gen_typ_name exp.note ^ "__" ^ gen_atom atom
    | CompE (_exp, _exp2) -> "3" 
    | TupE [] -> ""
    | TupE exps -> String.concat " " (List.map (fun e -> gen_exp ~is_match e) exps)   
    | MixE (_mixop, _exp) -> "10"    
    | CallE (id, args) -> func_prefix ^ id.it ^ " " ^ gen_call_args args
    | IterE (exp, (_iter, _ids)) -> gen_exp ~is_match exp  
    | OptE None -> "None"
    | OptE (Some exp) -> "Some " ^ gen_exp ~is_match exp  
    | TheE exp -> "the" ^ parens (gen_exp ~is_match exp)             
    | ListE exps -> (match exps with
      | [] -> "nil"
      | [e] -> if is_match then gen_exp ~is_match e else parens (gen_exp ~is_match e ^ " :: " ^ "nil")
      | _ -> "[" ^ String.concat ";" (List.map gen_exp exps) ^ "]")       
    | LenE exp -> "List.length(" ^ gen_exp ~is_match exp ^ ")"
    | CatE (exp1, exp2) -> let op = if is_match then " :: " else " ++ " in
      parens (gen_exp ~is_match exp1 ^ op ^ gen_exp ~is_match exp2)   
    | IdxE (exp1, exp2) -> "lookup_total(" ^ gen_exp ~is_match exp1 ^ ", " ^ gen_exp ~is_match exp2 ^ ")"  (* TODO: Haven't created lookup_total correctly yet*)
    | CaseE (mixop, exp1) -> let gen_exp1 = gen_exp ~is_match exp1 in parens (gen_typ_name e.note ^ "__" ^ gen_mixop mixop)
    ^ (if gen_exp1 == String.empty then "" else " " ^ gen_exp1) 
    | SubE (exp, _typ1, _typ2) -> gen_exp ~is_match exp
    | ProjE (_exp, n) -> string_of_int n
    | UncaseE (_exp, _mixop) -> "2"

and gen_typ (t: CoqAst.typ) =
  match t.it with
    | VarT (id, args) -> id.it ^ (gen_call_args args)
    | NatT -> "nat"
    | TextT -> "string"
    | BoolT -> "bool"
    | TupT [] -> "Type"
    | TupT typs -> String.concat " * " (List.map (fun (_, t) -> gen_typ t) typs)
    | IterT (typ, iter) -> gen_iter_typ iter ^ " " ^ parens (gen_typ typ)

and gen_typ_args (t : CoqAst.typ) =
  match t.it with
    | TupT typs -> String.concat " " (List.map (fun (e, t) -> parens (gen_exp e ^ " : " ^ gen_typ t)) typs)
    | _ -> parens (gen_typ t)

and gen_bind_typ (b : CoqAst.bind) =
  match b.it with 
    | ExpB (_, typ, _) -> gen_typ typ
    | TypB id -> id.it

and gen_arg (a : CoqAst.arg * CoqAst.bind) =
  match a with
    | ({it = ExpA exp; _},{it = ExpB (_, typ, _); _}) -> Some (parens (gen_exp exp ^ " : " ^ gen_typ typ))
    | ({it = TypA typ; _},{it = TypB _; _}) -> Some (curly_parens (gen_typ typ))
    | _ -> None

and gen_args (binds : CoqAst.bind list) (args : CoqAst.arg list) =
  match args with
    | [] -> ""
    | _ -> String.concat " " (List.filter_map gen_arg (List.combine args binds))

and gen_call_args (args : CoqAst.arg list) =
  match args with
  | [] -> ""
  | _ -> String.concat " " (List.map parens (List.filter_map (gen_arg_name false) args))

and gen_arg_name (is_match : bool) (a : CoqAst.arg) = 
  match a.it with
    | ExpA exp -> Some (gen_exp ~is_match exp)
    | _ -> None

and gen_match_args (args : CoqAst.arg list) = 
  match args with
    | [] -> ""
    | _ -> parens (String.concat ", " (List.filter_map (gen_arg_name true) args))

and gen_succ (n : int) (exp : CoqAst.exp) : text =
  match n with
    | 0 -> gen_exp exp 
    | m -> "S" ^ parens (gen_succ (m - 1) exp)
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

let gen_variant_premises (premises : CoqAst.premise list) =
  let e = (match premises with
    | [] -> ""
    | _ -> " -> ") in
  String.concat " /\\ " (List.map gen_premises premises) ^ e

let gen_param (p : CoqAst.param) = 
  match p.it with
    | ExpP (id, typ) -> parens (var_prefix ^ id.it ^ " : " ^ gen_typ typ)
    | TypP id -> curly_parens id.it

let gen_deftyp (binds : CoqAst.bind list) (args : CoqAst.arg list) (id : CoqAst.id) (d : CoqAst.deftyp) =
  match d.it with
    | AliasT typ -> "Definition " ^ id.it ^ gen_args binds args ^  " := " ^ gen_typ typ
    | StructT typfields -> "Record " ^ id.it ^ " := \n{" ^ "\t" ^
    String.concat "\n;\t" (List.map (fun (a, (t, _premises)) -> 
      id.it ^ "__" ^ gen_atom a ^ " : " ^ gen_typ t
    ) typfields) ^ "\n}" 
    | VariantT typcases -> 
    let arg_names = match args with 
      | [] -> "" 
      | _ -> " " ^ String.concat " " (List.filter_map (gen_arg_name false) args)
    in 
    "Inductive " ^ id.it ^ " " ^ gen_args binds args ^  " : Type :=\n" ^ 
    String.concat "\n" (List.map (fun (m, (t, _premises)) -> 
    "\t| " ^ id.it ^ "__" ^ gen_mixop m ^ gen_typ_args t ^ ": " ^
    id.it ^ arg_names) typcases)

let gen_param_id_used (param : CoqAst.param) =
  match param.it with
    | ExpP (id, _) -> Some (var_prefix ^ id.it)
    | _ -> None

let _gen_param_typ_used (param : CoqAst.param) =
  match param.it with
    | ExpP (_, typ) -> Some (gen_typ typ)
    | _ -> None

let gen_match_clause (params : CoqAst.param list) =
  match params with
    | [] -> ""
    | _ -> "\tmatch " ^ parens (String.concat ", " (List.filter_map gen_param_id_used params)) ^ " with\n"

let gen_instance (id : CoqAst.id) (i : CoqAst.inst) =
  match i.it with
    | InstD (binds, args, deftyp) -> (match deftyp.it with
      | AliasT typ -> "\t\t| " ^ gen_match_args args ^ " => " ^ gen_typ typ
      | VariantT typcases -> 
      let inductive_name = id.it ^ "__" ^ String.concat "__" (List.map (fun b -> gen_bind_typ b) binds) 
      in "Inductive " ^ inductive_name ^ " : Type :=\n" ^
      String.concat "\n" (List.map (fun (m, (t, _premises)) -> 
      "\t| " ^ inductive_name ^ "__" ^ gen_mixop m ^ gen_typ_args t ^ ": " ^ inductive_name) 
      typcases)
      | _ -> gen_deftyp binds args id deftyp
    )
let get_instance_binds (i : CoqAst.inst) =
  match i.it with
    | InstD (binds, args, _) -> (binds, args)
    
let gen_instances (params : CoqAst.param list) (id : CoqAst.id) (insts : CoqAst.inst list) =
  let i = List.hd insts in
  let binds_args_list = List.map get_instance_binds insts in
  match i.it with
  | InstD (_, _, deftyp) -> (match deftyp.it with 
    | AliasT _ -> "Definition " ^ id.it ^ 
    String.concat " " (List.map gen_param params) ^ " :=\n"  ^
    gen_match_clause params ^ 
    String.concat "\n" (List.map (gen_instance id) insts) ^
    "\n\tend"
    | StructT _ -> "" (* Should not happen *)
    | VariantT _ -> 
    String.concat ".\n" (List.map (gen_instance id) insts) ^ ".\n" ^
    "Definition " ^ id.it ^ 
    String.concat " " (List.map gen_param params) ^ " :=\n" ^
    gen_match_clause params ^
    "\t| " ^ String.concat "\n\t| " (List.map (fun (binds, args) -> 
     gen_match_args args ^ " => " ^ id.it ^ "__" ^ 
     String.concat "__" (List.map (fun b -> gen_bind_typ b) binds)) binds_args_list) ^
     "\n\tend"
  ) 
  
let gen_clause (c : CoqAst.clause) = 
  match c.it with
    | DefD (_binds, args, exp, _premises) -> "\t\t| " ^ gen_match_args args ^ " => " ^ gen_exp exp 

let gen_clauses (params : CoqAst.param list) (clauses : CoqAst.clause list) =
  match clauses with
    | [] -> ""
    | [{it = DefD (_, _, exp, _); _}] -> " := " ^ gen_exp exp 
    | _ -> " :=\n" ^ gen_match_clause params ^ String.concat "\n" (List.map gen_clause clauses) ^ "\n\tend"

let gen_rule (id : CoqAst.id) (rule : CoqAst.rule) =
  match rule.it with
    | RuleD (rule_id, mixop, exp, prems) -> let rule_id' = if String.empty <> rule_id.it then rule_id.it ^ " " else "" in
    "\t| " ^ id.it ^ "__" ^ rule_id' ^ gen_mixop mixop ^ " " ^ gen_exp exp ^ " : " ^ gen_variant_premises prems ^ id.it

let gen_rules (id : CoqAst.id) (rules : CoqAst.rule list) =
  String.concat "\n" (List.map (gen_rule id) rules)

let rec gen_def (d : CoqAst.def) (is_recursive : bool) =
  match d.it with
    | TypD (id, _params, [{it = InstD (binds, args, deftyp); _}]) -> gen_deftyp binds args id deftyp
    | TypD (id, params, insts) -> gen_instances params id insts 
    | RelD (id, _mixop, typ, rules) -> "Inductive " ^ id.it ^ ": " ^ gen_typ typ ^ " := \n" ^ gen_rules id rules
    | DecD (id, params, typ, clauses) -> let prefix = if is_recursive then "Fixpoint " else "Definition " in 
      prefix ^ func_prefix ^ id.it 
      ^ String.concat " " (List.map gen_param params) 
      ^ ": " ^ gen_typ typ
      ^ gen_clauses params clauses
    | RecD defs -> String.concat "" (List.map (fun d -> gen_def d true) defs)

let gen_script (il : CoqAst.script) =
  String.concat "\n" (List.filter (fun s -> s <> ".\n") (List.map (fun d -> gen_def d false ^ ".\n") il)) 

let gen_string (il : script) =
  let translated_il = translate_il il in
  "From Coq Require Import String List Unicode.Utf8.\n" ^
  "Require Import NArith.\n" ^
  "Require Import Arith.\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "\tList.nth n l default_val.\n\n" ^
  "Definition the {T : Type} {_ : Inhabited T} (arg : option T) : T :=\n" ^
	"\tmatch arg with\n" ^
	"\t\t| Some a => a\n" ^
	"\t\t| None => default_val\n" ^
	"\tend.\n\n" ^
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

