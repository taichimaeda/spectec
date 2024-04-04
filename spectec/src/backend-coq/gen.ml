open Il.Ast
open Translate
open Util.Source

module CoqAst = Ast

let parens s = "(" ^ s ^ ")"
let curly_parens s = "{" ^ s ^ "}"

(* Hack for now for mixops, anonymous names with be a *)
let reserved_mixop_name = "a"

let _gen_atom (a : CoqAst.atom) = Il.Atom.string_of_atom a
let gen_mixop (m : mixop) =
  match m with
    | [{it = Atom a; _}]::tail when List.for_all ((=) []) tail -> a
    | _ -> reserved_mixop_name
    
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
    | CallE (id, args) -> parens (id.it ^ String.concat " " (List.map gen_arg args))
    | IterE (exp, (_iter, _ids)) -> gen_exp exp  
    | OptE None -> "None"
    | OptE (Some exp) -> "Some " ^ gen_exp exp  
    | TheE _exp -> ""              
    | ListE _exps -> ""           
    | CatE (exp1, exp2) -> parens (gen_exp exp1 ^ " ++ " ^ gen_exp exp2)      
    | CaseE (mixop, exp) -> parens (gen_mixop mixop ^ " ++ " ^ gen_exp exp)      
    | SubE (exp, _typ1, _typ2) -> gen_exp exp
    | ProjE (_exp, _n) -> ""
    | UncaseE (_exp, _mixop) -> ""

and gen_typ (t: CoqAst.typ) =
  match t.it with
    | VarT (id, args) -> id.it ^ gen_args args
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
    | ExpA exp -> parens (gen_exp exp)
    | TypA typ -> curly_parens (gen_typ typ)

and gen_args (args: CoqAst.arg list) =
  match args with
    | [] -> ""
    | _ -> String.concat " " (List.map (fun x -> gen_arg x) args)

let gen_arg_name (a : CoqAst.arg) = 
  match a.it with
    | ExpA exp -> gen_exp exp
    | _ -> ""

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

let _gen_variant_type (id : CoqAst.id) (t : CoqAst.typ) =
  match t.it with
    | TupT [] -> id.it
    | _ -> gen_typ t ^ " -> " ^ id.it
let gen_variant_premises (premises : CoqAst.premise list) (id : CoqAst.id) =
  let e = (match premises with
    | [] -> ""
    | _ -> " -> ") in
  String.concat " /\\ " (List.map gen_premises premises) ^ e ^ id.it

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
let gen_def (d : CoqAst.def) =
  match d.it with
    | TypD (id, _params, [{it = InstD (args, deftyp); _}]) -> gen_deftyp args id deftyp
    | TypD (id, params, insts) -> "Definition " ^ id.it ^ String.concat " " (List.map gen_param params) ^ " := \n" ^
      String.concat "\n" (List.map (fun i -> (gen_instances id i) ^ ".\n") insts)
    | RelD (_id, _mixop, _typ, _rules) -> ""
    | DecD (_id, _params, _typ, _clauses) -> ""
    | RecD _defs -> ""

let gen_script (il : CoqAst.script) =
  String.concat "\n" (List.filter (fun s -> s <> ".\n") (List.map (fun d -> gen_def d ^ ".\n") il)) 

let gen_string (il : script) =
  let translated_il = translate_il il in
  "From Coq Require Import List.\n" ^
  "From Coq Require Import Arith.\n" ^
  "\n" ^
  "(* Generated Code *)\n" ^
  gen_script translated_il

let gen_file file il =
  let coq_code = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)

