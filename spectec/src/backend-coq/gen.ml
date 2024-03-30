open Il.Ast
open Translate
open Util.Source

module CoqAst = Ast

let parens s = "(" ^ s ^ ")"

let gen_atom (a : CoqAst.atom) =
  match a with
    | Atom str -> str
    | _ -> "" (*TODO:  This should not occur ever *)

let rec gen_typ (t: CoqAst.typ) =
  match t.it with
    | VarT id -> id.it
    | NatT -> "nat"
    | TextT -> "string"
    | BoolT -> "bool"
    | TupT typs -> String.concat " * " (List.map (fun t -> gen_typ t) typs)
    | IterT (_typ, _iter) -> ""

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
    | PlusOp -> "+"
    | MinusOp -> "0 - "

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
    | NatE nat -> string_of_int nat
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
    | CallE (id, exp) -> parens (id.it ^ " " ^ gen_exp exp)
    | IterE (_exp, (_iter, _ids)) -> ""  
    | OptE None -> "None"
    | OptE (Some exp) -> "Some " ^ gen_exp exp  
    | TheE _exp -> ""              
    | ListE _exps -> ""           
    | CatE (exp1, exp2) -> parens (gen_exp exp1 ^ " ++ " ^ gen_exp exp2)      
    | CaseE (atom, exp) -> parens (gen_atom atom ^ " ++ " ^ gen_exp exp)      
    | SubE (_exp, _typ1, _typ2) -> ""


(* and gen_path (p : CoqAst.path) =
  match p.it with   
    | RootP -> ""
    | IdxP (_path, _exp) -> ""
    | SliceP (path, exp1, exp2) -> ""
    | DotP (path, atom) -> ""

and gen_iter (it : CoqAst.iter) =
  match it with
    | Opt -> ""
    | List -> ""
    | List1 -> ""
    | ListN (exp, id) -> "" *)
let gen_premises (p : CoqAst.premise) =
  match p.it with
    | IfPr exp -> gen_exp exp
    | _ -> ""

let gen_variant_type (id : id) (t : CoqAst.typ) =
  match t.it with
    | TupT [] -> id.it
    | _ -> gen_typ t ^ " -> " ^ id.it
let gen_variant_premises (premises : CoqAst.premise list) =
  let e = (match premises with
    | [] -> ""
    | _ -> " -> ") in
  String.concat " /\\ " (List.map gen_premises premises) ^ e
let gen_typcases id typcases = 
  "Inductive " ^ id.it ^ ": Type :=\n" ^ 
  String.concat "\n" (List.map (fun (a, (t, premises)) -> 
    "\t| " ^ id.it ^ "__" ^ gen_atom a ^ ": " ^ gen_variant_premises premises 
    ^ gen_variant_type id t) typcases)

let gen_def (d : CoqAst.def) =
  match d.it with
    | SynD (id, deftyp) -> (match deftyp.it with
      | AliasT typ -> "Definition " ^ id.it ^ " := " ^ gen_typ typ
      | NotationT (_mixop, _typ) -> gen_exp (CoqAst.TextE "" $ no_region)
      | StructT _typfields -> ""
      | VariantT typcases -> gen_typcases id typcases
    )
    | RelD (_id, _mixop, _typ, _rules) -> ""
    | DecD (_id, _typ1, _typ2, _clauses) -> ""
    | RecD _defs -> ""

let gen_script (il : CoqAst.script) =
  String.concat "\n" (List.map (fun d -> gen_def d ^ "\n.") il) 
let gen_string (il : script) =
  let translated_il = translate_il il in
  gen_script translated_il

let gen_file file il =
  let coq_code = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)

