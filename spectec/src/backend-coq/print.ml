open Lang

let rec binder_type_lookup id binders =
  match binders with
  | [] -> UnitBT
  | b :: bs' -> 
    match b with 
    | (name, typ) -> 
      if id == name then typ
      else binder_type_lookup id bs'


let rec print_type typ = 
  match typ with
  | UnitBT -> "unit"
  | BoolBT -> "bool"
  | NatBT -> "nat"
  | StringBT -> "string"
  | TermT str -> str
  | ListT t -> "(list " ^ print_type t ^ ")"
  | OptionT t -> "(option " ^ print_type t ^ ")"
  | TupleT tys -> 
    begin match tys with
    | [] -> "unit"
    | [t] -> print_type t
    | _ -> "(" ^ String.concat " * " (List.map print_type tys) ^ ")"
    end

let print_typedef id typ =
  "Definition " ^ id ^ " := " ^ print_type typ

let print_bind b =
  match b with
  | (id, typ) -> "(" ^ id ^ " : " ^ print_type typ ^ ")"

let print_binds binds = 
  String.concat " " (List.map print_bind binds)

let print_unop unop =
  match unop with
  | NotE -> "~"
  | MinusE -> "0 -" (* TODO: print this correctly *)


let print_binop_prefix sop s1 s2 = sop ^ " " ^ s1 ^ " " ^ s2

let print_binop_infix sop s1 s2 = s1 ^ " " ^ sop ^ " " ^ s2

let print_binop binop s1 s2 = 
  match binop with
  | AddE -> print_binop_infix "+" s1 s2
  | SubE -> print_binop_infix "-" s1 s2
  | MulE -> print_binop_infix "*" s1 s2
  | DivE -> print_binop_infix "/" s1 s2
  | ExpE -> print_binop_prefix "Nat.pow" s1 s2
  | EqE -> print_binop_infix "=" s1 s2
  | NeqE -> print_binop_infix "<>" s1 s2
  | LeE -> print_binop_infix "<=" s1 s2
  | LtE -> print_binop_infix "<" s1 s2
  | GeE -> print_binop_infix ">=" s1 s2
  | GtE -> print_binop_infix ">" s1 s2
  | EquivE -> print_binop_infix "=" s1 s2
  | AndE -> print_binop_infix "/\\" s1 s2
  | OrE -> print_binop_infix "\\/" s1 s2

let rec print_exp exp = 
  match exp with
  | BasicE be -> print_basic_exp be
  | IdentE id -> id
  | AppE (id, es) -> 
    begin match es with 
    | [] -> "(* AppE *)" ^ id 
    | [e] -> if e = BasicE (TupE []) then id else "(" ^ id ^ " " ^ print_exp e ^ ")"
    | _ -> "(" ^ id ^ " " ^ String.concat " " (List.map print_exp es) ^ ")"
    end
  | MatchE exp_match -> 
    (match exp_match with
    | (id, clauses) ->
      "match " ^ id ^ " with\n  | " ^
      String.concat "\n  | " (List.map (fun (pat, exp) -> print_pat pat ^ " => " ^ print_exp exp) clauses) ^
      "\nend" )
  | UnsupportedE str -> "(* FIXME: unsuppurted exp: " ^ str ^ " *)"

and print_basic_exp be =
  match be with
  | NatBE n -> string_of_int n
  | BoolBE true -> "true"
  | BoolBE false -> "false"
  | StringBE str -> str
  | ListE es -> "[" ^ String.concat "; " (List.map print_exp es) ^ "]"
  | TupE es -> 
    begin match es with 
    | [] -> "(* Empty Tuple *) tt" (* TODO: check that this is always a unit *)
    | [e] -> print_exp e
    | _ -> "(" ^ String.concat ", " (List.map print_exp es) ^ ")"
    end
  | OptionE (Some e) -> "(Some " ^ print_exp e ^ ")"
  | OptionE None -> "None"
  | UnopE (unop, e) -> print_unop unop ^ " " ^ print_exp e
  | BinopE (binop, e1, e2) -> print_binop binop (print_exp e1) (print_exp e2)
  | OptionMapE (lexp, e) -> "(option.map " ^ print_lambda lexp ^ " " ^ print_exp e ^ ")"
  | OptionZipE (lexp, e1, e2) -> "(option_zip " ^ print_lambda lexp ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | ListLenE e -> "(List.length " ^ print_exp e ^ ")"
  | ListCatE (e1, e2) -> "(List.app " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | ListCompE (e1, e2) -> "(List.comp " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | ListMapE (lexp, e) -> "(List.map " ^ print_lambda lexp ^ " " ^ print_exp e ^ ")"
  | ListZipE (lexp, e1, e2) -> "(List.zip " ^ print_lambda lexp ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | ListGetE (e1, e2) -> "(list_get " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")"
  | ListSetE (e1, e2, e3) -> "(list_set " ^ print_exp e1 ^ " " ^ print_exp e2 ^ " " ^ print_exp e3 ^ ")"
  | ListForallE (lexp, e) -> "(List.Forall " ^ print_lambda lexp ^ " " ^ print_exp e ^ ")" 
  | ListForall2E (lexp, e1, e2) -> "(List.Forall2 " ^ print_lambda lexp ^ " " ^ print_exp e1 ^ " " ^ print_exp e2 ^ ")" 
  | RecordE fields -> "(\n{|\n  " ^ String.concat "\n  " (List.map (fun (id, e) -> id ^ " := " ^ print_exp e ^ ";") fields) ^ "\n|})\n"
  | GetFieldE (e, id) -> print_exp e ^ ".(" ^ id ^ ")"
  | SetFieldE (erec, id, e) -> print_exp erec ^ "(* TODO: record update: with " ^ id ^ " := " ^ print_exp e ^ "*)"
  
and print_pat pat = 
  match pat with
  | BasicP bp -> print_basic_pat bp
  | IdentP id -> id
  | ListP pats -> "[" ^ String.concat "; " (List.map print_pat pats) ^ "]"
  | AppP (id, pats) -> 
    begin match pats with 
    | [] -> "(* AppP *)" ^ id  
    | [p] -> if p = BasicP (TupP []) then id else id ^ " " ^ print_pat p
    | _ -> id ^ " " ^ String.concat " " (List.map print_pat pats)
    end
  | OptionP (Some pat) -> "(Some " ^ print_pat pat ^ ")"
  | OptionP None -> "None"
  | UnsupportedP str -> "(* FIXME: unsuppurted pat:" ^ str ^ "*)"

and print_basic_pat bp =
  match bp with
  | NatBP n -> string_of_int n
  | BoolBP true -> "true"
  | BoolBP false -> "false"
  | StringBP str -> str
  | TupP pats -> 
    (match pats with
    | [] -> "(* Empty Tuple *) tt" 
    | _ -> "(" ^ String.concat ", " (List.map print_pat pats) ^ ")")

and print_lambda lexp =
  match lexp with
  | (ids, exp) -> 
    if ids = [] then print_exp exp 
    else "(fun " ^ String.concat " " ids ^ " => " ^ print_exp exp ^ ")"

let print_funcdef recf id binds typ exp =
  "(* Funcdef *)\n" ^ (if recf = RecF then "Fixpoint " else "Definition ") ^
  id ^ " " ^ print_binds binds ^ " : " ^ print_type typ ^ " := \n" ^ 
  "  " ^ print_exp exp

let print_type_constructor tid tconstr = 
  match tconstr with
  | (id, tys) -> tid ^ "__" ^ id ^ " : " ^ String.concat " -> " ((List.map print_type tys) @ [tid])

let print_indtype id tconstrs = 
  "Inductive " ^ id ^ " : Type :=" ^
  String.concat "" (List.map (fun constr -> "\n| " ^ print_type_constructor id constr) tconstrs) ^
  "\n"

let print_prems prem_exps = 
  "  " ^ String.concat " ->\n  " (List.map print_exp prem_exps)

let print_rel_constructor tid rconstr =
  match rconstr with
  | (id, binders, prem_exps, e) ->
    id ^ " " ^ print_binds binders ^ ": \n" ^
    begin if (prem_exps != []) then
      print_prems prem_exps ^ " ->\n  " 
    else "  "
  end ^ tid ^ " " ^ print_exp e

let print_indrel id typ rconstrs =
  "Inductive " ^ id ^ " : " ^ print_type typ ^ " -> Prop :=\n| " ^
  String.concat "\n| " (List.map (print_rel_constructor id) rconstrs) ^
  "\n"

let print_record_constructor field = 
  match field with
  | (id, typ) -> id ^ " : " ^ print_type typ

let print_recorddef id fields = 
  "Record " ^ id ^ " : Type :=\n{\n  " ^
  String.concat ";\n  " (List.map print_record_constructor fields) ^ 
  "\n}"

let rec print_def def = 
  match def with
  | TypeD (id, typ) -> print_typedef id typ
  | FuncD (recf, id, binds, typ, exp) -> print_funcdef recf id binds typ exp
  | IndTypeD (id, tconstrs) -> print_indtype id tconstrs
  | IndRelD (id, typ, rconstrs) -> print_indrel id typ rconstrs
  | RecordD (id, fields) -> print_recorddef id fields
  | MutualD defs -> String.concat "\nwith\n" (List.map print_def defs) (* TODO: fix *)
  | UnsupportedD str -> "(* FIXME: Unsupported type definition: " ^ str ^ "*)"

let print_defs defs = 
  String.concat ".\n\n" (List.map print_def defs) ^ ".\n"

let print_prelude = "Require Import List String.\n\nImport ListNotations.\n\nOpen Scope type_scope.\n\n"

let gen_string il: string = 
  let defs = Translate.translate_script il in
    "(* Coq code below *)\n\n" ^
    print_prelude ^ 
    print_defs defs

let gen_file file il =
  let output = gen_string il in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc output)
    ~finally:(fun () -> Out_channel.close oc)