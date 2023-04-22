open Il.Ast

let error at msg = Util.Source.error at "Coq generation" msg

let include_input = false

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"
let ($$$) s1 ss = parens (String.concat " " (s1 :: ss))
let ($$) s1 s2 = s1 $$$ [s2]
let render_tuple how tys = parens (String.concat ", " (List.map how tys))
let render_list how tys = 
  if tys = [] then "nil"
  else brackets (String.concat "; " (List.map how tys))

(* let render_rec_con (id : id) = "Mk" ^ render_type_name id *)

let is_reserved = function
 | "in"
 | "()"
 -> true
 | _
 -> false

let make_id s = match s with
 | s when is_reserved s -> "reserved_" ^ s
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s


let render_id (id : id) = make_id id.it

let render_fun_id (id : id) = "fun_" ^ id.it

let render_type_name (id : id) = make_id (String.capitalize_ascii id.it)

let render_rule_name ty_id (rule_id : id) (i : int) :  string =
  render_type_name ty_id ^ "_" ^
  if rule_id.it = ""
  then "rule_" ^ string_of_int i
  else make_id rule_id.it

let render_con_name id : atom -> string = function
  | Atom s -> render_type_name id ^ "_" ^ make_id s
  | a -> "(* render_con_name: TODO *) " ^ Il.Print.string_of_atom a

let render_con_name' (typ : typ) a = match typ.it with
  | VarT id -> render_con_name id a
  | _ -> "_ (* render_con_name': Typ not id *)"


let render_field_name : atom -> string = function
  | Atom s -> make_id s
  | a -> "(* render_field_name: TODO *) " ^ Il.Print.string_of_atom a


let wrap_type_iter (ty : string) : iter -> string = function
  | Opt -> "option" $$ ty
  |  _  -> "list" $$ ty

let wrap_type_iters (ty : string) : iter list -> string = List.fold_left wrap_type_iter ty

let rec render_typ (ty : typ) = match ty.it with
  | VarT id -> render_type_name id
  | BoolT -> "bool"
  | NatT -> "nat"
  | TextT -> "string"
  | TupT [] -> "unit"
  | TupT tys -> render_tuple_typ tys
  | IterT (ty, it) -> wrap_type_iter (render_typ ty) it

and render_tuple_typ tys = parens (String.concat " * " (List.map render_typ tys))

let render_variant_case id ((a, ty, _hints) : typcase) =
  render_con_name id a ^ " : " ^
  if ty.it = TupT []
  then render_type_name id
  else render_typ ty ^ " -> " ^ render_type_name id

(* We need a lift if the LHS is a list lookup, since total lookups are scuffed in Coq *)
let lookup_option_lift (e1: exp) : string = 
  match e1.it with
  | IdxE _ -> "Some "
  | _ -> ""
  
let rec render_exp (exp : exp) = match exp.it with
  | VarE v -> render_id v
  | BoolE true -> "True"
  | BoolE false -> "Frue"
  | NatE n -> string_of_int n
  | TextE t -> "\"" ^ String.escaped t ^ "\""
  | MixE (_, e) -> render_exp e
  | TupE es -> render_tuple render_exp es
  | ListE es -> render_list render_exp es
  | OptE None -> "None"
  | OptE (Some e) -> "Some" $$ render_exp e
  (* Seems to be looking up from a list*)
  | TheE e  -> "(* TODO: what is TheE? *) List.nth_error " ^ render_exp e
  | IterE (e, (iter, vs)) -> begin match e.it with
    (* Short-ciruit v*; use variable directly instead of calling map *)
    | VarE v when [v.it] = List.map (fun (v : id) -> v.it) vs -> render_id v
    | _ -> match iter, vs with
      | (List|List1|ListN _), [] ->
        "[" ^ render_exp e ^ "]"
      | (List|List1|ListN _), [v] ->
        "List.map" $$$ [render_lam v e; render_id v]
      | (List|List1|ListN _), [v1; v2] ->
        "List.zipWith" $$$ [ "(fun " ^ render_id v1 ^ " " ^ render_id v2 ^ " => " ^ render_exp e ^ ")"; render_id v1; render_id v2 ]
      | Opt, [] -> "Some" $$ render_exp e
      | Opt, [v] ->
        "Option.map" $$$ [render_lam v e; render_id v]
      | Opt, [v1; v2] ->
        "option_zip" $$$ [ "(fun " ^ render_id v1 ^ " " ^ render_id v2 ^ " => " ^ render_exp e ^ ")"; render_id v1; render_id v2 ]
      | _, _ ->
      render_exp e ^ " (* " ^ Il.Print.string_of_iterexp (iter, vs) ^ " *)"
  end
  | CaseE (a, e, typ) -> render_case a e typ
  | StrE fields -> "{|" ^ ( String.concat "; " (List.map (fun (a, e) ->
    render_field_name a ^ " := " ^ render_exp e
    ) fields)) ^ "|}"
  | SubE _ -> error exp.at "SubE encountered. Did the SubE elimination pass run?"
  | DotE (_ty, e, a) -> render_dot (render_exp e) a
  | UpdE (exp1, path, exp2) ->
    render_path path (render_exp exp1) (fun _ -> render_exp exp2)
  | ExtE (exp1, path, exp2) ->
    render_path path (render_exp exp1) (fun old_val -> "List.append" $$$ [old_val;  render_exp exp2])
  | IdxE (e1, e2) -> render_idx (render_exp e1) e2
  | LenE e -> "List.length (" ^ render_exp e ^ ")"
  | CallE (id, e) -> render_fun_id id $$ render_exp e
  | UnE (MinusOp, e1)      -> parens ("0 - " ^ render_exp e1)
  | BinE (AddOp, e1, e2)   -> parens (render_exp e1 ^ " + " ^ render_exp e2)
  | BinE (SubOp, e1, e2)   -> parens (render_exp e1 ^ " - " ^ render_exp e2)
  | BinE (ExpOp, e1, e2)   -> parens ("Nat.pow" $$ render_exp e1 $$ render_exp e2)
  | BinE (DivOp, e1, e2)   -> parens ("Nat.div" $$ render_exp e1 $$ render_exp e2)
  | BinE (AndOp, e1, e2)   -> parens (render_exp e1 ^ " /\\ "  ^ render_exp e2)
  | BinE (EquivOp, e1, e2) -> parens (render_exp e1 ^ " = "   ^ render_exp e2)
  | BinE (OrOp, e1, e2)    -> parens (render_exp e1 ^ " \\/ "  ^ render_exp e2)
  | CmpE (EqOp, e1, e2)    -> parens (render_exp e1 ^ " = "  ^ lookup_option_lift e1 ^ render_exp e2)
  | CmpE (NeOp, e1, e2)    -> parens (render_exp e1 ^ " <> "  ^ render_exp e2)
  | CmpE (LeOp, e1, e2)    -> parens (render_exp e1 ^ " <= "  ^ render_exp e2)
  | CmpE (LtOp, e1, e2)    -> parens (render_exp e1 ^ " < "   ^ render_exp e2)
  | CmpE (GeOp, e1, e2)    -> parens (render_exp e1 ^ " >= "  ^ render_exp e2)
  | CmpE (GtOp, e1, e2)    -> parens (render_exp e1 ^ " > "   ^ render_exp e2)
  | CatE (e1, e2)          -> parens (render_exp e1 ^ " ++ "  ^ render_exp e2)
  | CompE (e1, e2)         -> parens (render_exp e2 ^ " ++ "  ^ render_exp e1) (* NB! flip order *)
  | _ -> "unit (* " ^ Il.Print.string_of_exp exp ^ " *)"

and render_dot e_string a = e_string ^ "." ^ parens (render_field_name a)

and render_idx e_string exp = parens ("List.nth_error " ^ e_string ^ " " ^ render_exp exp)

(* The path is inside out, in a way, hence the continuation passing style here *)
and render_path (path : path) old_val (k : string -> string) : string = match path.it with
  | RootP -> k old_val
  | DotP (path', a) ->
    render_path path' old_val (fun old_val ->
     "{" ^ old_val ^ " with " ^  render_field_name a ^ " := " ^ k (render_dot old_val a) ^ " }"
    )
  | IdxP (path', idx_exp) ->
    render_path path' old_val (fun old_val ->
      "(list_update " ^ old_val ^ " " ^ render_exp idx_exp ^ " " ^ k (render_idx old_val idx_exp) ^ ")"
    )


and render_case a e typ =
    if e.it = TupE []
    then render_con_name' typ a
    else render_con_name' typ a $$ render_exp e

and render_lam v e = match e.it with
  | CallE (f, {it = VarE v2;_}) when v.it = v2.it -> render_fun_id f
  | _ -> "(fun " ^ render_id v ^ " => " ^ render_exp e ^ ")"

let render_clause (_id : id) (clause : clause) = match clause.it with
  | DefD (_binds, lhs, rhs, premise) ->
   (if premise <> [] then "-- Premises ignored! \n" else "") ^
   "\n  | " ^ render_exp lhs ^ " => " ^ render_exp rhs

let show_input (d:def) =
    if include_input then
    "(* " (*  ^ Util.Source.string_of_region d.at ^ "\n"*)  ^
    Il.Print.string_of_def d ^
    "\n*)\n"
    else ""

let rec render_prem (prem : premise) =
    match prem.it with
    | RulePr (pid, _mixops, pexp) -> render_type_name pid $$ render_exp pexp
    | IfPr (pexp) -> render_exp pexp
    | IterPr (prem, iterexp) ->
    begin match iterexp with
      | (List|List1|ListN _), [v] ->
        "(List.Forall (fun " ^ render_id v ^ " => " ^ render_prem prem ^ ") " ^ render_id v ^ ")"
      | (List|List1|ListN _), [v1; v2] ->
        "(List.Forall2 (fun " ^ render_id v1 ^ " " ^ render_id v2 ^ " => " ^ render_prem prem ^ ") " ^ render_id v1 ^ " " ^ render_id v2 ^ ")"
      | Opt, [v] ->
        "(List.Forall (fun " ^ render_id v ^ " => " ^ render_prem prem ^ ") " ^ render_id v ^ ".toList)"
      | Opt, [v1; v2] ->
        "(List.Forall2 (fun " ^ render_id v1 ^ " " ^ render_id v2 ^ " => " ^ render_prem prem ^ ") " ^ render_id v1 ^ ".toList " ^ render_id v2 ^ ".toList)"
      | _,_ -> render_prem prem ^ "(* " ^ Il.Print.string_of_iterexp iterexp ^ " *)"
    end
    | ElsePr -> error prem.at "ElsePr encountered. Did the SubE elimination pass run?"
    | NegPr prem -> "Not" $$ render_prem prem

let rec render_def (mutrec_qual: bool) (d : def) =
  match d.it with
  | SynD (id, deftyp, _hints) ->
    show_input d ^
    begin match deftyp.it with
    | AliasT ty ->
      "(** Alias definition : " ^ render_type_name id ^ " **)\n" ^
      "Definition " ^ render_type_name id ^ " := " ^ render_typ ty
    | NotationT (_mop, ty) ->
      "(** Notation definition : " ^ render_type_name id ^ " **)\n" ^
      "Definition " ^ render_type_name id ^ " := (* mixop: " (* TODO: add it back after escaping round brackets ^ Il.Print.string_of_mixop mop *) ^ " *) " ^ render_typ ty
    | VariantT cases ->
      "(** Inductive definition : " ^ render_type_name id ^ " **)\n" ^
      "Inductive " ^ render_type_name id ^ " : Type :=" ^ String.concat "" (
        List.map (fun case -> "\n | " ^ render_variant_case id case) cases
      ) ^ "\n"
    | StructT fields ->
      "(** Record definition : " ^ render_type_name id ^ " **)\n" ^
      "Record " ^ render_type_name id ^ " : Type := {" ^
      String.concat "" ( List.map (fun (a, ty, _hints) ->
        "\n  " ^ render_field_name a ^ " : " ^ render_typ ty ^ ";"
      ) fields) ^
      "\n } \n"
      (* TODO: this needs either an overloaded notation or a separate implementation. Is such thing actually used anywhere in the spec though? *)
     (* (* Generate an instance so that ++ works, for CompE *)
      "instance : Append " ^ render_type_name id ^ " where\n" ^
      "  append := fun r1 r2 => {\n" ^
      String.concat "" (List.map (fun (a, _ty, _hints) ->
        "    " ^ render_field_name a ^ " := r1." ^ render_field_name a ^ " ++ r2." ^ render_field_name a ^ ",\n"
      ) fields) ^
      "  }"*)
    end
  | DecD (id, typ1, typ2, clauses, hints) ->
    show_input d ^
    "(** Function definition : " ^ render_fun_id id ^ " **)\n" ^
    "Definition " ^ render_fun_id id ^ " (arg: " ^ render_typ typ1 ^ ") : " ^ render_typ typ2 ^ " :=\n" ^
    "  match arg with" ^
    begin if clauses = [] then " := default" else
    String.concat "" (List.map (render_clause id) clauses) ^
    (if (List.exists (fun h -> h.hintid.it = "partial") hints)
    then "\n  | _ => default" else "") ^ "\nend"(* Could use no_error_if_unused% as well *)
    end

  | RelD (id, _mixop, typ, rules, _hints) ->
    show_input d ^
    "(** Relation definition : " ^ render_type_name id ^ " **)\n" ^
    (if mutrec_qual then
      render_type_name id ^ " : " ^ render_typ typ ^ " -> Prop := "
    else "Inductive " ^ render_type_name id ^ " : " ^ render_typ typ ^ " -> Prop := ")
    ^
    String.concat "" (List.mapi (fun i (rule : rule) -> match rule.it with
      | RuleD (rule_id, binds, _mixop, exp, prems) ->
        "\n  | " ^ render_rule_name id rule_id i ^ " " ^
        String.concat " " (List.map (fun ((bid : id), btyp, iters) ->
          parens (render_id bid ^ " : " ^ wrap_type_iters (render_typ btyp) iters)
          ) binds) ^ " : " ^
        String.concat "" (List.map (fun (prem : premise) ->
          "\n    " ^ render_prem prem ^ " -> "
        ) prems) ^
          "\n    " ^ (render_type_name id $$ render_exp exp)
    ) rules) ^ "\n"

  | RecD defs ->
    (* It's not trivial to handle arbitrary mutual recursion *)
    (match defs with
    | [] -> error d.at "Mutual recursive definition cannot have an empty body"
    (* Self-recursion is always fine *)
    | [def] -> render_def false def 
    | def1 :: def2 :: defs' -> String.concat "\nwith " (render_def false def1 :: (List.map (render_def true) (def2 :: defs')))
    )

  | HintD _ -> ""

let is_non_hint (e: def) =
  match e.it with
  | HintD _ -> false
  | _ -> true

let render_script (el : script) =
  String.concat ".\n\n" (List.map (render_def false) (List.filter is_non_hint el)) ^ "."

let gen_string (el : script) =
  "(** Coq export **)\n\n" ^
  "From Coq Require Import String List Unicode.Utf8.\n" ^
  "\n" ^
  "Open Scope type_scope.\n" ^
  "Import ListNotations.\n" ^
  "\n" ^
  "Set Implicit Arguments.\n" ^
  "Unset Strict Implicit.\n" ^
  "Unset Printing Implicit Defensive.\n" ^
  "\n\n" ^
  "(** Auxiliary definitions **)\n" ^
  "\n" ^
  "Class Append (T: Type) : Type :=\n" ^
  "  append : T -> T -> T." ^
  "\n\n" ^
  "Definition option_zip {α β γ: Type} (f: α → β → γ) (x: option α) (y: option β): option γ := \n" ^
  " match x, y with\n" ^
  "  | Some x, Some y => Some (f x y)\n" ^
  "  | _, _ => None\n" ^
  " end.\n\n" ^
  "Definition option_to_list {α: Type} (x: option α): list α :=\n" ^
  " match x with\n" ^
  "  | None => nil\n" ^
  "  | Some x => (cons x nil)\n" ^
  " end.\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "match l, n with\n" ^
  "  | nil, _=> nil\n" ^
  "  | x :: l', 0 => y :: l'\n" ^
  "  | x :: l', S n => x :: list_update l' n y\n" ^
  "end.\n" ^
  "\n\n" ^
  "(** Generated code **)\n" ^
  "\n" ^
  render_script el


let gen_file file el =
  let coq_code = gen_string el in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)
