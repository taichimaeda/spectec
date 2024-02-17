open Il.Ast


let error at msg = Util.Source.error at "Coq generation" msg

(* an ugly solution given the constraints *)
let record_helper = Hashtbl.create 16

let include_input = false

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"
let ($$$) s1 ss = parens (String.concat " " (s1 :: ss))
let ($$) s1 s2 = s1 $$$ [s2]
let render_tuple how tys = 
  if tys = [] then "tt"
  else parens (String.concat ", " (List.map how tys))
let render_list how tys = 
  if tys = [] then "nil"
  else brackets (String.concat "; " (List.map how tys))

module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"] |> IdSet.of_list

let make_id s = match s with
 | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s


let render_id (id : id) = make_id id.it

let render_fun_id (id : id) = "fun_" ^ id.it

let render_type_name (id : id) = make_id id.it

let render_rule_name ty_id (rule_id : id) (i : int) :  string =
  render_type_name ty_id ^ "__" ^
  if rule_id.it = ""
  then "rule_" ^ string_of_int i
  else make_id rule_id.it

let render_con_name id : atom -> string = function
  | Atom s -> render_type_name id ^ "__" ^ make_id s
  | a -> "(* render_con_name: TODO *) " ^ Il.Print.string_of_atom a

let render_con_name' (typ : typ) a = match typ.it with
  | VarT id -> render_con_name id a
  | _ -> "_ (* render_con_name': Typ not id *)"


let render_field_name oty_id (at: atom) : string = 
  begin match oty_id with
  | Some ty_id -> render_type_name ty_id ^ "__"
  | None -> ""
  end ^
  match at with
  | Atom s -> make_id s
  | a -> "(* render_field_name: TODO *) " ^ Il.Print.string_of_atom a


let wrap_type_iter (ty : string) : iter -> string = function
  | Opt -> "option" $$ ty
  |  _  -> "list" $$ ty

let wrap_type_iters (ty : string) : iter list -> string = List.fold_left wrap_type_iter ty

let rec render_typ (ty : typ) = match ty.it with
  | VarT id -> render_type_name id
  | BoolT -> "bool"
  | NumT _-> "nat" (* TODO: With changes to numtypes is this still reasonable? *)
  | TextT -> "string"
  | TupT [] -> "unit"
  | TupT tys -> render_tuple_typ tys
  | IterT (ty, it) -> wrap_type_iter (render_typ ty) it

and render_tuple_typ tys = parens (String.concat " * " (List.map render_typ tys)) ^ "%type"

let render_variant_case id ((a, (_binds, ty, _premises), _hints) : typcase) =
  render_con_name id a ^ " : " ^
  if ty.it = TupT []
  then render_type_name id
  else render_typ ty ^ " -> " ^ render_type_name id
  
let infer_record_name ats = 
  let fields_name = String.concat "" (List.map (fun a -> render_field_name None a) ats) in
  Hashtbl.find_opt record_helper fields_name

let render_iterexp iter ids = Il.Print.string_of_iter iter ^ "{" ^ String.concat " " (List.map Util.Source.it ids) ^ "}"

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
  (* Seems to be looking up from a list *)
  | TheE e  -> "(* TODO: what is TheE? *) " ^ render_exp e
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
      render_exp e ^ " (* " ^ render_iterexp iter vs ^ " *)"
  end
  | CaseE (a, e) -> render_case a e exp.note
  | StrE fields -> 
    let o_record_name = infer_record_name (List.map fst fields) in
    (if o_record_name = None then "(* FIXME: cannot infer the type of record *) " else "") ^
    "{| " ^ ( String.concat "; " (List.map (fun (a, e) ->
    render_field_name o_record_name a ^ " := " ^ render_exp e
    ) fields)) ^ " |}"
  | SubE _ -> error exp.at "SubE encountered. Did the SubE elimination pass run?"
  | DotE (e, a) -> render_dot (render_exp e) a
  | UpdE (exp1, path, exp2) ->
    render_path path (render_exp exp1) (fun _ -> render_exp exp2)
  | ExtE (exp1, path, exp2) ->
    render_path path (render_exp exp1) (fun old_val -> "List.app" $$$ [old_val;  render_exp exp2])
  | IdxE (e1, e2) -> render_idx (render_exp e1) e2
  | LenE e -> "List.length (" ^ render_exp e ^ ")"
  | CallE (id, e) -> render_fun_id id $$ render_exp e
  | UnE (MinusOp _, e1)      -> parens ("0 - " ^ render_exp e1)
  | UnE (NotOp, e1)      -> parens ("~" ^ render_exp e1)
  | BinE (AddOp _, e1, e2)   -> parens (render_exp e1 ^ " + " ^ render_exp e2)
  | BinE (SubOp _, e1, e2)   -> parens (render_exp e1 ^ " - " ^ render_exp e2)
  | BinE (ExpOp _, e1, e2)   -> parens ("Nat.pow" $$ render_exp e1 $$ render_exp e2)
  | BinE (DivOp _, e1, e2)   -> parens ("Nat.div" $$ render_exp e1 $$ render_exp e2)
  | BinE (AndOp, e1, e2)   -> parens (render_exp e1 ^ " /\\ "  ^ render_exp e2)
  | BinE (EquivOp, e1, e2) -> parens (render_exp e1 ^ " = "   ^ render_exp e2)
  | BinE (OrOp, e1, e2)    -> parens (render_exp e1 ^ " \\/ "  ^ render_exp e2)
  | CmpE (EqOp, e1, e2)    -> parens (render_exp e1 ^ " = "  ^ render_exp e2)
  | CmpE (NeOp, e1, e2)    -> parens (render_exp e1 ^ " <> "  ^ render_exp e2)
  | CmpE (LeOp _, e1, e2)    -> parens (render_exp e1 ^ " <= "  ^ render_exp e2)
  | CmpE (LtOp _, e1, e2)    -> parens (render_exp e1 ^ " < "   ^ render_exp e2)
  | CmpE (GeOp _, e1, e2)    -> parens (render_exp e1 ^ " >= "  ^ render_exp e2)
  | CmpE (GtOp _, e1, e2)    -> parens (render_exp e1 ^ " > "   ^ render_exp e2)
  | CatE (e1, e2)          -> parens (render_exp e1 ^ " ++ "  ^ render_exp e2)
  | CompE (e1, e2)         -> parens (render_exp e2 ^ " ++ "  ^ render_exp e1) (* NB! flip order *)
  | _ -> "default_val (* FIXME: " ^ Il.Print.string_of_exp exp ^ " *)"

and render_dot e_string a = e_string ^ "." ^ parens (render_field_name None a)

and render_idx e_string exp = parens ("lookup_total " ^ e_string ^ " " ^ render_exp exp)

(* The path is inside out, in a way, hence the continuation passing style here *)
and render_path (path : path) old_val (k : string -> string) : string = match path.it with
  | RootP -> k old_val
  | DotP (path', a) ->
    render_path path' old_val (fun old_val ->
      "(* TODO: Coq need a bit more help for dealing with records \n" ^
     "  {" ^ old_val ^ " with " ^  render_field_name None a ^ " := " ^ k (render_dot old_val a) ^ " }" ^ " *)" ^
     old_val
    )
  | IdxP (path', idx_exp) ->
    render_path path' old_val (fun old_val ->
      "(list_update " ^ old_val ^ " " ^ render_exp idx_exp ^ " " ^ k (render_idx old_val idx_exp) ^ ")"
    )
  | SliceP (_path', _e1, _e2) ->
      "default_val (* TODO *)"


and render_case a e typ =
    if e.it = TupE []
    then render_con_name' typ a
    else render_con_name' typ a $$ render_exp e

and render_lam v e = match e.it with
  | CallE (f, {it = VarE v2;_}) when v.it = v2.it -> render_fun_id f
  | _ -> "(fun " ^ render_id v ^ " => " ^ render_exp e ^ ")"

let render_succ_pattern e_string (n: int) = 
  (String.concat "" (List.init n (fun _ -> "(S "))) ^ "(" ^ e_string ^ ")" ^ (String.concat "" (List.init n (fun _ -> ")")))

let rec render_pattern (pat : exp) = match pat.it with
  | VarE v -> render_id v
  | BoolE true -> "True"
  | BoolE false -> "Frue"
  | NatE n -> string_of_int n
  | TextE t -> "\"" ^ String.escaped t ^ "\""
  | MixE (_, e) -> render_pattern e
  | TupE es -> render_tuple render_pattern es
  | ListE es -> render_list render_pattern es
  | OptE None -> "None"
  | OptE (Some e) -> "Some" $$ render_pattern e
  | TheE e  -> "(* TODO: what is TheE? *) " ^ render_pattern e
  | IterE (e, (_iter, vs)) -> begin match e.it with
    (* Short-ciruit v*; use variable directly instead of calling map *)
    | VarE v when [v.it] = List.map (fun (v : id) -> v.it) vs -> render_id v
    | _ -> "default_val (* FIXME: Unsupported match pattern " ^ Il.Print.string_of_exp pat ^ " *)"
  end
  | CaseE (a, e) -> render_case a e pat.note
  | SubE _ -> error pat.at "SubE encountered. Did the SubE elimination pass run?"
  | IdxE (e1, e2) -> render_idx (render_pattern e1) e2
  | BinE (AddOp _, e1, e2) -> begin match e2.it with 
                            | NatE n -> render_succ_pattern (render_pattern e1) n
                            | _ -> render_pattern e1 ^ "(* FIXME: Unsupported match pattern " ^ Il.Print.string_of_exp pat ^ " *)"
                            end
  | _ -> "default_val (* FIXME: Unsupported match pattern " ^ Il.Print.string_of_exp pat ^ " *)"

let render_clause (_id : id) (clause : clause) = match clause.it with
  | DefD (_binds, lhs, rhs, premise) ->
   (if premise <> [] then "(* Premises ignored! *) \n" else "") ^
   "\n  | " ^ render_pattern lhs ^ " => " ^ render_exp rhs

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
        "(List.Forall (fun " ^ render_id v ^ " => " ^ render_prem prem ^ ") (option_to_list " ^ render_id v ^ "))"
      | Opt, [v1; v2] ->
        "(List.Forall2 (fun " ^ render_id v1 ^ " " ^ render_id v2 ^ " => " ^ render_prem prem ^ ") (option_to_list " ^ render_id v1 ^ ") (option_to_list " ^ render_id v2 ^ "))"
      | iter, vs -> render_prem prem ^ "(* " ^ render_iterexp iter vs ^ " *)"
    end
    | ElsePr -> error prem.at "ElsePr encountered. Did the SubE elimination pass run?"
    | LetPr (_e1, _e2, _ids) -> (* TODO: don't really know a good example of this *) "default_val (*TODO*)"

let is_simple_constructor ((_, (_binds, ty, _prems), _): typcase) : bool = (ty.it = TupT [])

let get_inhabitance_proof id cases : string =
  "Global Instance Inhabited_" ^ render_type_name id ^ " : Inhabited " ^ render_type_name id ^ 
  let simple_constructors = List.filter is_simple_constructor cases in
  match simple_constructors with
  | [] -> "(* FIXME: no inhabitant found! *) .\n" ^
          "  Admitted"
  | (con, _, _) :: _ -> " := { default_val := " ^ render_con_name id con ^ " }"

let render_record_inhabitance_proof type_string fields : string =
  "Global Instance Inhabited_" ^ type_string ^ " : Inhabited " ^ type_string ^ " := \n" ^
  "{default_val := {|\n" ^
      String.concat "" (List.map (fun (a, _ty, _hints) -> 
        "  " ^ type_string ^ "__" ^ render_field_name None a ^ " := default_val ;\n"
        ) fields) ^ "|} }. \n\n"

let rec get_id_used (rhs: exp) : id list = match rhs.it with
  | VarE _v -> []
  | BoolE true -> []
  | BoolE false -> []
  | NatE _n -> []
  | TextE _t -> []
  | MixE (_, e) -> get_id_used e
  | TupE es -> List.concat (List.map get_id_used es)
  | ListE es -> List.concat (List.map get_id_used es)
  | OptE None -> []
  | OptE (Some e) -> get_id_used e
  | TheE e  -> get_id_used e
  | IterE (e, (_iter, vs)) -> begin match e.it with
    (* Short-ciruit v*; use variable directly instead of calling map *)
    | VarE v when [v.it] = List.map (fun (v : id) -> v.it) vs -> []
    | _ -> get_id_used e
  end
  | CaseE (_a, e) -> get_id_used e
  | StrE fields -> List.concat (List.map (fun (_a, e) -> get_id_used e) fields)
  | SubE _ -> error rhs.at "SubE encountered. Did the SubE elimination pass run?"
  | DotE (e, _a) -> get_id_used e
  | UpdE (exp1, _path, exp2) -> get_id_used exp1 @ get_id_used exp2
  | ExtE (exp1, _path, exp2) -> get_id_used exp1 @ get_id_used exp2
  | IdxE (e1, e2) -> get_id_used e1 @ get_id_used e2
  | LenE e -> get_id_used e
  | CallE (id, e) -> [id] @ get_id_used e
  | UnE (MinusOp _typ, e1)      -> get_id_used e1
  | BinE (AddOp _typ, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (SubOp _typ, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (ExpOp _typ, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (DivOp _typ, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (AndOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (EquivOp, e1, e2) -> get_id_used e1 @ get_id_used e2
  | BinE (OrOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (EqOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (NeOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (LeOp _typ, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (LtOp _typ, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (GeOp _typ, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (GtOp _typ, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CatE (e1, e2)          -> get_id_used e1 @ get_id_used e2
  | CompE (e1, e2)         -> get_id_used e1 @ get_id_used e2
  | _ -> []

let get_id_used_list (clauses: clause list) : id list =
  List.concat (List.map (fun (cl: clause) -> match cl.it with | DefD (_binds, _lhs, rhs, _premise) -> get_id_used rhs) clauses)

let is_recursive (i: id) (clauses: clause list) : bool =
  let ids = get_id_used_list clauses in
  List.exists (fun (id': id) -> i.it = id'.it) ids

let rec render_def (mutrec_qual: bool) (d : def) =
  match d.it with
  | SynD (id, deftyp) ->
    show_input d ^
    begin match deftyp.it with
    | AliasT ty ->
      "(** Alias definition : " ^ render_type_name id ^ " **)\n" ^
      "Definition " ^ render_type_name id ^ " := " ^ render_typ ty
    | NotationT (_mop, ty) ->
      "(** Notation definition : " ^ render_type_name id ^ " **)\n" ^
      "Definition " ^ render_type_name id ^ " := (* mixop: " (* TODO: add it back after escaping round brackets ^ Il.Print.string_of_mixop mop *) ^ " *) " ^ render_typ ty
    | VariantT cases ->
      "(** Variant definition : " ^ render_type_name id ^ " **)\n" ^
      "Inductive " ^ render_type_name id ^ " : Type :=" ^ String.concat "" (
        List.map (fun case -> "\n | " ^ render_variant_case id case) cases
      ) ^ "\n.\n" ^ get_inhabitance_proof id cases
    | StructT fields ->
      let type_string = render_type_name id in
      "(** Record definition : " ^ type_string ^ " **)\n" ^
      "Record " ^ type_string ^ " : Type := {" ^
      String.concat "" ( List.map (fun (a, (_binds, ty, _prems), _hints) ->
        "\n  " ^ render_field_name (Some id) a ^ " : " ^ render_typ ty ^ ";"
      ) fields) ^
      "\n }. \n\n" ^
      render_record_inhabitance_proof type_string fields ^
      "\n\n" ^
      "Definition _append_" ^ type_string ^ " (r1 r2: " ^ type_string ^ ") : " ^ type_string ^ " :=\n" ^
      "{|\n" ^
      String.concat "" (List.map (fun (a, _ty, _hints) -> 
        "  " ^ render_field_name (Some id) a ^ " := r1.(" ^ render_field_name (Some id) a ^ ") ++ r2.(" ^ render_field_name (Some id) a ^ ");\n"
        ) fields) ^ "|}. \n\n" ^
      "Global Instance Append_" ^ type_string ^ " : Append " ^ type_string ^ " := { _append arg1 arg2 := _append_" ^ type_string ^ " arg1 arg2 }" 
    end
  | DecD (id, typ1, typ2, clauses) ->
    show_input d ^
    "(** Function definition : " ^ render_fun_id id ^ " **)\n" ^
    "(* Dependencies: " ^ String.concat ", " (List.map render_id (get_id_used_list clauses)) ^ " *)\n" ^
    if is_recursive id clauses then "Fixpoint " ^ render_fun_id id ^ " (arg: " ^ render_typ typ1 ^ ") : " ^ render_typ typ2 ^ ".\n" ^
    "(* FIXME: Generated fixpoint definitions are fragile and may not directly pass the termination check. The following code is an attempt at rendering:\n" ^
    "  := match arg with" ^
     (if clauses = [] then "\n  | _ => default_val" else
    String.concat "" (List.map (render_clause id) clauses)) ^
    "\nend *)\nAdmitted"(* Could use no_error_if_unused% as well *)
    else "Definition " ^ render_fun_id id ^ " (arg: " ^ render_typ typ1 ^ ") : " ^ render_typ typ2 ^ " :=\n" ^
    "  match arg with" ^
     (if clauses = [] then "\n  | _ => default_val" else
    String.concat "" (List.map (render_clause id) clauses)) ^
    "\nend"
    

  | RelD (id, _mixop, typ, rules) ->
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

let parse_record_fields (d: def) =
  match d.it with
  | SynD (id, deftyp) ->
    begin match deftyp.it with
    | StructT fields ->
      let type_id = id in
      let fields_name = String.concat "" (List.map (fun (a, _ty, _hints) -> render_field_name None a) fields) in
      (fields_name, Some type_id)
    | _ -> ("", None)
    end
  | _ -> ("", None)

let build_record_helper (el: script) =
  let _ = List.fold_left 
          (fun _ (record_fields_name, otype_id) -> 
            match otype_id with 
            | Some type_id -> (Hashtbl.add record_helper record_fields_name type_id)
            | None -> ()) 
          () (List.map parse_record_fields el) in 
          ()

let render_script (el : script) =
  let _ = build_record_helper el in 
  String.concat ".\n\n" (List.map (render_def false) (List.filter is_non_hint el)) ^ "."

let gen_string (el : script) =
  "(* Coq export *)\n\n" ^
  "From Coq Require Import String List Unicode.Utf8.\n" ^
  "Require Import NArith.\n" ^
  "\n" ^
  "Set Implicit Arguments.\n" ^
  "Unset Strict Implicit.\n" ^
  "Unset Printing Implicit Defensive.\n" ^
  "\n\n" ^
  "(** * Auxiliary definitions **)\n" ^
  "\n" ^
  "Declare Scope wasm_scope.\n\n" ^
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
  "Class Append (α: Type) := _append : α -> α -> α.\n\n" ^
  "Infix \"++\" := _append (right associativity, at level 60) : wasm_scope.\n\n" ^
  "Global Instance Append_List_ {α: Type}: Append (list α) := { _append l1 l2 := List.app l1 l2 }.\n\n" ^
  "Definition option_append {α: Type} (x y: option α) : option α :=\n" ^
  " match x with\n" ^
  "  | Some _ => x\n" ^
  "  | None => y\n" ^
  "end.\n\n" ^
  "Global Instance Append_Option {α: Type}: Append (option α) := { _append o1 o2 := option_append o1 o2 }.\n\n" ^
  "Fixpoint list_update {α: Type} (l: list α) (n: nat) (y: α): list α :=\n" ^
  "match l, n with\n" ^
  "  | nil, _=> nil\n" ^
  "  | x :: l', 0 => y :: l'\n" ^
  "  | x :: l', S n => x :: list_update l' n y\n" ^
  "end.\n\n" ^
  "Class Inhabited (T: Type) := { default_val : T }.\n\n" ^
  "Definition lookup_total {T: Type} {_: Inhabited T} (l: list T) (n: nat) : T :=\n" ^
  "  List.nth n l default_val.\n\n" ^
  "Global Instance Inh_unit : Inhabited unit := { default_val := tt }.\n\n" ^
  "Global Instance Inh_nat : Inhabited nat := { default_val := O }.\n\n" ^
  "Global Instance Inh_list {T: Type} : Inhabited (list T) := { default_val := nil }.\n\n" ^
  "Global Instance Inh_option {T: Type} : Inhabited (option T) := { default_val := None }.\n\n" ^
  "Global Instance Inh_prod {T1 T2: Type} {_: Inhabited T1} {_: Inhabited T2} : Inhabited (prod T1 T2) := { default_val := (default_val, default_val) }.\n\n" ^
  "Open Scope wasm_scope.\n" ^
  "Import ListNotations.\n" ^
  "\n" ^
  "(** * Generated code **)\n" ^
  "\n" ^
  render_script el


let gen_file file el =
  let coq_code = gen_string el in
  let oc = Out_channel.open_text file in
  Fun.protect (fun () -> Out_channel.output_string oc coq_code)
    ~finally:(fun () -> Out_channel.close oc)
