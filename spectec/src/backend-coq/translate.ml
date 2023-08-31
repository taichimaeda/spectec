open Il.Ast

let error at msg = Util.Source.error at "Lang generation" msg

(* an ugly solution given the constraints *)
(*
let record_helper = Hashtbl.create 16
*)

let include_input = false

let parens s = "(" ^ s ^ ")"
let brackets s = "[" ^ s ^ "]"
let ($$$) s1 ss = parens (String.concat " " (s1 :: ss))
let ($$) s1 s2 = s1 $$$ [s2]
let translate_tuple how tys = 
  if tys = [] then "tt"
  else parens (String.concat ", " (List.map how tys))
let translate_list how tys = 
  if tys = [] then "nil"
  else brackets (String.concat "; " (List.map how tys))

let escape (s: string) : string =
  match s with
  | "in" -> "In"
  | _ -> s

let make_id (s: string) : string = 
  escape (String.lowercase_ascii (match s with
  | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s))


let translate_id (id : id) : Lang.ident = 
  if id.it = "" then "NONAME"
  else make_id id.it

let translate_id_note (id : id) (note: typ) : Lang.ident = 
  "(* Annotated *)"^
  (match note.it with
  | VarT t_id -> make_id (t_id.it) ^ "__"
  | _ -> "")
  ^
  (if id.it = "" then "NONAME"
  else make_id id.it)

let translate_note (note: typ) : Lang.ident =
  match note.it with
  | VarT id -> make_id id.it
  | _ -> "(* error: unexpected constructor notation :" ^ Il.Print.string_of_typ note ^ "*)"

let translate_id_exp (id: id): Lang.term = Lang.IdentE (translate_id id)

let translate_fun_id (id : id) : Lang.ident = translate_id id

let translate_type_name (id : id) : Lang.ident = make_id (String.capitalize_ascii id.it)

let translate_rule_id ty_id (rule_id : id) :  string =
  translate_type_name ty_id ^ "__" ^
  if rule_id.it = ""
  then "noname"
  else make_id rule_id.it

let translate_atom : atom -> Lang.ident = function
  | Atom s -> make_id s
  | a -> "(* translate_con_name: TODO *) " ^ Il.Print.string_of_atom a

let translate_atom_note (a: atom) (note: typ) : Lang.ident = match a with
  | Atom s -> (translate_note note) ^ "__" ^ (make_id s)
  | a -> "(* translate_con_name: TODO *) " ^ Il.Print.string_of_atom a

let translate_atom_exp (a: atom) : Lang.term = Lang.IdentE (translate_atom a)

let translate_con_name tid : atom -> string = function
  | Atom s -> translate_id tid ^ "__" ^ make_id s
  | a -> translate_id tid ^ "__" ^ "(* translate_con_name: TODO *) " ^ Il.Print.string_of_atom a

  (*
let translate_con_name' (typ : typ) a = match typ.it with
  | VarT _id -> translate_con_name a
  | _ -> "_ (* translate_con_name': Typ not id *)"
*)

let translate_field_name oty_id (at: atom) : string = 
  begin match oty_id with
  | Some ty_id -> translate_type_name ty_id ^ "__"
  | None -> ""
  end ^
  match at with
  | Atom s -> make_id s
  | a -> "(* translate_field_name: TODO *) " ^ Il.Print.string_of_atom a


let wrap_type_iter (ty : Lang.typ) : iter -> Lang.typ = function
  | Opt -> Lang.OptionT ty
  |  _  -> Lang.ListT ty

let wrap_type_iters (ty : Lang.typ) : iter list -> Lang.typ = List.fold_left wrap_type_iter ty

let rec translate_typ (ty : typ) : Lang.typ = 
  match ty.it with
  | VarT id -> Lang.TermT (translate_type_name id)
  | BoolT -> BoolBT
  | NatT -> NatBT
  | TextT -> StringBT
  | TupT [] -> UnitBT
  | TupT tys -> Lang.TupleT (List.map translate_typ tys)
  | IterT (ty, it) -> wrap_type_iter (translate_typ ty) it

let translate_variant_case _id ((a, ty, _hints) : typcase) : Lang.type_constructor =
  match ty.it with
  | TupT tys -> (translate_atom a, List.map (translate_typ) tys)
  | _ -> (translate_atom a, [translate_typ ty])
  
  (*
let infer_record_name ats = 
  let fields_name = String.concat "" (List.map (fun a -> translate_field_name None a) ats) in
  Hashtbl.find_opt record_helper fields_name
  *)

let rec translate_exp (e0: exp) : Lang.term = match e0.it with
  | VarE v -> Lang.IdentE (translate_id v)
  | BoolE b -> Lang.BasicE (Lang.BoolBE b)
  | NatE n -> Lang.BasicE (Lang.NatBE n)
  | TextE t -> Lang.BasicE (Lang.StringBE (String.escaped t))
  | MixE (_, e) -> translate_exp e (* TODO: check *)
  | TupE es -> Lang.BasicE (Lang.TupE (List.map translate_exp es))
  | ListE es -> Lang.BasicE (Lang.ListE (List.map translate_exp es))
  | OptE None -> Lang.BasicE (Lang.OptionE None)
  | OptE (Some e) -> Lang.BasicE (Lang.OptionE (Some (translate_exp e)))
  | TheE e  -> error e.at "TheE encountered." (*translate_exp e (* TODO: check *)*)
  | IterE (e, (iter, vs)) -> 
    begin match e.it with
    (* Short-ciruit v*; use variable directly instead of calling map *)
    | VarE v when [v.it] = List.map (fun (v : id) -> v.it) vs -> Lang.IdentE (translate_id v)
    | _ -> match iter, vs with
      | (List|List1|ListN _), [] ->
        Lang.BasicE (Lang.ListE [translate_exp e])
      | (List|List1|ListN _), [v] ->
        begin
        match e.it with
        | CallE (f, {it = VarE v2;_}) when v.it = v2.it -> Lang.BasicE (Lang.ListMapE (([], translate_id_exp f), translate_id_exp v))
        | _ -> Lang.BasicE (Lang.ListMapE (([translate_id v], translate_exp e), Lang.IdentE (translate_id v))) (* TODO: check arguments *)
        end
    (*    "List.map" $$$ [translate_lam v e; translate_id v] *)
      | (List|List1|ListN _), [v1; v2] ->
        Lang.BasicE (Lang.ListZipE (([translate_id v1; translate_id v2], translate_exp e), translate_id_exp v1, translate_id_exp v2))
    (*    "List.zipWith" $$$ [ "(fun " ^ translate_id v1 ^ " " ^ translate_id v2 ^ " => " ^ translate_exp e ^ ")"; translate_id v1; translate_id v2 ]*)
      | Opt, [] -> Lang.BasicE (Lang.OptionE (Some (translate_exp e)))
      | Opt, [v] -> 
        begin
        match e.it with
        | CallE (f, {it = VarE v2;_}) when v.it = v2.it -> Lang.BasicE (Lang.OptionMapE (([], (translate_id_exp f)), translate_id_exp v))
        | _ -> Lang.BasicE (Lang.OptionMapE (([translate_id v], translate_exp e), Lang.IdentE (translate_id v))) (* TODO: check arguments *)
        end
    (*   "Option.map" $$$ [translate_lam v e; translate_id v] *)
      | Opt, [v1; v2] ->
        Lang.BasicE (Lang.OptionZipE (([translate_id v1; translate_id v2], translate_exp e), translate_id_exp v1, translate_id_exp v2))
       (* "option_zip" $$$ [ "(fun " ^ translate_id v1 ^ " " ^ translate_id v2 ^ " => " ^ translate_exp e ^ ")"; translate_id v1; translate_id v2 ] *)
      | _, _ ->
      (* translate_exp e ^ " (* " ^ Il.Print.string_of_iterexp (iter, vs) ^ " *)" *)
      Lang.UnsupportedE "" (*(" (* " ^ Il.Print.string_of_iterexp (iter, vs) ^ " *)")*)
    end
  (* TODO: add type information *)
  | CaseE (a, e) -> Lang.AppE (("(*case_exp*)" ^ translate_atom_note a e0.note), ([translate_exp e])) 
  | StrE fields -> Lang.BasicE (Lang.RecordE (List.map (fun (a, e) -> (translate_atom a, translate_exp e)) fields))
   (* let o_record_name = infer_record_name (List.map fst fields) in
    (if o_record_name = None then "(* FIXME: cannot infer the type of record *) " else "") ^
    "{| " ^ ( String.concat "; " (List.map (fun (a, e) ->
    translate_field_name o_record_name a ^ " := " ^ translate_exp e
    ) fields)) ^ " |}" *)
  | SubE _ -> error e0.at "SubE encountered. Did the SubE elimination pass run?"
  | DotE (e, a) -> Lang.BasicE (Lang.GetFieldE ((translate_exp e), (translate_atom a)))
  | UpdE (exp1, path, exp2) ->
    translate_path path (translate_exp exp1) (fun _ -> translate_exp exp2)
  | ExtE (exp1, path, exp2) ->
    translate_path path (translate_exp exp1) (fun old_val -> Lang.BasicE (Lang.ListCatE (old_val, translate_exp exp2)))
  | IdxE (e1, e2) -> Lang.BasicE (Lang.ListGetE ((translate_exp e1), (translate_exp e2)))
  | LenE e -> Lang.BasicE (Lang.ListLenE (translate_exp e))
  | CallE (id, e) -> Lang.AppE ((translate_fun_id id), [translate_exp e])
  | UnE (MinusOp, e1)      -> Lang.BasicE (Lang.UnopE (Lang.MinusE, (translate_exp e1)))
  | BinE (AddOp, e1, e2)   -> Lang.BasicE (Lang.BinopE (Lang.AddE, translate_exp e1, translate_exp e2))
  | BinE (SubOp, e1, e2)   -> Lang.BasicE (Lang.BinopE (Lang.SubE, translate_exp e1, translate_exp e2))
  | BinE (ExpOp, e1, e2)   -> Lang.BasicE (Lang.BinopE (Lang.ExpE, translate_exp e1, translate_exp e2))
  | BinE (DivOp, e1, e2)   -> Lang.BasicE (Lang.BinopE (Lang.DivE, translate_exp e1, translate_exp e2))
  | BinE (AndOp, e1, e2)   -> Lang.BasicE (Lang.BinopE (Lang.AndE, translate_exp e1, translate_exp e2))
  | BinE (EquivOp, e1, e2) -> Lang.BasicE (Lang.BinopE (Lang.EquivE, translate_exp e1, translate_exp e2))
  | BinE (OrOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.OrE, translate_exp e1, translate_exp e2))
  | CmpE (EqOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.EqE, translate_exp e1, translate_exp e2))
  | CmpE (NeOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.NeqE, translate_exp e1, translate_exp e2))
  | CmpE (LeOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.LeE, translate_exp e1, translate_exp e2))
  | CmpE (LtOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.LtE, translate_exp e1, translate_exp e2))
  | CmpE (GeOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.GeE, translate_exp e1, translate_exp e2))
  | CmpE (GtOp, e1, e2)    -> Lang.BasicE (Lang.BinopE (Lang.GtE, translate_exp e1, translate_exp e2))
  | CatE (e1, e2)          -> Lang.BasicE (Lang.ListCatE (translate_exp e1, translate_exp e2))
  | CompE (e1, e2)         -> Lang.BasicE (Lang.ListCompE (translate_exp e2, translate_exp e1)) (* NB! flip order *)
  | _ -> Lang.UnsupportedE ("Unknown exp: " ^ Il.Print.string_of_exp e0 ^ "")

  (*
and translate_dot e_string a = e_string ^ "." ^ parens (translate_field_name None a)

and translate_get_field e_string record_string a = e_string ^ "." ^ parens (record_string ^ "__" ^ translate_field_name None a)

and translate_idx e_string exp = parens ("lookup_total " ^ e_string ^ " " ^ translate_exp exp)
*)

(* The path is inside out, in a way, hence the continuation passing style here *)
and translate_path (path : path) (old_val: Lang.term) (acc : Lang.term -> Lang.term) : Lang.term = match path.it with
  | RootP -> acc old_val
  | DotP (path', a) ->
    translate_path path' old_val (fun old_val ->
      Lang.BasicE (Lang.SetFieldE (old_val, (translate_atom a), acc (Lang.BasicE (Lang.GetFieldE (old_val, translate_atom a))))))
   (*   "(* TODO: need a bit more help for dealing with records \n" ^
     "  {" ^ old_val ^ " with " ^  translate_field_name None a ^ " := " ^ k (translate_dot old_val a) ^ " }" ^ " *)" ^
     old_val
    )*)
  | IdxP (path', idx_exp) ->
    translate_path path' old_val 
    (fun old_val -> Lang.BasicE (Lang.ListSetE (old_val, (translate_exp idx_exp), acc (Lang.BasicE (Lang.ListGetE (old_val, translate_exp idx_exp))))))
  (*  translate_path path' old_val (fun old_val ->
      "(list_update " ^ old_val ^ " " ^ translate_exp idx_exp ^ " " ^ k (translate_idx old_val idx_exp) ^ ")" 
    )*)
  | SliceP (_path', _e1, _e2) ->
    Lang.UnsupportedE "SliceP" (* TODO: check *)

(*
and translate_case a (e: exp) typ =
    if e.it = TupE []
    then translate_con_name' typ a
    else translate_con_name' typ a $$ translate_exp e


and translate_lam v (e: exp) : Lang.term = 
  match e.it with
 (* | CallE (f, {it = VarE v2;_}) when v.it = v2.it -> translate_fun_id f *)
  | _ -> Lang.BasicE (Lang.LambdaE ((translate_id v), (translate_exp e)))
*)

let rec translate_succ_pattern pat (n: int): Lang.pattern = 
  if n <= 0 then pat
  else Lang.AppP ("S", [(translate_succ_pattern pat (n-1))])

  (*(String.concat "" (List.init n (fun _ -> "(S "))) ^ "(" ^ e_string ^ ")" ^ (String.concat "" (List.init n (fun _ -> ")")))*)

let rec translate_pattern (pat : exp) = 
  match pat.it with
  | VarE v -> Lang.IdentP ("(*var_pat*)" ^ translate_id v)
  | BoolE b -> Lang.BasicP (Lang.BoolBP b)
  | NatE n -> Lang.BasicP (Lang.NatBP n)
  | TextE t -> Lang.BasicP (Lang.StringBP ("(*string_pat*)" ^ String.escaped t))
  | MixE (_, e) -> translate_pattern e (* TODO: check *)
  | TupE es -> Lang.BasicP (Lang.TupP (List.map translate_pattern es))
  | ListE es -> Lang.ListP (List.map translate_pattern es) (* TODO: check *)
  | OptE None -> Lang.OptionP None
  | OptE (Some e) -> Lang.OptionP (Some (translate_pattern e))
  | TheE e  -> (* TODO: check *) translate_pattern e
  | IterE (e, (_iter, vs)) -> 
    begin match e.it with
    (* Short-ciruit v*; use variable directly instead of calling map *)
    | VarE v when [v.it] = List.map (fun (v : id) -> v.it) vs -> Lang.IdentP ("(* test_iter_pat *)"^translate_id v)
    | _ -> Lang.UnsupportedP ("Unsupported match pattern " ^ Il.Print.string_of_exp pat)
    end
  | CaseE (a, e) -> Lang.AppP (("(*case_pat*)"^translate_atom_note a pat.note), ([translate_pattern e]))
  | SubE _ -> error pat.at "SubE encountered. Did the SubE elimination pass run?"
 (* | IdxE (e1, e2) -> Lang.Unspported translate_idx (translate_pattern e1) e2 *)
  | BinE (AddOp, e1, e2) ->
    (begin match e2.it with 
    | NatE n -> translate_succ_pattern (translate_pattern e1) n
    | _ -> Lang.UnsupportedP ("Unsupported match pattern " ^ Il.Print.string_of_exp pat)
    end)
  | _ -> Lang.UnsupportedP ("Unsupported match pattern " ^ Il.Print.string_of_exp pat)

let rec add_note (e: exp) (note_typ: typ) : exp = 
  match e.it with
  | TheE e' -> 
    let e'_res = TheE (add_note e' note_typ) in
    { at = e.at; it = e'_res; note = note_typ }
  | _ -> { at= e.at; it = e.it; note = note_typ }

let translate_clause (_typ1: typ) (typ2: typ) (clause : clause) = 
  match clause.it with
  | DefD (_binds, lhs, rhs, _premise) ->
    (translate_pattern lhs, translate_exp (add_note rhs typ2))

let show_input (d : def) =
    if include_input then
    "(* " (*  ^ Util.Source.string_of_region d.at ^ "\n"*)  ^
    Il.Print.string_of_def d ^
    "\n*)\n"
    else ""

let rec translate_prem (prem : premise): Lang.term =
    match prem.it with
    | RulePr (pid, _mixops, pexp) -> (Lang.AppE (translate_type_name pid, [translate_exp pexp]))
    | IfPr (pexp) -> translate_exp pexp
    | IterPr (prem, iterexp) ->
      begin match iterexp with
      | (List|List1|ListN _), [v] ->
        Lang.BasicE (Lang.ListForallE (([translate_id v], translate_prem prem), translate_id_exp v))
   (*     "(List.Forall (fun " ^ translate_id v ^ " => " ^ translate_prem prem ^ ") " ^ translate_id v ^ ")" *)
      | (List|List1|ListN _), [v1; v2] ->
        Lang.BasicE (Lang.ListForall2E (([translate_id v1; translate_id v2], translate_prem prem), translate_id_exp v1, translate_id_exp v2))
   (*     "(List.Forall2 (fun " ^ translate_id v1 ^ " " ^ translate_id v2 ^ " => " ^ translate_prem prem ^ ") " ^ translate_id v1 ^ " " ^ translate_id v2 ^ ")"*)
      | Opt, [v] ->
        Lang.BasicE (Lang.OptionMapE (([translate_id v], translate_prem prem), translate_id_exp v))
   (*     "(List.Forall (fun " ^ translate_id v ^ " => " ^ translate_prem prem ^ ") (option_to_list " ^ translate_id v ^ "))"*)
      | Opt, [v1; v2] ->
        Lang.BasicE (Lang.OptionZipE (([translate_id v1; translate_id v2], translate_prem prem), translate_id_exp v1, translate_id_exp v2))
   (*     "(List.Forall2 (fun " ^ translate_id v1 ^ " " ^ translate_id v2 ^ " => " ^ translate_prem prem ^ ") (option_to_list " ^ translate_id v1 ^ ") (option_to_list " ^ translate_id v2 ^ "))"*)
      | _,_ -> 
        Lang.UnsupportedE ""(*(Il.Print.string_of_iterexp iterexp)*)
      end
    | ElsePr -> error prem.at "ElsePr encountered. Did the Else elimination pass run?"
    | LetPr (_exp1, _exp2) -> Lang.UnsupportedE "" (* TODO: check *)
    | NegPr prem -> Lang.BasicE (Lang.UnopE (Lang.NotE, translate_prem prem))

let translate_field tid ((a, ty, _hints): typcase) : Lang.record_constructor =
  (translate_con_name tid a, translate_typ ty)

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
  | UnE (MinusOp, e1)      -> get_id_used e1
  | BinE (AddOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (SubOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (ExpOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (DivOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (AndOp, e1, e2)   -> get_id_used e1 @ get_id_used e2
  | BinE (EquivOp, e1, e2) -> get_id_used e1 @ get_id_used e2
  | BinE (OrOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (EqOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (NeOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (LeOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (LtOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (GeOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CmpE (GtOp, e1, e2)    -> get_id_used e1 @ get_id_used e2
  | CatE (e1, e2)          -> get_id_used e1 @ get_id_used e2
  | CompE (e1, e2)         -> get_id_used e1 @ get_id_used e2
  | _ -> []

let get_id_used_list (clauses: clause list) : id list =
  List.concat (List.map (fun (cl: clause) -> match cl.it with | DefD (_binds, _lhs, rhs, _premise) -> get_id_used rhs) clauses)

let is_recursive (i: id) (clauses: clause list) : bool =
  let ids = get_id_used_list clauses in
  List.exists (fun (id': id) -> i.it = id'.it) ids

let translate_binder b : Lang.binder =
  match b with
  | (bid, btyp, iters) -> (translate_id bid, wrap_type_iters (translate_typ btyp) iters)

(*
    show_input d ^
    "(** Relation definition : " ^ translate_type_name id ^ " **)\n" ^
    (if mutrec_qual then
      translate_type_name id ^ " : " ^ translate_typ typ ^ " -> Prop := "
    else "Inductive " ^ translate_type_name id ^ " : " ^ translate_typ typ ^ " -> Prop := ")
    ^
    String.concat "" (List.mapi (fun i (rule : rule) -> match rule.it with
      | RuleD (rule_id, binds, _mixop, exp, prems) ->
        "\n  | " ^ translate_rule_name id rule_id i ^ " " ^
        String.concat " " (List.map (fun ((bid : id), btyp, iters) ->
          parens (translate_id bid ^ " : " ^ wrap_type_iters (translate_typ btyp) iters)
          ) binds) ^ " : " ^
        String.concat "" (List.map (fun (prem : premise) ->
          "\n    " ^ translate_prem prem ^ " -> "
        ) prems) ^
          "\n    " ^ (translate_type_name id $$ translate_exp exp)
    ) rules) ^ "\n"
    *)

let translate_rule id (r : rule) =
  match r.it with
  | RuleD (rule_id, binds, _mixop, exp, prems) ->
      (
        translate_rule_id id rule_id, 
        (List.map translate_binder binds),
        (List.map translate_prem prems),
        (translate_exp exp)
      )

let rec translate_def (d : def): Lang.typedef =
  match d.it with
  | SynD (id, deftyp) ->
    begin match deftyp.it with
    | AliasT ty ->
    (*  "(** Alias definition : " ^ translate_type_name id ^ " **)\n" ^ 
      "Definition " ^ translate_type_name id ^ " := " ^ translate_typ ty *)
      Lang.TypeD ((translate_type_name id), (translate_typ ty))
    | NotationT (_mop, ty) ->
      (*"(** Notation definition : " ^ translate_type_name id ^ " **)\n" ^
      "Definition " ^ translate_type_name id ^ " := (* mixop: " (* TODO: add it back after escaping round brackets ^ Il.Print.string_of_mixop mop *) ^ " *) " ^ translate_typ ty *)
      Lang.TypeD ((translate_type_name id), (translate_typ ty))
    | VariantT cases ->
      (*"(** Variant definition : " ^ translate_type_name id ^ " **)\n" ^
      "Inductive " ^ translate_type_name id ^ " : Type :=" ^ String.concat "" (
        List.map (fun case -> "\n | " ^ translate_variant_case id case) cases
      ) ^ "\n.\n" ^ get_inhabitance_proof id cases*)
      Lang.IndTypeD ((translate_type_name id), (List.map (translate_variant_case id) cases))
    | StructT fields ->
      (*let type_string = translate_type_name id in
      "(** Record definition : " ^ type_string ^ " **)\n" ^
      "Record " ^ type_string ^ " : Type := {" ^
      String.concat "" ( List.map (fun (a, ty, _hints) ->
        "\n  " ^ translate_field_name (Some id) a ^ " : " ^ translate_typ ty ^ ";"
      ) fields) ^
      "\n }. \n\n" ^
      translate_record_inhabitance_proof type_string fields ^
      "\n\n" ^
      "Definition _append_" ^ type_string ^ " (r1 r2: " ^ type_string ^ ") : " ^ type_string ^ " :=\n" ^
      "{|\n" ^
      String.concat "" (List.map (fun (a, _ty, _hints) -> 
        "  " ^ translate_field_name (Some id) a ^ " := r1.(" ^ translate_field_name (Some id) a ^ ") ++ r2.(" ^ translate_field_name (Some id) a ^ ");\n"
        ) fields) ^ "|}. \n\n" ^
      "Global Instance Append_" ^ type_string ^ " : Append " ^ type_string ^ " := { _append arg1 arg2 := _append_" ^ type_string ^ " arg1 arg2 }"  *)
      Lang.RecordD ((translate_type_name id), (List.map (translate_field id) fields))
    end
  | DecD (id, typ1, typ2, clauses) ->
(*
    show_input d ^
    "(** Function definition : " ^ translate_fun_id id ^ " **)\n" ^
    "(* Dependencies: " ^ String.concat ", " (List.map translate_id (get_id_used_list clauses)) ^ " *)\n" ^
    if is_recursive id clauses then "Fixpoint " ^ translate_fun_id id ^ " (arg: " ^ translate_typ typ1 ^ ") : " ^ translate_typ typ2 ^ ".\n" ^
    "(* FIXME: Generated fixpoint definitions are fragile and may not directly pass the termination check. The following code is an attempt at translating:\n" ^
    "  := match arg with" ^
     (if clauses = [] then "\n  | _ => default_val" else
    String.concat "" (List.map (translate_clause id) clauses)) ^
    "\nend *)\nAdmitted"(* Could use no_error_if_unused% as well *)
    else "Definition " ^ translate_fun_id id ^ " (arg: " ^ translate_typ typ1 ^ ") : " ^ translate_typ typ2 ^ " :=\n" ^
    "  match arg with" ^
     (if clauses = [] then "\n  | _ => default_val" else
    String.concat "" (List.map (translate_clause id) clauses)) ^
    "\nend"*)
      Lang.FuncD 
        ((if (is_recursive id clauses) then Lang.RecF else Lang.NoRecF),
        (translate_fun_id id),
        (["arg", translate_typ typ1]),
        (translate_typ typ2),
        (Lang.MatchE ("arg", (List.map (translate_clause typ1 typ2) clauses))))
      

  | RelD (id, _mixop, typ, rules) ->
    (*
    show_input d ^
    "(** Relation definition : " ^ translate_type_name id ^ " **)\n" ^
    (if mutrec_qual then
      translate_type_name id ^ " : " ^ translate_typ typ ^ " -> Prop := "
    else "Inductive " ^ translate_type_name id ^ " : " ^ translate_typ typ ^ " -> Prop := ")
    ^
    String.concat "" (List.mapi (fun i (rule : rule) -> match rule.it with
      | RuleD (rule_id, binds, _mixop, exp, prems) ->
        "\n  | " ^ translate_rule_name id rule_id i ^ " " ^
        String.concat " " (List.map (fun ((bid : id), btyp, iters) ->
          parens (translate_id bid ^ " : " ^ wrap_type_iters (translate_typ btyp) iters)
          ) binds) ^ " : " ^
        String.concat "" (List.map (fun (prem : premise) ->
          "\n    " ^ translate_prem prem ^ " -> "
        ) prems) ^
          "\n    " ^ (translate_type_name id $$ translate_exp exp)
    ) rules) ^ "\n"
    *)
    Lang.IndRelD ((translate_fun_id id), (translate_typ typ), (List.map (translate_rule id) rules))

  | RecD defs ->
    (match defs with
    | [] -> error d.at "Mutual recursive definition cannot have an empty body"
    | [def] -> translate_def def 
    | _ -> Lang.MutualD (List.map translate_def defs)
    )

  | HintD _ -> Lang.UnsupportedD "HintDef"

let is_non_hint (d: def) : bool =
  match d.it with
  | HintD _ -> false
  | _ -> true

let translate_script (il : script) =
  (List.map translate_def (List.filter is_non_hint il))
