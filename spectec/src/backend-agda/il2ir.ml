module Translate = struct
  open Util.Source
  open Il

  type _env = unit

  let initial_env = ()
  let unsafe_str (i : string) : Ir.id = Id i

  let str i =
    unsafe_str
      (String.map (function '_' | '.' -> '-' | ';' -> ',' | c -> c) i)

  let tyid i = str ("ty-" ^ i.it)
  let id i = str i.it
  let funid i = str ("$" ^ i.it)

  let atom : Ast.atom -> Ir.id = function
    | Atom a -> str a
    | _ -> failwith __LOC__

  let record_id (exp : Ast.exp) =
    match exp.note with { it = VarT i; _ } -> tyid i | _ -> assert false

  let builtin_const name : Ir.exp = VarE (unsafe_str name)
  let builtin_unary name (e : Ir.exp) : Ir.exp = ApplyE (builtin_const name, e)

  let builtin_binary name (e1 : Ir.exp) (e2 : Ir.exp) : Ir.exp =
    ApplyE (ApplyE (builtin_const name, e1), e2)

  let builtin_infix name (e1 : Ir.exp) (e2 : Ir.exp) : Ir.exp =
    builtin_binary ("_" ^ name ^ "_") e1 e2

  let builtin_ternary name (e1 : Ir.exp) (e2 : Ir.exp) (e3 : Ir.exp) : Ir.exp =
    ApplyE (ApplyE (ApplyE (builtin_const name, e1), e2), e3)

  let rec typ env (t : Ast.typ) : Ir.exp =
    match t.it with
    | VarT n -> VarE (tyid n)
    | BoolT -> ConstE BoolC
    | NatT -> ConstE NatC
    | TextT -> ConstE TextC
    | TupT ts -> ProdE (List.map (typ env) ts)
    | IterT (t, Opt) -> MaybeE ((typ env) t)
    | IterT (t, (List | List1 | ListN _)) -> ListE ((typ env) t)

  let unop (op : Ast.unop) : Ir.exp -> Ir.exp =
    let opname =
      match op with NotOp -> "~" | PlusOp -> "+" | MinusOp -> "-"
    in

    builtin_unary opname

  let binop (op : Ast.binop) : Ir.exp -> Ir.exp -> Ir.exp =
    let opname =
      match op with
      | AndOp -> "/\\"
      | OrOp -> "\\/"
      | ImplOp -> "=>"
      | EquivOp -> "<=>"
      | AddOp -> "+"
      | SubOp -> "-"
      | MulOp -> "*"
      | DivOp -> "/"
      | ExpOp -> "^"
    in
    builtin_infix opname

  let cmpop (op : Ast.cmpop) : Ir.exp -> Ir.exp -> Ir.exp =
    let opname =
      match op with
      | EqOp -> "==="
      | NeOp -> "=/="
      | LtOp -> "<<"
      | GtOp -> ">"
      | LeOp -> "<="
      | GeOp -> ">="
    in
    builtin_infix opname

  let rec exp env (e : Ast.exp) : Ir.exp =
    match e.it with
    | VarE n -> VarE (id n)
    | BoolE b -> ConstE (Bool b)
    | NatE n -> ConstE (Nat n)
    | TextE t -> ConstE (Text t)
    | UnE (op, e) -> (unop op) (exp env e)
    | BinE (op, e1, e2) -> (binop op) (exp env e1) (exp env e2)
    | CmpE (op, e1, e2) -> (cmpop op) (exp env e1) (exp env e2)
    | IdxE (e1, e2) -> builtin_binary "idx" (exp env e1) (exp env e2)
    | SliceE (_e1, _e2, _e3) -> YetE ("SliceE: " ^ Print.string_of_exp e)
    | UpdE (e1, path, e2) -> update_path env path e1 (fun _ -> exp env e2)
    | ExtE (_e1, _p, _e2) -> YetE ("ExtE: " ^ Print.string_of_exp e)
    | StrE efs -> StrE (List.map (fun (f, e) -> (atom f, exp env e)) efs)
    | DotE (e1, a) -> DotE (exp env e1, record_id e1, atom a)
    | CompE (e1, e2) ->
        let (Ir.Id i) = record_id e1 in
        builtin_infix ("++" ^ i) (exp env e1) (exp env e2)
    | LenE e -> builtin_unary "length" (exp env e)
    | TupE es -> TupleE (List.map (exp env) es)
    | MixE (_op, e1) ->
        (exp env)
          e1 (* mixops arise only from notations, so they are identities *)
    | CallE (x, e) -> ApplyE (VarE (funid x), (exp env) e)
    | IterE (({ it = VarE v; _ } as e), (_, [ v' ])) when v.it = v'.it ->
        exp env e
    | IterE (e, (Opt, [])) -> builtin_unary "just" (exp env e)
    | IterE (e, ((List | List1 | ListN _), [])) -> ConsE (exp env e, NilE)
    | IterE (e, (Opt, [ v ])) ->
        builtin_binary "maybeMap" (FunE (id v, exp env e)) (VarE (id v))
    | IterE (e, ((List | List1 | ListN _), [ v ])) ->
        builtin_binary "map" (FunE (id v, exp env e)) (VarE (id v))
    | IterE (_e1, _iter) -> YetE ("IterE: " ^ Print.string_of_exp e)
    | OptE None -> VarE (str "nothing")
    | OptE (Some e) -> builtin_unary "just" (exp env e)
    | TheE e -> builtin_unary "maybeThe" (exp env e)
    | ListE es ->
        List.fold_right (fun e lst -> Ir.ConsE (exp env e, lst)) es Ir.NilE
    | CatE (e1, e2) -> builtin_infix "++" (exp env e1) (exp env e2)
    | CaseE (a, e) -> ApplyE (VarE (atom a), (exp env) e)
    | SubE (_e1, _t1, _t2) -> YetE ("SubE: " ^ Print.string_of_exp e)

  and update_path env path old_val (k : Ir.exp -> Ir.exp) =
    match path.it with
    | RootP -> k (exp env old_val)
    | DotP (p, a) ->
        update_path env p old_val (fun old_val' ->
            UpdE
              (old_val', atom a, k (DotE (old_val', record_id old_val, atom a))))
    | IdxP (p, e) ->
        update_path env p old_val (fun old_val' ->
            builtin_ternary "upd" old_val' (exp env e)
              (k (builtin_binary "idx" old_val' (exp env e))))
    | SliceP (_p, _e1, _e2) -> YetE "SliceP"

  let rec pat env (e : Ast.exp) : Ir.pat =
    match e.it with
    | VarE n -> VarP (id n)
    | BoolE b -> ConstP (Bool b)
    | NatE n -> ConstP (Nat n)
    | TextE t -> ConstP (Text t)
    | UnE (_op, _e2) -> YetP ("UnE: " ^ Print.string_of_exp e)
    | BinE (_op, _e1, _e2) -> YetP ("BinE: " ^ Print.string_of_exp e)
    | CmpE (_op, _e1, _e2) -> YetP ("CmpE: " ^ Print.string_of_exp e)
    | IdxE (_e1, _e2) -> YetP ("IdxE: " ^ Print.string_of_exp e)
    | SliceE (_e1, _e2, _e3) -> YetP ("SliceE: " ^ Print.string_of_exp e)
    | UpdE (_e1, _p, _e2) -> YetP ("UpdE: " ^ Print.string_of_exp e)
    | ExtE (_e1, _p, _e2) -> YetP ("ExtE: " ^ Print.string_of_exp e)
    | StrE _efs -> YetP ("StrE: " ^ Print.string_of_exp e)
    | DotE (_e1, _atom) -> YetP ("DotE: " ^ Print.string_of_exp e)
    | CompE (_e1, _e2) -> YetP ("CompE: " ^ Print.string_of_exp e)
    | LenE _e1 -> YetP ("LenE: " ^ Print.string_of_exp e)
    | TupE es -> TupleP (List.map (pat env) es)
    | MixE (_op, e1) ->
        (pat env)
          e1 (* mixops arise only from notations, so they are identities *)
    | CallE (_id, _e1) -> YetP ("CallE: " ^ Print.string_of_exp e)
    | IterE (_e1, _iter) -> YetP ("IterE: " ^ Print.string_of_exp e)
    | OptE _eo -> YetP ("OptE: " ^ Print.string_of_exp e)
    | TheE _e1 -> YetP ("TheE: " ^ Print.string_of_exp e)
    | ListE _es -> YetP ("ListE: " ^ Print.string_of_exp e)
    | CatE (_e1, _e2) -> YetP ("CatE: " ^ Print.string_of_exp e)
    | CaseE (a, e) -> CaseP (atom a, pat env e)
    | SubE (_e1, _t1, _t2) -> YetP ("SubE: " ^ Print.string_of_exp e)

  let typefield env (a, t, _hints) = (atom a, (typ env) t)

  let deftyp env x (dt : Ast.deftyp) : Ir.def =
    match dt.it with
    | AliasT ty -> DefD (tyid x, ConstE SetC, [ ([], (typ env) ty) ])
    | NotationT (_op, ty) -> DefD (tyid x, ConstE SetC, [ ([], (typ env) ty) ])
    | StructT tfs -> RecordD (tyid x, ConstE SetC, List.map (typefield env) tfs)
    | VariantT tcs ->
        DataD
          ( tyid x,
            ConstE SetC,
            List.map
              (fun (a, t, _hints) ->
                (atom a, [], [ (typ env) t ], Ir.VarE (tyid x)))
              tcs )

  let clause env (cls : Ast.clause) =
    let (DefD (_binds, p, e, premises)) = cls.it in
    match premises with
    | [] -> ([ (pat env) p ], (exp env) e)
    | _ :: _ -> failwith __LOC__

  let iterate_ty (ty : Ir.exp) : Ast.iter -> Ir.exp = function
    | Opt -> MaybeE ty
    | List | List1 | ListN _ -> ListE ty

  let rule env (rel : Ir.exp) (r : Ast.rule) =
    let (RuleD (x, bs, _op, e, ps)) = r.it in
    let binds bs =
      List.map
        (fun (x, t, iter) -> (id x, List.fold_left iterate_ty (typ env t) iter))
        bs
    in
    let rec premise (p : Ast.premise) : Ir.exp =
      match p.it with
      | RulePr (x, _op, e) -> ApplyE (VarE (tyid x), (exp env) e)
      | IfPr e -> (exp env) e
      | ElsePr ->
          failwith
            __LOC__ (* Apparently, this should be removed in the middlend *)
      | IterPr (p', (Opt, [ v ])) ->
          builtin_binary "maybeTrue" (FunE (id v, premise p')) (VarE (id v))
      | IterPr (p', ((List | List1 | ListN _), [ v ])) ->
          builtin_binary "forAll" (FunE (id v, premise p')) (VarE (id v))
      | IterPr (p', ((List | List1 | ListN _), [ v1; v2 ])) ->
          builtin_ternary "forAll2"
            (FunE (id v1, FunE (id v2, premise p')))
            (VarE (id v1))
            (VarE (id v2))
      | IterPr (_prem, _iter) -> YetE ("IterPr: " ^ "ITER")
    in

    let premises ps = List.map premise ps in
    ( (if x.it <> "" then id x else str "-"),
      binds bs,
      premises ps,
      Ir.ApplyE (rel, (exp env) e) )

  let rec def env (d : Ast.def) : Ir.def list =
    match d.it with
    | SynD (id, dt) -> [ deftyp env id dt ]
    | RelD (x, _op, ty, rules) ->
        [
          DataD
            ( tyid x,
              ArrowE ((typ env) ty, ConstE SetC),
              List.map (rule env (VarE (tyid x))) rules );
        ]
    | DecD (i, tin, tout, clss) ->
        [
          DefD
            ( funid i,
              ArrowE ((typ env) tin, (typ env) tout),
              List.map (clause env) clss );
        ]
    | RecD defs -> [ MutualD (script defs) ]
    | HintD _ -> []

  and script sc = List.concat_map (def initial_env) sc
end

let translate = Translate.script
