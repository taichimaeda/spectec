module Translate = struct
  open Util.Source
  open Il

  type env = { records_with_comp : Agda.id list; variants : (Ast.id * Ast.typcase list) list; relations : (Ast.id * Ast.rule list) list }

  let initial_env = { records_with_comp = []; variants = []; relations = [] }

  let add_record_with_comp env t =
    { env with records_with_comp = t :: env.records_with_comp }

  let add_variant env x tcs =
    { env with variants = (x, tcs) :: env.variants }

    let add_relation env r rules =
    { env with relations = (r, rules) :: env.relations }

  let id i = Agda.Id i.it
  let tyid i = Agda.TyId i.it
  let funid i = Agda.FunId i.it
  let builtin i = Agda.BuiltIn i

  let atom : Ast.atom -> Agda.id = function
    | Atom a -> Agda.Id a
    | _ -> failwith __LOC__

  let record_id (exp : Ast.exp) =
    match exp.note with { it = VarT i; _ } -> tyid i | _ -> assert false

  let builtin_const b : Agda.exp = VarE (builtin b)
  let builtin_unary b (e : Agda.exp) : Agda.exp = ApplyE (builtin_const b, e)

  let builtin_binary b (e1 : Agda.exp) (e2 : Agda.exp) : Agda.exp =
    ApplyE (ApplyE (builtin_const b, e1), e2)

  let builtin_infix b (e1 : Agda.exp) (e2 : Agda.exp) : Agda.exp =
    MixfixE (builtin b, [ e1; e2 ])

  let builtin_mixfix b (es : Agda.exp list) : Agda.exp = MixfixE (builtin b, es)

  let builtin_ternary b (e1 : Agda.exp) (e2 : Agda.exp) (e3 : Agda.exp) :
      Agda.exp =
    ApplyE (ApplyE (ApplyE (builtin_const b, e1), e2), e3)

  let rec typ env (t : Ast.typ) : Agda.exp =
    match t.it with
    | VarT n -> VarE (tyid n)
    | BoolT -> VarE (BuiltIn BoolB)
    | NatT -> VarE (BuiltIn NatB)
    | TextT -> VarE (BuiltIn TextB)
    | TupT ts -> ProdE (List.map (typ env) ts)
    | IterT (t, Opt) -> builtin_unary MaybeB (typ env t)
    | IterT (t, (List | List1 | ListN _)) -> builtin_unary ListB (typ env t)

  let rec exp env (e : Ast.exp) : Agda.exp =
    match e.it with
    | VarE n -> VarE (id n)
    | BoolE b -> LiteralE (BoolL b)
    | NatE n -> LiteralE (NatL n)
    | TextE t -> LiteralE (TextL t)
    | UnE (op, e) -> builtin_unary (UnOpB op) (exp env e)
    | BinE (op, e1, e2) -> builtin_infix (BinOpB op) (exp env e1) (exp env e2)
    | CmpE (op, e1, e2) -> builtin_infix (CmpOpB op) (exp env e1) (exp env e2)
    | IdxE (e1, _e2) -> builtin_binary LookupB (exp env e1) (YetE "idx")
    | SliceE (_e1, _e2, _e3) -> YetE ("SliceE: " ^ Print.string_of_exp e)
    | UpdE (e1, path, e2) -> update_path env path e1 (fun _ -> exp env e2)
    | ExtE (_e1, _p, _e2) -> YetE ("ExtE: " ^ Print.string_of_exp e)
    | StrE efs -> StrE (List.map (fun (f, e) -> (atom f, exp env e)) efs)
    | DotE (e1, a) -> DotE (exp env e1, record_id e1, atom a)
    | CompE (e1, e2) ->
        builtin_infix (CompB (record_id e1)) (exp env e1) (exp env e2)
    | LenE e -> builtin_unary LengthB (exp env e)
    | TupE es -> TupleE (List.map (exp env) es)
    | MixE (_op, e1) ->
        (exp env)
          e1 (* mixops arise only from notations, so they are identities *)
    | CallE (x, e) -> ApplyE (VarE (funid x), exp env e)
    | IterE (({ it = VarE v; _ } as e), (_, [ v' ])) when v.it = v'.it ->
        exp env e
    | IterE (e, (Opt, [])) -> builtin_unary JustB (exp env e)
    | IterE (e, ((List | List1 | ListN _), [])) ->
        builtin_infix ConsB (exp env e) (builtin_const NilB)
    | IterE (e, (Opt, [ v ])) ->
        builtin_binary MaybeMapB (FunE (id v, exp env e)) (VarE (id v))
    | IterE (e, ((List | List1 | ListN _), [ v ])) ->
        builtin_binary ListMapB (FunE (id v, exp env e)) (VarE (id v))
    | IterE (_e1, _iter) -> YetE ("IterE: " ^ Print.string_of_exp e)
    | OptE None -> builtin_const NothingB
    | OptE (Some e) -> builtin_unary JustB (exp env e)
    | TheE _e -> YetE ("TheE: " ^ Print.string_of_exp e)
    | ListE es ->
        List.fold_right
          (fun e lst -> builtin_infix ConsB (exp env e) lst)
          es (builtin_const NilB)
    | CatE (e1, e2) -> builtin_infix ConcatB (exp env e1) (exp env e2)
    | CaseE (a, { it = TupE es; _ }) -> CaseE (atom a, List.map (exp env) es)
    | CaseE (a, e) -> CaseE (atom a, [ exp env e ])
    | SubE (_e1, _t1, _t2) -> YetE ("SubE: " ^ Print.string_of_exp e)

  and update_path env path old_val (k : Agda.exp -> Agda.exp) =
    match path.it with
    | RootP -> k (exp env old_val)
    | DotP (p, a) ->
        update_path env p old_val (fun old_val' ->
            UpdE
              (old_val', atom a, k (DotE (old_val', record_id old_val, atom a))))
    | IdxP (p, _e) ->
        update_path env p old_val (fun old_val' ->
            builtin_mixfix UpdateB
              [
                old_val';
                YetE "upd";
                k (builtin_binary LookupB old_val' (YetE "upd"));
              ])
    | SliceP (_p, _e1, _e2) -> YetE "SliceP"

  let rec pat env (e : Ast.exp) : Agda.pat =
    match e.it with
    | VarE n -> VarP (id n)
    | BoolE b -> LiteralP (BoolL b)
    | NatE n -> LiteralP (NatL n)
    | TextE t -> LiteralP (TextL t)
    | UnE (_op, _e2) -> YetP ("UnE: " ^ Print.string_of_exp e)
    | BinE (AddOp, e, { it = Ast.NatE 1; _ }) ->
        CaseP (builtin SucB, [ pat env e ])
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
    | CaseE (a, { it = TupE es; _ }) -> CaseP (atom a, List.map (pat env) es)
    | CaseE (a, e) -> CaseP (atom a, [ pat env e ])
    | SubE (_e1, _t1, _t2) -> YetP ("SubE: " ^ Print.string_of_exp e)

  let typefield env (a, t, _hints) = (atom a, (typ env) t)

  exception NoComp

  let record_comp env x tfs =
    let x1 = Agda.Id "x1" in
    let x2 = Agda.Id "x2" in
    let field (a, t, _) =
      let op =
        match typ env t with
        | ApplyE (VarE (BuiltIn MaybeB), _) -> Agda.MaybeChoiceB
        | ApplyE (VarE (BuiltIn ListB), _) -> Agda.ConcatB
        | VarE t when List.mem t env.records_with_comp -> Agda.CompB t
        | _ -> raise NoComp
      in
      ( atom a,
        Agda.(
          builtin_mixfix op
            [ DotE (VarE x1, x, atom a); DotE (VarE x2, x, atom a) ]) )
    in
    try
      Some
        (Agda.DefD
           ( builtin (CompB x),
             ArrowE (Agda.VarE x, ArrowE (Agda.VarE x, Agda.VarE x)),
             [ ([ VarP x1; VarP x2 ], StrE (List.map field tfs)) ] ))
    with NoComp -> None

  let deftyp env x (dt : Ast.deftyp) =
    match dt.it with
    | AliasT ty ->
        ([ Agda.DefD (tyid x, builtin_const SetB, [ ([], (typ env) ty) ]) ], env)
    | NotationT (_op, ty) ->
        ([ DefD (tyid x, builtin_const SetB, [ ([], (typ env) ty) ]) ], env)
    | StructT tfs -> (
        let t = tyid x in
        let record_def =
          Agda.RecordD (t, builtin_const SetB, List.map (typefield env) tfs)
        in

        match record_comp env t tfs with
        | None -> ([ record_def ], env)
        | Some comp_def -> ([ record_def; comp_def ], add_record_with_comp env t)
        )
    | VariantT tcs ->
        ( [
            DataD
              ( tyid x,
                builtin_const SetB,
                List.map
                  (fun (a, t, _hints) ->
                    ( atom a,
                      [],
                      (match t.it with
                      | Ast.TupT ts -> List.map (typ env) ts
                      | _ -> [ typ env t ]),
                      Agda.VarE (tyid x) ))
                  tcs );
          ],
          add_variant env x tcs )

  let clause env (cls : Ast.clause) =
    let (DefD (_binds, p, e, premises)) = cls.it in
    match premises with
    | [] -> ([ (pat env) p ], exp env e)
    | _ :: _ -> failwith __LOC__

  let iterate_ty (ty : Agda.exp) : Ast.iter -> Agda.exp = function
    | Opt -> builtin_unary MaybeB ty
    | List | List1 | ListN _ -> builtin_unary ListB ty

  let rule env (rel : Agda.exp) (r : Ast.rule) =
    let (RuleD (x, bs, _op, e, ps)) = r.it in
    let binds bs =
      List.map
        (fun (x, t, iter) -> (id x, List.fold_left iterate_ty (typ env t) iter))
        bs
    in
    let rec premise (p : Ast.premise) : Agda.exp =
      match p.it with
      | RulePr (x, _op, e) -> ApplyE (VarE (tyid x), exp env e)
      | IfPr e -> exp env e
      | ElsePr ->
          failwith
            __LOC__ (* Apparently, this should be removed in the middlend *)
      | IterPr (p', (Opt, [ v ])) ->
          builtin_binary MaybeAllB (FunE (id v, premise p')) (VarE (id v))
      | IterPr (p', ((List | List1 | ListN _), [ v ])) ->
          builtin_binary ListAllB (FunE (id v, premise p')) (VarE (id v))
      | IterPr (p', ((List | List1 | ListN _), [ v1; v2 ])) ->
          builtin_ternary ListAll2B
            (FunE (id v1, FunE (id v2, premise p')))
            (VarE (id v1))
            (VarE (id v2))
      | IterPr (_prem, _iter) -> YetE ("IterPr: " ^ "ITER")
    in

    let premises ps = List.map premise ps in
    ( (if x.it <> "" then id x else Agda.Id "-"),
      binds bs,
      premises ps,
      Agda.ApplyE (rel, exp env e) )

  let rec def env (d : Ast.def) =
    match d.it with
    | SynD (id, dt) -> deftyp env id dt
    | RelD (x, _op, ty, rules) ->
        ( [
            DataD
              ( tyid x,
                ArrowE ((typ env) ty, builtin_const SetB),
                List.map (rule env (VarE (tyid x))) rules );
          ],
          add_relation env x rules )
    | DecD (i, tin, tout, clss) ->
        ( [
            DefD
              ( funid i,
                ArrowE ((typ env) tin, (typ env) tout),
                List.map (clause env) clss );
          ],
          env )
    | RecD defs ->
        let defs', env = script env defs in
        ([ MutualD defs' ], env)
    | HintD _ -> ([], env)

  and script env sc =
    List.fold_left
      (fun (defs, env) d ->
        let defs', env' = def env d in
        (defs @ defs', env'))
      ([], env) sc
end

let script sc =
  let sc', _env = Translate.script Translate.initial_env sc in
  sc'
