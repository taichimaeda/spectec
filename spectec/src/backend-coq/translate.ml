open Il.Ast
open Util.Source

let _error at msg = Util.Source.error at "Coq generation" msg
module CoqAst = Ast

module IdSet = Set.Make(String)
let reserved_ids = ["N"; "in"; "In"; "()"; "tt"; "Import"; "Export"; "List"; "String"; "Type"] |> IdSet.of_list

let rec make_id s = 
  let s' = make_id' s.it in
  s' $ s.at

and make_id' s = match s with
 | s when IdSet.mem s reserved_ids -> "reserved__" ^ s
 | s -> String.map (function
    | '.' -> '_'
    | '-' -> '_'
    | c -> c
    ) s

let translate_atom (a : atom) =
  match a with
    | Atom str -> CoqAst.Atom (make_id' str)
    | _ -> CoqAst.Atom (Il.Print.string_of_atom a)

let translate_binop (b : binop) =
  match b with
    | AndOp -> CoqAst.AndOp
    | OrOp -> CoqAst.OrOp
    | AddOp _ -> CoqAst.AddOp
    | SubOp _ -> CoqAst.SubOp
    | ImplOp -> CoqAst.ImplOp
    | MulOp _ -> CoqAst.MulOp
    | DivOp _ -> CoqAst.DivOp
    | ExpOp _ -> CoqAst.ExpOp
    | EquivOp -> CoqAst.EquivOp

let translate_unop (u : unop) =
  match u with
    | NotOp -> CoqAst.NotOp
    | PlusOp _ -> CoqAst.PlusOp
    | MinusOp _ -> CoqAst.MinusOp

let translate_cmpop (c : cmpop) =
  match c with
    | EqOp -> CoqAst.EqOp
    | NeOp -> CoqAst.NeOp
    | LtOp _ -> CoqAst.LtOp
    | GtOp _ -> CoqAst.GtOp
    | LeOp _ -> CoqAst.LeOp
    | GeOp _ -> CoqAst.GeOp

let rec translate_typ (t : typ) = 
  let t' = translate_typ' t in
  t' $ t.at
and translate_typ' (t: typ) =
  match t.it with
    | VarT id -> CoqAst.VarT (make_id id)
    | NumT _ -> CoqAst.NatT
    | TextT -> CoqAst.TextT
    | BoolT -> CoqAst.BoolT
    | TupT typs -> CoqAst.TupT (List.map (fun t -> translate_typ t) typs)
    | IterT (typ, iter) -> CoqAst.IterT (translate_typ typ, translate_iter iter)

and translate_exp (e : exp) = 
  let e' = translate_exp' e in
  e' $ e.at

and translate_exp' (e : exp) =
  match e.it with
    | VarE id -> CoqAst.VarE (make_id id)
    | BoolE bool -> CoqAst.BoolE bool
    | NatE nat -> CoqAst.NatE nat
    | TextE text -> CoqAst.TextE ("\"" ^ String.escaped text ^ "\"")
    | UnE (op, exp) ->  CoqAst.UnE (translate_unop op, translate_exp exp)
    | BinE (binop, exp1, exp2) -> CoqAst.BinE (translate_binop binop, translate_exp exp1, translate_exp exp2)
    | CmpE (cmpop, exp1, exp2) -> CoqAst.CmpE (translate_cmpop cmpop, translate_exp exp1, translate_exp exp2)
    | IdxE (exp1, exp2) -> CoqAst.CallE ("lookup_total" $ no_region, (CoqAst.TupE [translate_exp exp1; translate_exp exp2]) $ e.at) 
    | SliceE (exp1, exp2, exp3) -> CoqAst.SliceE (translate_exp exp1, translate_exp exp2, translate_exp exp3)
    | UpdE (exp, path, exp2) -> CoqAst.UpdE (translate_exp exp, translate_path path, translate_exp exp2)
    | ExtE (exp1, path, exp2) -> CoqAst.ExtE (translate_exp exp1, translate_path path, translate_exp exp2)
    | StrE expfields -> CoqAst.StrE (List.map (fun (a, e) -> (translate_atom a, translate_exp e)) expfields)       
    | DotE (exp, atom) -> CoqAst.DotE (translate_exp exp, translate_atom atom)       
    | CompE (exp, exp2) -> CoqAst.CompE (translate_exp exp, translate_exp exp2)
    | LenE exp -> CoqAst.CallE ("List.length" $ no_region, CoqAst.TupE [translate_exp exp] $ e.at)                 
    | TupE exps -> CoqAst.TupE (List.map (fun e -> translate_exp e) exps)
    | MixE (mixop, exp) -> CoqAst.MixE (translate_mixop mixop, translate_exp exp)
    | CallE (id, exp) -> CoqAst.CallE (id, translate_exp exp)
    | IterE (exp, (iter, ids)) -> CoqAst.IterE (translate_exp exp, (translate_iter iter, ids))
    | OptE None -> CoqAst.OptE (None)
    | OptE (Some exp) -> CoqAst.OptE (Some (translate_exp exp))
    | TheE exp -> CoqAst.TheE (translate_exp exp)   
    | ListE exps -> CoqAst.ListE (List.map (fun e -> translate_exp e) exps)
    | CatE (exp1, exp2) -> CoqAst.CatE (translate_exp exp1, translate_exp exp2)
    | CaseE (atom, exp) -> CoqAst.CaseE (translate_atom atom, translate_exp exp)         
    | SubE (exp, typ1, typ2) -> CoqAst.SubE (translate_exp exp, translate_typ typ1, translate_typ typ2)

and translate_mixop (m : mixop) =
  List.map (fun l -> List.map (fun a -> translate_atom a) l) m
and translate_path (p : path) =
  let p' = translate_path' p in
  p' $ p.at

and translate_path' (p : path) =
  match p.it with   
    | RootP -> CoqAst.RootP
    | IdxP (path, exp) -> CoqAst.IdxP (translate_path path, translate_exp exp)
    | SliceP (path, exp1, exp2) -> CoqAst.SliceP (translate_path path, translate_exp exp1, translate_exp exp2)
    | DotP (path, atom) -> CoqAst.DotP (translate_path path, translate_atom atom)

and translate_iter (it : iter) =
  match it with
    | Opt -> CoqAst.Opt
    | List -> CoqAst.List
    | List1 -> CoqAst.List1
    | ListN (exp, id) -> CoqAst.ListN (translate_exp exp, id)

let rec translate_premise (p : premise) =
  let p' = translate_premise' p in
  p' $ p.at
and translate_premise' (p : premise) = 
  match p.it with
    | RulePr (id, mixop, exp) -> CoqAst.RulePr (id, translate_mixop mixop, translate_exp exp)
    | IfPr exp -> CoqAst.IfPr (translate_exp exp)
    | LetPr (exp1, exp2, ids) -> CoqAst.LetPr (translate_exp exp1, translate_exp exp2, ids)
    | ElsePr -> CoqAst.ElsePr
    | IterPr (premise, (iter, ids)) -> CoqAst.IterPr (translate_premise premise, (translate_iter iter, ids))

let rec translate_def (d : def) : CoqAst.def =
  let d' = translate_def' d in
  d' $ d.at

and translate_def' (d : def) =
  match d.it with
    | SynD (id, deftyp) -> CoqAst.SynD (make_id id, (match deftyp.it with 
      | AliasT typ -> CoqAst.AliasT (translate_typ typ)
      | NotationT (_mixop, _typ) -> CoqAst.StructT []
      | StructT (_typfields) -> CoqAst.StructT []
      | VariantT typcases -> CoqAst.VariantT (List.map (fun (a, (_, t, prems), _) -> 
        (translate_atom a, (translate_typ t, List.map translate_premise prems))) typcases)) 
        $ deftyp.at)
    | RelD (_id, _mixop, _typ, _rules) -> CoqAst.RecD []
    | DecD (_id, _typ1, _typ2, _clauses) -> CoqAst.RecD []
    | RecD _defs -> CoqAst.RecD []
    | HintD _ -> CoqAst.RecD []
  
 let translate_il (il: script) = 
  List.map (fun d -> translate_def d) il

