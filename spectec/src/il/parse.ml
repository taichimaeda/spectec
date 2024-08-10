open Ast
open Util.Source


(* Source stream *)

type stream = {src : string; pos : int}

let stream src = {src; pos = 0}
let pos is = is.pos
let rem is = String.length is.src - is.pos
let eof is = (rem is = 0)
let get is = is.src.[is.pos]
let str is n = String.sub is.src is.pos n
let rest is = String.sub is.src is.pos (String.length is.src - is.pos)
let adv is n = {is with pos = is.pos + n}
let at is n =
  let left = {no_pos with column = is.pos} in
  let right = {no_pos with column = is.pos + n} in
  {left; right}


(* Results *)

type 'a results =
  | Success of stream * Subst.t * 'a * 'a results Lazy.t
  | Failure of stream * string

let failure is msg = Failure (is, msg)
let success is n s e = Success (adv is n, s, e, lazy (failure is "unexpected input"))

let rec append_results r1 lr2 =
  match r1 with
  | Failure _ -> Lazy.force lr2
  | Success (is, s, e, tl) ->
    Success (is, s, e, lazy (append_results (Lazy.force tl) lr2))

let rec map_results r f =
  match r with
  | Failure (is, s) -> Failure (is, s)
  | Success (is, s, e, tl) ->
    append_results (f (is, s, e)) (lazy (map_results (Lazy.force tl) f))

let (let*) = map_results
let (|||) r lr = append_results r (lazy (Lazy.force lr))


(* Parsing *)

let rec parse_sym env is s g : exp results =
  Debug.(log "il.parse_sym"
  	(fun _ -> fmt "%s: %s" (il_sym g) (il_text (rest is)))
  	(function
    | Success (is, s, e, _) -> fmt "success[%s] {%s} %s" (il_exp e) (mapping il_exp s.varid) (il_text (rest is))
    | Failure (_, msg) -> "failure: " ^ msg
    )
  ) @@ fun _ ->
  match g.it with
  | VarG (x, as_) ->
    let* is', _s', e = parse_gram env is x as_ in
    let src = str is (pos is' - pos is) in
    let s' = Subst.add_gramid s x (TextG src $$ x.at % (TextT $ x.at)) in (* HACK *)
    success is' 0 s' e
  | NatG _b when eof is ->
    failure is "unexpected end of input"
  | NatG b ->
    let n = Char.code b in
    if get is = b then
      success is 1 s (NatE (Z.of_int n) $$ at is 1 % g.note)
    else
      failure is (Printf.sprintf "byte 0x%02X expected" n)
  | TextG t when rem is < String.length t ->
    failure is "unexpected end of input"
  | TextG t ->
    let n = String.length t in
    if str is n = t then
      success is n s (TextE t $$ at is n % g.note)
    else
      failure is (Printf.sprintf "text `%s` expected" t)
  | EpsG ->
    success is 0 s (TupE [] $$ at is 0 % g.note)
  | SeqG [] ->
    success is 0 s (TupE [] $$ at is 0 % g.note)
  | SeqG (g1::gs) ->
    let* is', s', _e = parse_sym env is s g1 in
    parse_sym env is' s' {g with it = SeqG gs}
  | AltG [] ->
    failure is "unexpected input"
  | AltG (g1::gs) ->
    parse_sym env is s g1 ||| lazy (parse_sym env is s {g with it = AltG gs})
  | RangeG _ when eof is ->
    failure is "unexpected end of input"
  | RangeG (b1, b2) when b1 <= get is && get is <= b2->
    parse_sym env is s (NatG (get is) $$ g.at % g.note)
  | RangeG _ ->
    failure is "out of range byte"
  | IterG (g1, (Opt, _xes)) ->
    (let* is', s', eo = parse_exp_opt env is s g1 in
    success is' 0 s' (OptE eo $$ g.at % g.note) : exp results)
  | IterG (g1, (List, _xes)) ->
    let* is', s', es = parse_exp_list env is s g1 in
    success is' 0 s' (ListE es $$ g.at % g.note)
  | IterG (g1, (List1, _xes)) ->
    let* is', s', es = parse_exp_list env is s g1 in
    if es = [] then
      failure is "non-empty sequence expected"
    else
      success is' 0 s' (ListE es $$ g.at % g.note)
  | IterG (g1, (ListN (en, _ido), _xes)) ->
    let* is', s', es = parse_exp_list env is s g1 in
    (match (Eval.reduce_exp env (Subst.subst_exp s en)).it with
    | NatE n when n = Z.of_int (List.length es) ->
      success is' 0 s' (ListE es $$ g.at % g.note)
    | NatE n ->
      failure is ("sequence of length " ^ Z.to_string n ^ " expected")
    | _ ->
      failure is "cannot determine expected length of sequence"
    )
  | AttrG (e, g1) ->
    let* is', s', e' = parse_sym env is s g1 in
    match Eval.match_exp env s' e' e with
    | Some s'' -> success is' 0 s'' e'
    | None -> failure is "result does not match attribute pattern"

and parse_exp_opt env is s g1 : exp option results =
    success is 0 s None |||
    lazy (
      let* is', s', e = parse_sym env is s g1 in
      success is' 0 s' (Some e)
    )

and parse_exp_list env is s g1 : exp list results =
    success is 0 s [] |||
    lazy (
      let* is', s', e = parse_sym env is s g1 in
      let* is'', s'', es = parse_exp_list env is' s' g1 in
      success is'' 0 s'' (e::es)
    )

and parse_prod env is as_ prod =
  Debug.(log "il.parse_prod"
  	(fun _ ->
  	  let ProdD (_, _, g, e, _) = prod.it in
  	  fmt "%s -> %s @ %s" (il_sym g) (il_exp e) (il_text (rest is))
  	)
  	(function
  	| Success (is, _, e, _) -> fmt "success[%s] %s" (il_exp e) (il_text (rest is))
  	| Failure (_, msg) -> "failure: " ^ msg
    )
  ) @@ fun _ ->
	(match prod.it with
	| ProdD (_bs, as', g, e, prems) ->
	  match Eval.match_list Eval.match_arg env Subst.empty as_ as' with
	  | exception Eval.Irred -> failure is "irreducible grammar arguments"
	  | None -> failure is "grammar undefined for arguments"
	  | Some s ->
	    let g', e', prems' =
    	  Subst.(subst_sym s g, subst_exp s e, subst_prems s prems) in
      Debug.(log_in "il.parse_prod" (fun _ -> "arg subst: " ^ mapping il_exp s.varid));
      let* is', s', _e' = parse_sym env is Subst.empty g' in
      Debug.(log_in "il.parse_prod" (fun _ -> "prem subst: " ^ mapping il_exp s'.varid));
      match Eval.reduce_prems env (Subst.subst_prems s' prems') with
      | None -> failure is "cannot verify side condition"
      | Some false -> failure is "violating side condition"
      | Some true ->
        success is' 0 Subst.empty (Eval.reduce_exp env (Subst.subst_exp s' e'))
  )

and parse_prods env is as_ = function
  | [] when eof is -> failure is "unexpected end of input"
  | [] -> failure is "unexpected input"
  | prod::prods' ->
    parse_prod env is as_ prod ||| lazy (parse_prods env is as_ prods')

and parse_gram env is id as_ =
  let _ps, _t, prods = Env.find_gram env id in
  parse_prods env is as_ prods


let rec parse_all = function
  | Failure (is, msg) -> Error (pos is, msg)
  | Success (is, _s, e, _tl) when eof is ->
    (* Exercise the entire search space to detect ambiguity. This is expensive!
    (match parse_all (Lazy.force tl) with
    | Error _ -> Ok e
    | Ok _ -> Error (0, "ambiguous parse")
    )
    *)
    Ok e
  | Success (is, _s, _e, lazy tl) ->
    match parse_all tl with
    | Error _ -> Error (pos is, "end of input expected")
    | ok -> ok

let parse script name src =
  let env = Env.env_of_script script in
  let id = name $ no_region in
  if not (Env.mem_gram env id) then raise (Invalid_argument "parse") else
  let is = stream src in
  parse_all (parse_gram env is id [])
