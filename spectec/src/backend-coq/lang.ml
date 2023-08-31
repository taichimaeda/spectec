(* Identifiers *)
type ident = string

(* Names in binders *)
type name = ident

type typ =
  | UnitBT
  | BoolBT
  | NatBT
  | StringBT
  | TermT of ident
  | ListT of typ
  | OptionT of typ
  | TupleT of typ list
  

(* TODO: Find out a hierarchy between patterns and terms that is actually sensible *)
type pattern0 = 
  | NatBP of int
  | BoolBP of bool
  | StringBP of string
  | TupP of (pattern list)

and pattern = 
  | BasicP of pattern0
  | IdentP of ident
  | ListP of (pattern list)
  | AppP of ident * (pattern list)
  | OptionP of (pattern option)
  | UnsupportedP of string


type term0 = 
  | NatBE of int
  | BoolBE of bool
  | StringBE of string
  | ListE of (term list)
  | TupE of (term list)
  | OptionE of (term option)
  | UnopE of unop * term
  | BinopE of binop * term * term
  | OptionMapE of lambda_term * term
  | OptionZipE of lambda_term * term * term
  | ListLenE of term
  | ListCatE of term * term
  | ListCompE of term * term
  | ListMapE of lambda_term * term
  | ListZipE of lambda_term * term * term
  | ListGetE of term * term
  | ListSetE of term * term * term
  | ListForallE of lambda_term * term
  | ListForall2E of lambda_term * term * term
  | RecordE of ((ident * term) list) (* TODO: need type information *)
  | GetFieldE of term * ident
  | SetFieldE of term * ident * term

and lambda_term = (ident list) * term

and unop = 
  | NotE
  | MinusE

and binop = 
  | AddE
  | SubE 
  | MulE 
  | DivE 
  | ExpE 
  | EqE
  | NeqE 
  | LeE
  | LtE
  | GeE
  | GtE
  | EquivE
  | AndE
  | OrE

and term = 
  | BasicE of term0
  | IdentE of ident
  | AppE of ident * (term list)
  | MatchE of term_match
  | UnsupportedE of string

and match_clause = pattern * term

and term_match = ident * (match_clause list)

type binder = name * typ

(* (Inductive) type constructors can only be of the form `ident (type)^*`.
   *)
type type_constructor = ident * (typ list)

(*
  (Inductive) relation constructors can only be of the form `ident (binder)^* (prem)^* relation_inst`.
  Each premise is a term, and the final relation instance is also expressed in a term.
   *)
type rel_constructor = ident * (binder list) * (term list) * term

(*
  Definition of each field of a record is simply its identifier and type.
   *)
type record_constructor = ident * typ

(* Flag for whether a definition is recursive or not. This was not part of the DSL and had to be inferred from the
   translation process. Seemingly only useful to Coq to determine whether a function definition should start
   with `Definition` or `Fixpoint`.  *)
type rec_flag = 
  | RecF
  | NoRecF

type typedef = 
  | TypeD of ident * typ
  | FuncD of rec_flag * ident * (binder list) * typ * term
  | IndTypeD of ident * (type_constructor list)
  | IndRelD of ident * typ * (rel_constructor list) (* Currently, relations are only defined on one argument of a given type *)
  | RecordD of ident * (record_constructor list)
  | MutualD of typedef list
  | UnsupportedD of string