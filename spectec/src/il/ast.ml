open Util.Source


(* TODO: annotate types on nodes *)


(* Terminals *)

type nat = Z.t
type text = string
type id = string phrase
type atom = Atom.atom
type mixop = Atom.mixop


(* Iteration *)

type iter =
  | Opt                          (* `?` *)
  | List                         (* `*` *)
  | List1                        (* `+` *)
  | ListN of exp * id option     (* `^` exp *)


(* Types *)

and numtyp =
  | NatT                         (* `nat` *)
  | IntT                         (* `int` *)
  | RatT                         (* `rat` *)
  | RealT                        (* `real` *)

and typ = typ' phrase
and typ' =
  | VarT of id * arg list        (* varid( arg* ) *)
  | BoolT                        (* `bool` *)
  | NumT of numtyp               (* numtyp *)
  | TextT                        (* `text` *)
  | TupT of (exp * typ) list     (* typ * ... * typ *)
  | IterT of typ * iter          (* typ iter *)
  | BotT                         (* bottom type *)

and deftyp = deftyp' phrase
and deftyp' =
  | AliasT of typ                (* type alias *)
  | StructT of typfield list     (* record type *)
  | VariantT of typcase list     (* variant type *)

and typfield = atom * (bind list * typ * prem list) * hint list  (* record field *)
and typcase = mixop * (bind list * typ * prem list) * hint list  (* variant case *)


(* Expressions *)

and unop =
  | NotOp             (* `~` *)
  | PlusOp of numtyp  (* `+` *)
  | MinusOp of numtyp (* `-` *)
  | PlusMinusOp of numtyp (* `+-` *)
  | MinusPlusOp of numtyp (* `-+` *)

and binop =
  | AndOp            (* `/\` *)
  | OrOp             (* `\/` *)
  | ImplOp           (* `=>` *)
  | EquivOp          (* `<=>` *)
  | AddOp of numtyp  (* `+` *)
  | SubOp of numtyp  (* `-` *)
  | MulOp of numtyp  (* `*` *)
  | DivOp of numtyp  (* `/` *)
  | ModOp of numtyp  (* `\` *)
  | ExpOp of numtyp  (* `^` *)

and cmpop =
  | EqOp             (* `=` *)
  | NeOp             (* `=/=` *)
  | LtOp of numtyp   (* `<` *)
  | GtOp of numtyp   (* `>` *)
  | LeOp of numtyp   (* `<=` *)
  | GeOp of numtyp   (* `>=` *)

and exp = (exp', typ) note_phrase
and exp' =
  | VarE of id                   (* varid *)
  | BoolE of bool                (* bool *)
  | NatE of nat                  (* nat *)
  | TextE of text                (* text *)
  | UnE of unop * exp            (* unop exp *)
  | BinE of binop * exp * exp    (* exp binop exp *)
  | CmpE of cmpop * exp * exp    (* exp cmpop exp *)
  | TupE of exp list             (* ( exp* ) *)
  | ProjE of exp * int           (* exp.i *)
  | CaseE of mixop * exp         (* atom exp? *)
  | UncaseE of exp * mixop       (* exp!mixop *)
  | OptE of exp option           (* exp? *)
  | TheE of exp                  (* exp! *)
  | StrE of expfield list        (* { expfield* } *)
  | DotE of exp * atom           (* exp.atom *)
  | CompE of exp * exp           (* exp @ exp *)
  | ListE of exp list            (* [exp ... exp] *)
  | LenE of exp                  (* |exp| *)
  | CatE of exp * exp            (* exp :: exp *)
  | IdxE of exp * exp            (* exp[exp]` *)
  | SliceE of exp * exp * exp    (* exp[exp : exp] *)
  | UpdE of exp * path * exp     (* exp[path = exp] *)
  | ExtE of exp * path * exp     (* exp[path =.. exp] *)
  | CallE of id * arg list       (* defid( arg* ) *)
  | IterE of exp * iterexp       (* exp iter *)
  | SubE of exp * typ * typ      (* exp : typ1 <: typ2 *)
  | RuleE of id * mixop * exp    (* relid : exp *)
  (* TODO: (lemmagen) Binds only args in quantifiers *)
  | ForallE of bind list * arg list * exp    (* forall `(` arg* `)` exp *)
  | ExistsE of bind list * arg list * exp    (* exists `(` arg* `)` exp *)
  | TmplE of slot                (* `{{ slot`}}` *)

and expfield = atom * exp        (* atom exp *)

and path = (path', typ) note_phrase
and path' =
  | RootP                        (*  *)
  | IdxP of path * exp           (* path `[` exp `]` *)
  | SliceP of path * exp * exp   (* path `[` exp `:` exp `]` *)
  | DotP of path * atom          (* path `.` atom *)

and slot = slot' phrase
and slot' = 
  | TopS of id                   (* id *)
  | DotS of slot * id            (* slot `.` id *)
  | WildS of slot                (* slot `.` `*` *)
  | VarS of slot                 (* `...` slot *)

and iterexp = iter * (id * typ) list


(* Definitions *)

and arg = arg' phrase
and arg' =
  | ExpA of exp                                       (* exp *)
  | TypA of typ                                       (* `syntax` typ *)

and bind = bind' phrase
and bind' =
  | ExpB of id * typ * iter list
  | TypB of id

and param = param' phrase
and param' =
  | ExpP of id * typ                                  (* varid `:` typ *)
  | TypP of id                                        (* `syntax` varid *)

and def = def' phrase
and def' =
  | TypD of id * param list * inst list               (* syntax type (family) *)
  | RelD of id * mixop * typ * rule list              (* relation *)
  | DecD of id * param list * typ * clause list       (* definition *)
  | ThmD of id * bind list * exp                      (* theorem *)
  | LemD of id * bind list * exp                      (* lemma *)
  | RecD of def list                                  (* recursive *)
  | TmplD of def                                      (* template *)
  | HintD of hintdef

and inst = inst' phrase
and inst' =
  | InstD of bind list * arg list * deftyp            (* family instance clause *)

and rule = rule' phrase
and rule' =
  | RuleD of id * bind list * mixop * exp * prem list (* relation rule *)

and clause = clause' phrase
and clause' =
  | DefD of bind list * arg list * exp * prem list    (* definition clause *)

and prem = prem' phrase
and prem' =
  | RulePr of id * mixop * exp                        (* premise *)
  | IfPr of exp                                       (* side condition *)
  | LetPr of exp * exp * id list                      (* assignment *)
  | ElsePr                                            (* otherwise *)
  | IterPr of prem * iterexp                          (* iteration *)

and hintdef = hintdef' phrase
and hintdef' =
  | TypH of id * hint list
  | RelH of id * hint list
  | DecH of id * hint list
  | ThmH of id * hint list
  | LemH of id * hint list

and hint = {hintid : id; hintexp : string list}       (* hint *)


(* Scripts *)

type script = def list
