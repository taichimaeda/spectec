open Util.Source


type nat = Z.t
type text = string
type id = string phrase
type atom = Il.Atom.atom
type mixop = Il.Atom.mixop

type typ' = 
  | VarT of id * arg list
  | NatT
  | BoolT
  | TextT
  | IterT of typ * iter
  | TupT of (exp * typ) list

and typ = typ' phrase

and iter =
  | Opt                          (* `?` *)
  | List                         (* `*` *)
  | List1                        (* `+` *)
  | ListN of exp * id option     (* `^` exp *)


and deftyp = deftyp' phrase
and deftyp' =
  | AliasT of typ                (* type alias *)
  | StructT of typfield list     (* record type *)
  | VariantT of typcase list     (* variant type *)

and typfield = atom * (typ * premise list)   (* record field *)
and typcase = mixop * (typ * premise list)    (* variant case *)



and unop =
  | NotOp             (* `~` *)
  | PlusOp            (* `+` *)
  | MinusOp           (* `-` *)
  | PlusMinusOp       (* `+-` *)
  | MinusPlusOp       (* `-+` *)

and binop =
  | AndOp            (* `/\` *)
  | OrOp             (* `\/` *)
  | ImplOp           (* `=>` *)
  | EquivOp          (* `<=>` *)
  | AddOp            (* `+` *)
  | SubOp            (* `-` *)
  | MulOp            (* `*` *)
  | DivOp            (* `/` *)
  | ExpOp            (* `^` *)

and cmpop =
  | EqOp             (* `=` *)
  | NeOp             (* `=/=` *)
  | LtOp             (* `<` *)
  | GtOp             (* `>` *)
  | LeOp             (* `<=` *)
  | GeOp             (* `>=` *)

and exp' = 
  | VarE of id                   (* varid *)
  | BoolE of bool                (* bool *)
  | NatE of nat                  (* nat *)
  | TextE of text                (* text *)
  | UnE of unop * exp            (* unop exp *)
  | BinE of binop * exp * exp    (* exp binop exp *)
  | CmpE of cmpop * exp * exp    (* exp cmpop exp *)
  | SliceE of exp * exp * exp    (* exp `[` exp `:` exp `]` *)
  | UpdE of exp * path * exp     (* exp `[` path `=` exp `]` *)
  | ExtE of exp * path * exp     (* exp `[` path `=..` exp `]` *)
  | StrE of expfield list        (* `{` list(expfield, `,`) `}` *)
  | ProjE of exp * int           (* exp.i *)
  | DotE of exp * atom           (* exp `.` atom *)
  | CompE of exp * exp           (* exp `@` exp *)
  | TupE of exp list             (* `(` list2(exp, `,`) `)` *)
  | MixE of mixop * exp          (* exp atom exp *)
  | CallE of id * arg list       (* defid exp? *)
  | IterE of exp * iterexp       (* exp iter *)
  | OptE of exp option           (* exp? *)
  | TheE of exp                  (* THE exp *)
  | ListE of exp list            (* [exp ... exp] *)
  | LenE of exp
  | CatE of exp * exp            (* exp :: exp *)
  | IdxE of exp * exp
  | CaseE of mixop * exp          (* atom exp *)
  | SubE of exp * typ * typ      (* exp : typ1 <: typ2 *)
  | UncaseE of exp * mixop       (* exp!mixop *)

and exp = (exp', typ) note_phrase

and arg = arg' phrase
and arg' =
  | ExpA of exp                                       (* exp *)
  | TypA of typ                                       (* `syntax` typ *)

and expfield = atom * exp        (* atom exp *)

and path = (path', typ) note_phrase
and path' =
  | RootP                        (*  *)
  | IdxP of path * exp           (* path `[` exp `]` *)
  | SliceP of path * exp * exp   (* path `[` exp `:` exp `]` *)
  | DotP of path * atom          (* path `.` atom *)

and iterexp = iter * (id * typ) list

and bind = bind' phrase
and bind' =
  | ExpB of id * typ * iter list
  | TypB of id

and inst = inst' phrase
and inst' =
  | InstD of bind list * arg list * deftyp            (* family instance clause *)

and param = param' phrase
and param' =
  | ExpP of id * typ                                  (* varid `:` typ *)
  | TypP of id                                        (* `syntax` varid *)

and rule = rule' phrase
and rule' =
  | RuleD of id * mixop * exp * premise list  (* relation rule *)

and clause = clause' phrase
and clause' =
  | DefD of bind list * arg list * exp * premise list          (* definition clause *)

and premise = premise' phrase
and premise' =
  | RulePr of id * mixop * exp                        (* premise *)
  | IfPr of exp                                       (* side condition *)
  | LetPr of exp * exp * id list                      (* assignment *)
  | ElsePr                                            (* otherwise *)
  | IterPr of premise * iterexp 

and def' =
  | TypD of id * param list * inst list               (* syntax type *)
  | RelD of id * mixop * typ * rule list              (* relation *)
  | DecD of id * param list * typ * clause list              (* definition *)
  | RecD of def list                                  (* recursive *)


and def = def' phrase

and script = def list