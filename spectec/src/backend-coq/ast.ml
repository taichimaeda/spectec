open Util.Source


type nat = int
type text = string
type id = string phrase

type atom =
  | Atom of string               (* atomid *)
  | Infinity                     (* infinity *)
  | Bot                          (* `_|_` *)
  | Top                          (* `^|^` *)
  | Dot                          (* `.` *)
  | Dot2                         (* `..` *)
  | Dot3                         (* `...` *)
  | Semicolon                    (* `;` *)
  | Backslash                    (* `\` *)
  | In                           (* `<-` *)
  | Arrow                        (* `->` *)
  | Arrow2                       (* `=>` *)
  | Colon                        (* `:` *)
  | Sub                          (* `<:` *)
  | Sup                          (* `:>` *)
  | Assign                       (* `:=` *)
  | Equiv                        (* `==` *)
  | Approx                       (* `~~` *)
  | SqArrow                      (* `~>` *)
  | SqArrowStar                  (* `~>*` *)
  | Prec                         (* `<<` *)
  | Succ                         (* `>>` *)
  | Turnstile                    (* `|-` *)
  | Tilesturn                    (* `-|` *)
  | Quest                        (* `?` *)
  | Plus                         (* `+` *)
  | Star                         (* `*` *)
  | Comma                        (* `,` *)
  | Bar                          (* `|` *)
  | LParen                       (* `(` *)
  | LBrack                       (* `[` *)
  | LBrace                       (* `{` *)
  | RParen                       (* `)` *)
  | RBrack                       (* `]` *)
  | RBrace                       (* `}` *)

type mixop = atom list list      (* mixfix name *)

type typ' = 
  | VarT of id 
  | NatT
  | BoolT
  | TextT
  | IterT of typ * iter
  | TupT of typ list

and typ = typ' phrase

and iter =
  | Opt                          (* `?` *)
  | List                         (* `*` *)
  | List1                        (* `+` *)
  | ListN of exp * id option     (* `^` exp *)


and deftyp = deftyp' phrase
and deftyp' =
  | AliasT of typ                       (* type alias *)
  | NotationT of mixop * typ            (* notation type *)
  | StructT of typfield list            (* record type *)
  | VariantT of typcase list            (* variant type *)

and typfield = atom * (typ * premise list)   (* record field *)
and typcase = atom * (typ * premise list)    (* variant case *)



and unop =
  | NotOp             (* `~` *)
  | PlusOp            (* `+` *)
  | MinusOp           (* `-` *)

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
  | DotE of exp * atom           (* exp `.` atom *)
  | CompE of exp * exp           (* exp `@` exp *)
  | TupE of exp list             (* `(` list2(exp, `,`) `)` *)
  | MixE of mixop * exp          (* exp atom exp *)
  | CallE of id * exp            (* defid exp? *)
  | IterE of exp * iterexp       (* exp iter *)
  | OptE of exp option           (* exp? *)
  | TheE of exp                  (* THE exp *)
  | ListE of exp list            (* [exp ... exp] *)
  | CatE of exp * exp            (* exp :: exp *)
  | CaseE of atom * exp          (* atom exp *)
  | SubE of exp * typ * typ      (* exp : typ1 <: typ2 *)

and exp = exp' phrase

and expfield = atom * exp        (* atom exp *)

and path = path' phrase
and path' =
  | RootP                        (*  *)
  | IdxP of path * exp           (* path `[` exp `]` *)
  | SliceP of path * exp * exp   (* path `[` exp `:` exp `]` *)
  | DotP of path * atom          (* path `.` atom *)

and iterexp = iter * id list

and binds = (id * typ * iter list) list

and rule = rule' phrase
and rule' =
  | RuleD of id * binds * mixop * exp * premise list  (* relation rule *)

and clause = clause' phrase
and clause' =
  | DefD of binds * exp * exp * premise list          (* definition clause *)

and premise = premise' phrase
and premise' =
  | RulePr of id * mixop * exp                        (* premise *)
  | IfPr of exp                                       (* side condition *)
  | LetPr of exp * exp * id list                      (* assignment *)
  | ElsePr                                            (* otherwise *)
  | IterPr of premise * iterexp 

and def' =
  | SynD of id * deftyp                               (* syntax type *)
  | RelD of id * mixop * typ * rule list              (* relation *)
  | DecD of id * typ * typ * clause list              (* definition *)
  | RecD of def list                                  (* recursive *)

and def = def' phrase

and script = def list