type builtin =
  | SetB
  | BoolB
  | NatB
  | TextB
  | MaybeB
  | ListB
  | UnOpB of Il.Ast.unop
  | BinOpB of Il.Ast.binop
  | CmpOpB of Il.Ast.cmpop
  | LookupB
  | CompB of string
  | LengthB
  | JustB
  | ConsB
  | NilB
  | ConcatB
  | MaybeMapB
  | ListMapB
  | NothingB
  | SucB
  | MaybeAllB
  | ListAllB
  | ListAll2B
  | UpdateB

type id = Id of string | TyId of string | FunId of string | BuiltIn of builtin
type literal = BoolL of bool | NatL of int | TextL of string

type pat =
  | VarP of id
  | LiteralP of literal
  | TupleP of pat list
  | YetP of string
  | CaseP of id * pat list

type exp =
  | VarE of id
  | LiteralE of literal
  | ProdE of exp list
  | TupleE of exp list
  | StrE of (id * exp) list
  | YetE of string
  | ArrowE of exp * exp
  | ApplyE of exp * exp
  | CaseE of id * exp list
  | DotE of exp * id * id
  | FunE of id * exp
  | UpdE of exp * id * exp
  | MixfixE of id * exp list

type cons = id * (id * exp) list * exp list * exp
type field = id * exp
type clause = pat list * exp

type def =
  | DefD of id * exp * clause list
  | DataD of id * exp * cons list
  | RecordD of id * exp * field list
  | MutualD of def list

type program = def list
