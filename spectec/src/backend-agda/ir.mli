type id = Id of string
type const = SetC | BoolC | NatC | TextC

type exp =
  | VarE of id
  | ConstE of const
  | ProdE of exp list
  | TupleE of exp list
  | ListE of exp
  | MaybeE of exp
  | YetE of string

type cons = id * (id option * exp) list
type field = id * exp

type def =
  | DefD of id * exp option * exp
  | DataD of id * exp * cons list
  | RecordD of id * exp * field list
  | YetD of string

type program = def list
