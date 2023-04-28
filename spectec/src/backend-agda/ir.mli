type id = string

type exp =
  | VarE of id
  | SetE
  | YetE of string

type cons = id * (id option * exp) list

type def =
  | DefD of id * exp
  | DataD of id * exp * cons list
  | YetD of string

type program = def list