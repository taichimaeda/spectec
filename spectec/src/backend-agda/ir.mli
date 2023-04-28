type id = string

type exp =
  | YetE of string

type cons = id * (id * exp) list

type def =
  | DefD of id * exp
  | DataD of id * exp * cons list
  | YetD of string

type program = def list
