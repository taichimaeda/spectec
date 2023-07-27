open Ast

val eq_iter : iter -> iter -> bool
val eq_exp : exp -> exp -> bool
val eq_typ : typ -> typ -> bool

val eq_opt : ('a -> 'a -> bool) -> 'a option -> 'a option -> bool
val eq_list : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
