(* Currently, the prose directly borrows some structures of AL.
   Perhaps this should be improved later *)

type cmpop = Eq | Ne | Lt | Gt | Le | Ge

(* TODO: perhaps rename to `stmt`, to avoid confusion with Wasm *)
type instr =
| LetI of Al.Ast.expr * Al.Ast.expr
| CmpI of Al.Ast.expr * cmpop * Al.Ast.expr
| MustValidI of Al.Ast.expr * Al.Ast.expr * Al.Ast.expr option
| MustMatchI of Al.Ast.expr * Al.Ast.expr
| IsValidI of Al.Ast.expr option
| IfI of Al.Ast.expr * instr list
| ForallI of Al.Ast.expr * Al.Ast.expr * instr list
| EquivI of Al.Ast.expr * Al.Ast.expr
| YetI of string

type para =
| CmpP of cmpop * Al.Ast.expr * Al.Ast.expr
| NotP of para
| AndP of para list
| OrP of para list
| IfP of para list * para
| IffP of para * para
| ForeachP of (Al.Ast.expr * Al.Ast.expr) list * para
| ForallP of Al.Ast.expr list * para
| ExistsP of Al.Ast.expr list * para
| ExpP of Al.Ast.expr
| ValidP of Al.Ast.expr option * Al.Ast.expr option * Al.Ast.expr * Al.Ast.expr option
| StepP of Al.Ast.expr * Al.Ast.expr
(* TODO: (lemmagen) Refactor this *)
(* | RelP of Al.Ast.id * (Il.Ast.mixop list * Al.Ast.expr list) *)
| RelP of Al.Ast.id * Al.Ast.expr list
| PredP of Al.Ast.id * Al.Ast.expr list
| CustomP of string * Al.Ast.expr list
| YetP of string

(* TODO: perhaps rename to avoid name clash *)
type def =
(* TODO: (lemmagen) Refactor this *)
| Stmt of string * string * Al.Ast.id * para
| Pred of Al.Ast.atom * Al.Ast.expr list * instr list
| Algo of Al.Ast.algorithm

type prose = def list
