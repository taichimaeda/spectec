type ('acc, 't) fold_map = 't -> 'acc -> 't * 'acc

val fold_map :
  ?exp:('acc, Il.Ast.exp) fold_map ->
  ?iter:('acc, Il.Ast.iter) fold_map ->
  ?iterexp:('acc, Il.Ast.iterexp) fold_map ->
  ?path:('acc, Il.Ast.path) fold_map ->
  ?rule:('acc, Il.Ast.rule) fold_map ->
  ?def:('acc, Il.Ast.def) fold_map ->
  ('acc, Il.Ast.script) fold_map

type 't map = 't -> 't

val map :
  ?exp:Il.Ast.exp map ->
  ?iter:Il.Ast.iter map ->
  ?iterexp:Il.Ast.iterexp map ->
  ?path:Il.Ast.path map ->
  ?rule:Il.Ast.rule map ->
  ?def:Il.Ast.def map ->
  Il.Ast.script map

type ('acc, 't) fold = 't -> 'acc -> 'acc

val fold :
  ?exp:('acc, Il.Ast.exp) fold ->
  ?iter:('acc, Il.Ast.iter) fold ->
  ?iterexp:('acc, Il.Ast.iterexp) fold ->
  ?path:('acc, Il.Ast.path) fold ->
  ?rule:('acc, Il.Ast.rule) fold ->
  ?def:('acc, Il.Ast.def) fold ->
  ('acc, Il.Ast.script) fold

type ('env, 't) reader = 'env -> 't -> 't

val reader :
  ?exp:('env, Il.Ast.exp) reader ->
  ?iter:('env, Il.Ast.iter) reader ->
  ?iterexp:('env, Il.Ast.iterexp) reader ->
  ?path:('env, Il.Ast.path) reader ->
  ?rule:('env, Il.Ast.rule) reader ->
  ?def:('env, Il.Ast.def) reader ->
  ('env, Il.Ast.script) reader
