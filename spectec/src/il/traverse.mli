type 'acc t
type ('acc, 't) visitor = 't -> 'acc -> 't * 'acc

val traverse :
  ?exp:('acc, Ast.exp) visitor ->
  ?iter:('acc, Ast.iter) visitor ->
  ?iterexp:('acc, Ast.iterexp) visitor ->
  ?path:('acc, Ast.path) visitor ->
  ?def:('acc, Ast.def) visitor ->
  ('acc, Ast.script) visitor
