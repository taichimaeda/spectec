type 'acc t
type ('acc, 't) visitor = 't -> 'acc -> 't * 'acc

val traverse :
  ?exp:('acc, Il.Ast.exp) visitor ->
  ?iter:('acc, Il.Ast.iter) visitor ->
  ?iterexp:('acc, Il.Ast.iterexp) visitor ->
  ?path:('acc, Il.Ast.path) visitor ->
  ?def:('acc, Il.Ast.def) visitor ->
  ('acc, Il.Ast.script) visitor
