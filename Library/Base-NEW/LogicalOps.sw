LogicalOp qualifying spec

  (* This spec defines some useful logical operations, which may become
  "inbuilt" (see language manual) in future versions of Metaslang. *)

  % epsilon operator (looks like binder in `some (fn x -> ...)'):
  op some : [a] {p : a -> Boolean | ex(x) p x} -> a
  % underspecified:
  axiom some is [a] fa (p : a -> Boolean) (ex(x) p x) => p (some p)

  % exists unique (looks like quantifier in `ex1 (fn x -> ...)'):
  op ex1 : [a] (a -> Boolean) -> Boolean
  def ex1 p = (ex(x) p x && (fa(y) p y => y = x))

  % iota operator (looks like binder in `the (fn x -> ...)'):
  op the : [a] ((a -> Boolean) | ex1) -> a
  def the p = some p

endspec
