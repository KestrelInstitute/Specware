Boolean qualifying spec

  import Primitive

  % sorts:

  % sort Boolean

  % ops whose Lisp code is hand-written:

  op ~             : Boolean -> Boolean
  op &   infixr 15 : Boolean * Boolean -> Boolean 
  op or  infixr 14 : Boolean * Boolean -> Boolean 
  op =>  infixr 13 : Boolean * Boolean -> Boolean 
  op <=> infixr 12 : Boolean * Boolean -> Boolean 

  axiom not_def is
    fa (x : Boolean) ~x = (if x then false else true)

  axiom and_def is
    fa (x,y : Boolean) (x & y)   = (if x then y    else false)

  axiom or_def is
    fa (x,y : Boolean) (x or y)  = (if x then true else y)

  axiom implies_def is
    fa (x,y : Boolean) (x => y)  = (if x then y    else true)

  axiom iff_def is
    fa (x,y : Boolean) (x <=> y) = (if x then y    else ~y)

  % ops whose Lisp code is generated:

  op ~=  infixr 20 : fa(a) a * a -> Boolean

  def ~=  (x,y) = ~(x = y)

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op compare  : Boolean * Boolean -> Comparison
  % op toString : Boolean -> String  % deprecated
  % op show     : Boolean -> String

endspec
