Boolean qualifying spec

  % refinement of base spec Boolean

  import Primitive

  % sorts:

  % sort Boolean

  % ops whose Lisp code is generated:

  op ~             : Boolean -> Boolean
  op &   infixr 15 : Boolean * Boolean -> Boolean 
  op or  infixr 14 : Boolean * Boolean -> Boolean 
  op =>  infixr 13 : Boolean * Boolean -> Boolean 
  op <=> infixr 12 : Boolean * Boolean -> Boolean 
  op ~=  infixr 20 : fa(a) a * a -> Boolean

  def ~   x     = if x then false else true

  def &   (x,y) = if x then y     else false

  def or  (x,y) = if x then true  else y

  def =>  (x,y) = if x then y     else true

  def <=> (x,y) = if x then y     else ~y 

  def ~=  (x,y) = ~(x = y)

  % ops conceptually belonging to this spec but introduced elsewhere:

  % op compare  : Boolean * Boolean -> Comparison
  % op toString : Boolean -> String  % deprecated
  % op show     : Boolean -> String

endspec
