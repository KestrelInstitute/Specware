\section{Boolean}

\begin{spec}
Boolean qualifying spec
  import PrimitiveSorts
  import Compare

  % sort Boolean = | true | false
  op &   infixr 15 : Boolean * Boolean -> Boolean 
  op or  infixr 14 : Boolean * Boolean -> Boolean 
  op =>  infixr 13 : Boolean * Boolean -> Boolean 
  op <=> infixr 12 : Boolean * Boolean -> Boolean 

  op ~ : Boolean -> Boolean

  op toString : Boolean -> String
  op show : Boolean -> String
  def show b = toString b

  op compare  : Boolean * Boolean -> Comparison

  def ~   x     = if x then false else true
  def or  (x,y) = if x then true  else y
  def &   (x,y) = if x then y     else false
  def =>  (x,y) = if x then y     else true
  def <=> (x,y) = if x then y     else ~y 
end
\end{spec}
