\section{Doubles}

\begin{spec}
Double qualifying spec {
  type Double
  op +  infixl 25 : Double * Double -> Double
  op -  infixl 25 : Double * Double -> Double
  op *  infixl 27 : Double * Double -> Double
  op // infixl 27 : Double * Double -> Double
  op ~ : Double -> Double

  op <  infixl 20 : Double * Double -> Bool
  op <= infixl 20 : Double * Double -> Bool
  op >  infixl 20 : Double * Double -> Bool
  op >= infixl 20 : Double * Double -> Bool

  op min : Double * Double -> Double
  op max : Double * Double -> Double

  op sqrt : Double -> Double
  op exp  : Double -> Double
  op abs  : Double -> Double
  op pi   : Double

  op sqr : Double -> Double
  def sqr x = x * x

  op show : Double -> String

  op fromNat    : Nat    -> Double
  op fromInt    : Int    -> Double
  op fromString : String -> Double
}
\end{spec}
