\section{Doubles}

\begin{spec}
Double qualifying spec {
  sort Double
  op + infixl 25 : Double * Double -> Double
  op - infixl 25 : Double * Double -> Double
  op * infixl 27 : Double * Double -> Double
  op // infixl 27 : Double * Double -> Double
  op ~ : Double -> Double

  op <  infixl 20 : Double * Double -> Boolean
  op <= infixl 20 : Double * Double -> Boolean
  op >  infixl 20 : Double * Double -> Boolean
  op >= infixl 20 : Double * Double -> Boolean

  op min : Double * Double -> Double
  op max : Double * Double -> Double

  op sqrt : Double -> Double
  op exp : Double -> Double
  op abs : Double -> Double
  op pi : Double

  op sqr : Double -> Double
  def sqr x = x * x

  op show : Double -> String

  op fromNat : Nat -> Double
  op fromString : String -> Double
  op fromInteger : Integer -> Double
}
\end{spec}
