\section{Functions}
This spec should be given a better name.

\begin{spec}
Functions qualifying spec 
  import PrimitiveSorts

  op id : fa (A) A -> A
  op o infixl 24 : fa (A,B,C) (B -> C) * (A -> B) -> A -> C

  def id x = x
  def o (f2,f1) x = f2 (f1 x)

 % axiom ident is fa (x) id x = x
%  axiom assoc is fa (f,g,h) (h o g) o f = h o (g o f)
%  axiom comp  is fa (f,g,x) (g o f) x = g (f x)
endspec
\end{spec}
