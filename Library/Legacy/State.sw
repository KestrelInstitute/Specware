\section{State Primitives}

This should be used sparingly!

\begin{spec}
State qualifying spec {
 sort Ref T = | Ref T

 op := infixl 4 : fa(T) Ref T * T -> ()
 op ! : fa(T) Ref T -> T

 % def := (cell,value) = ()
 % def !(x) = case x of ref(y) => y end 
}
\end{spec}
