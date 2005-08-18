\section{Abstraction of Spec Calculus}

This is an unfortunate (and perhaps unnecessary) mutual dependency
between specs in this directory and those in the directory for the spec
calculus. The SpecCalculus/AbstractSyntax/Types imports PosSpec. PosSpec
imports AnnSpec and AnnSpec needs the sort SpecCalc.Term to record import
information. Similarly, the pretty printer for specs must pretty print
the spec calculus terms that are imported to that spec.

In this spec, we abstract the signature for the sorts and ops from
the spec calculus that are needed by local specs and thereby break
the recursion.

\begin{spec}
spec
 sort SpecCalc.Term a

 op SpecCalc.showTerm : fa (a) SpecCalc.Term a -> String

 op sameSCTerm? : [a] SpecCalc.Term a * SpecCalc.Term a -> Boolean

endspec
\end{spec}
