\section{Procedural Specs}

I have forgotten what the axiom spec is for .. why is it not part
of the static or dynamic specs. Look into this.

\begin{spec}
spec {
  import Procedure
  import /Languages/MetaSlang/Specs/AnnSpec
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

  sort PSpec a = {
    staticSpec : ASpec a,
    dynamicSpec : ASpec a,
    axiomSpec : ASpec a,
    procedures : PolyMap.Map (String,Procedure a)
  }
}
\end{spec}
