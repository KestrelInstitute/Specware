\section{Construction / Destruction Operations}

\begin{spec}
spec {
  import Environment

  op staticSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  op dynamicSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  op procedures : fa (a) PSpec a -> SpecCalc.Env (PolyMap.Map (QualifiedId,Procedure))
  
  op setStaticSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  op setDynamicSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  op setProcedures : fa (a) PSpec a -> PolyMap.Map (QualifiedId,Procedure) -> SpecCalc.Env (PSpec a)
  op addProcedure : fa (a) PSpec a -> QualifiedId -> Procedure -> SpecCalc.Env (PSpec a)
}
\end{spec}
