\section{Construction / Destruction Operations}

\begin{spec}
spec {
  import Environment

  op staticSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  op dynamicSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  op axiomSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  op procedures : fa (a) PSpec a -> SpecCalc.Env (PolyMap.Map (String,Procedure a))
  
  op setStaticSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  op setDynamicSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  op setAxiomSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  op setProcedures : fa (a) PSpec a -> PolyMap.Map (String,Procedure a) -> SpecCalc.Env (PSpec a)
}
\end{spec}
