\section{Construction / Destruction Operations}

\begin{spec}
spec {
  import Environment

  op evaluatePSpecElems :
           PSpec Position
        -> List (PSpecElem Position)
        -> Env (PSpec Position * TimeStamp * URI_Dependency)

  op staticSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  def staticSpec pSpec = return pSpec.staticSpec

  op dynamicSpec : fa (a) PSpec a -> SpecCalc.Env (ASpec a)
  def dynamicSpec pSpec = return pSpec.dynamicSpec

  op procedures : fa (a) PSpec a -> SpecCalc.Env (PolyMap.Map (QualifiedId,Procedure))
  def procedures pSpec = return pSpec.procedures
  
  op setStaticSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  def setStaticSpec pSpec spc = return {
      staticSpec = spc,
      dynamicSpec = pSpec.dynamicSpec,
      procedures = pSpec.procedures
    }

  op setDynamicSpec : fa (a) PSpec a -> ASpec a -> SpecCalc.Env (PSpec a)
  def setDynamicSpec pSpec spc = return {
      staticSpec = pSpec.staticSpec,
      dynamicSpec = spc,
      procedures = pSpec.procedures
    }

  op setProcedures : fa (a) PSpec a -> PolyMap.Map (QualifiedId,Procedure) -> SpecCalc.Env (PSpec a)
  def setProcedures pSpec procs = return {
      staticSpec = pSpec.staticSpec,
      dynamicSpec = pSpec.dynamicSpec,
      procedures = procs
    }

  op addProcedure : fa (a) PSpec a -> QualifiedId -> Procedure -> SpecCalc.Env (PSpec a)
  def addProcedure pSpec id proc = return {
      staticSpec = pSpec.staticSpec,
      dynamicSpec = pSpec.dynamicSpec,
      procedures = PolyMap.update pSpec.procedures id proc
    }
}
\end{spec}
