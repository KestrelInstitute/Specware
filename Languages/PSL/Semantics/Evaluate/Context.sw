During compilation we carry around some contex information. This requires some
more thought as not all the compilation functions need all the information.
Perhaps this should be added to the local monadic state. Perhaps the operations
should be monadic.

Some of the state is changed and must be restored as one enters and leaves a context.
The rest changes monotonically.  Perhaps the product should be partitioned
to reflect this and thereby simplify the task of restoring the context.

\begin{spec}
Context qualifying spec 

  sort ProcContext = {
      procedures : PolyMap.Map (QualifiedId,Procedure),
      modeSpec : ModeSpec,
      graphCounter : Nat,
      varCounter : Nat,
      initial : V.Elem,
      final : V.Elem,
      exit : V.Elem,
      break : Option V.Elem,
      continue : Option V.Elem,
      bSpec : BSpec,
      returnInfo : ReturnInfo
    }
  
  op procedures : ProcContext -> PolyMap.Map (QualifiedId, Procedure)
  def procedures ctxt = procedures ctxt
  
  op modeSpec : ProcContext -> ModeSpec
  def modeSpec ctxt = ctxt.modeSpec
  
  op graphCounter : ProcContext -> Nat
  def graphCounter ctxt = graphCounter ctxt

% Should really identify V.Elem with E.Elem since in the
% twist they have the same.
% The implementation of this function is naive in the sense that
% it creates and destroys things on the heap more than it should.

  op newGraphElement : ProcContext -> (V.Elem * ProcContext)
  def newGraphElement ctxt =
    (mkNatVertexEdge (graphCounter ctxt),
     ctxt withGraphCounter ((graphCounter ctxt) + 1))

% perhaps we should have just new var function?
  op varCounter : ProcContext -> Nat
  def varCounter ctxt = varCounter ctxt

  op initial : ProcContext -> V.Elem
  def initial ctxt = initial ctxt
  
  op final : ProcContext -> V.Elem
  def final ctxt = final ctxt
  
  op exit : ProcContext -> V.Elem
  def exit ctxt = exit ctxt
  
  op break : ProcContext -> Option V.Elem
  def break ctxt = break ctxt
  
  op continue : ProcContext -> Option V.Elem
  def continue ctxt = continue ctxt
  
  op bSpec : ProcContext -> BSpec
  def bSpec ctxt = bSpec ctxt
  
  op returnInfo : ProcContext -> ReturnInfo
  def returnInfo ctxt = returnInfo ctxt

  op withProcedures : ProcContext * PolyMap.Map (QualifiedId,Procedure) -> ProcContext 
  def withProcedures ctxt procs = {
      procedures = procs,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }

  op withModeSpec : ProcContext * ModeSpec -> ProcContext 
  def withModeSpec (ctxt,modeSpec) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withFinal infixl 17 : ProcContext * V.Elem -> ProcContext 
  def withFinal (ctxt,vertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = vertex,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withBreak infixl 17 : ProcContext * (Option V.Elem) -> ProcContext 
  def withBreak (ctxt,optVertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = optVertex,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withContinue infixl 17 : ProcContext * (Option V.Elem) -> ProcContext 
  def withContinue (ctxt,optVertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = optVertex,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withInitial infixl 17 : ProcContext * V.Elem -> ProcContext 
  def withInitial (ctxt,vertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = vertex,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withBSpec infixl 17 : ProcContext * BSpec -> ProcContext 
  def withBSpec (ctxt,bSpec) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec,
      returnInfo = returnInfo ctxt
    }
  
  op withGraphCounter infixl 17 : ProcContext * Nat -> ProcContext 
  def withGraphCounter (ctxt,graphCounter) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      graphCounter = graphCounter,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      returnInfo = returnInfo ctxt
    }

  op withExit infixl 17 : ProcContext * V.Elem -> ProcContext 
  op withReturnInfo infixl 17 : ProcContext * ReturnInfo -> ProcContext 
\end{spec}

