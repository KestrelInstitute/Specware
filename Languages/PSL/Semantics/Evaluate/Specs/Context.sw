\section{Compilation Context}

During compilation we carry around some contex information. This requires some
more thought as not all the compilation functions need all the information.
Perhaps this should be added to the local monadic state. Perhaps the operations
should be monadic.

Some of the state is changed and must be restored as one enters and leaves a context.
The rest changes monotonically.  Perhaps the product should be partitioned
to reflect this and thereby simplify the task of restoring the context.

\begin{spec}
CompCtxt qualifying spec 
  import ProcMap 

  sort CompCtxt = {
      procedures : ProcMap.Map,
      modeSpec : ModeSpec,
      graphCounter : Nat,
      varCounter : Nat,
      initial : Vrtx.Vertex,
      final : Vrtx.Vertex,
      exit : Vrtx.Vertex,
      break : Option Vrtx.Vertex,
      continue : Option Vrtx.Vertex,
      bSpec : BSpec,
      returnInfo : ReturnInfo
    }
  
  op procedures : CompCtxt -> ProcMap.Map
  def procedures ctxt = ctxt.procedures
  
  op modeSpec : CompCtxt -> ModeSpec
  def modeSpec ctxt = ctxt.modeSpec
  
  op graphCounter : CompCtxt -> Nat
  def graphCounter ctxt = ctxt.graphCounter

  % op newGraphElement : CompCtxt -> (Vrtx.Vertex * CompCtxt)
  % def newGraphElement ctxt =
    % (mkNatVertexEdge (graphCounter ctxt),
     % ctxt withGraphCounter ((graphCounter ctxt) + 1))

% perhaps we should have just new var function?
  op varCounter : CompCtxt -> Nat
  def varCounter ctxt = ctxt.varCounter

  op initial : CompCtxt -> Vrtx.Vertex
  def initial ctxt = ctxt.initial
  
  op final : CompCtxt -> Vrtx.Vertex
  def final ctxt = ctxt.final
  
  op exit : CompCtxt -> Vrtx.Vertex
  def exit ctxt = ctxt.exit
  
  op break : CompCtxt -> Option Vrtx.Vertex
  def break ctxt = ctxt.break
  
  op continue : CompCtxt -> Option Vrtx.Vertex
  def continue ctxt = ctxt.continue
  
  op bSpec : CompCtxt -> BSpec
  def bSpec ctxt = ctxt.bSpec
  
  op returnInfo : CompCtxt -> ReturnInfo
  def returnInfo ctxt = ctxt.returnInfo

  op withProcedures infixl 17 : CompCtxt * ProcMap.Map -> CompCtxt 
  def withProcedures (ctxt,procs) = {
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

  op withModeSpec infixl 17 : CompCtxt * ModeSpec -> CompCtxt 
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
  
  op withFinal infixl 17 : CompCtxt * Vrtx.Vertex -> CompCtxt 
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
  
  op withBreak infixl 17 : CompCtxt * (Option Vrtx.Vertex) -> CompCtxt 
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
  
  op withContinue infixl 17 : CompCtxt * (Option Vrtx.Vertex) -> CompCtxt 
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
  
  op withInitial infixl 17 : CompCtxt * Vrtx.Vertex -> CompCtxt 
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
  
  op withBSpec infixl 17 : CompCtxt * BSpec -> CompCtxt 
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

  op CompCtxtEnv.withBSpec infixl 17 : CompCtxt * BSpec -> Env CompCtxt 
  def CompCtxtEnv.withBSpec (ctxt,bSpec) = return (ctxt withBSpec bSpec)
  
  op withGraphCounter infixl 17 : CompCtxt * Nat -> CompCtxt 
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

  op withExit infixl 17 : CompCtxt * Vrtx.Vertex -> CompCtxt 
  op withReturnInfo infixl 17 : CompCtxt * ReturnInfo -> CompCtxt 
endspec
\end{spec}
