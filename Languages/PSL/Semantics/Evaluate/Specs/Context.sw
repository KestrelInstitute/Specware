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
      varCounter : Nat,
      initial : Mode,
      final : Mode,
      exit : Mode,
      break : Option Mode,
      continue : Option Mode,
      bSpec : BSpec,
      procId : Id.Id,
      returnInfo : ReturnInfo
    }
  
  op procedures : CompCtxt -> ProcMap.Map
  def procedures ctxt = ctxt.procedures
  
  op modeSpec : CompCtxt -> ModeSpec
  def modeSpec ctxt = ctxt.modeSpec
  
  op varCounter : CompCtxt -> Nat
  def varCounter ctxt = ctxt.varCounter

  op initial : CompCtxt -> Mode
  def initial ctxt = ctxt.initial
  
  op final : CompCtxt -> Mode
  def final ctxt = ctxt.final
  
  op exit : CompCtxt -> Mode
  def exit ctxt = ctxt.exit
  
  op break : CompCtxt -> Option Mode
  def break ctxt = ctxt.break
  
  op continue : CompCtxt -> Option Mode
  def continue ctxt = ctxt.continue
  
  op bSpec : CompCtxt -> BSpec
  def bSpec ctxt = ctxt.bSpec

  op procId : CompCtxt -> Id.Id
  def procId ctxt = ctxt.procId
  
  op returnInfo : CompCtxt -> ReturnInfo
  def returnInfo ctxt = ctxt.returnInfo

  op withProcedures infixl 17 : CompCtxt * ProcMap.Map -> CompCtxt 
  def withProcedures (ctxt,procs) = {
      procedures = procs,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }

  op withModeSpec infixl 17 : CompCtxt * ModeSpec -> CompCtxt 
  def withModeSpec (ctxt,modeSpec) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withFinal infixl 17 : CompCtxt * Mode -> CompCtxt 
  def withFinal (ctxt,mode) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = mode,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withBreak infixl 17 : CompCtxt * (Option Mode) -> CompCtxt 
  def withBreak (ctxt,optVertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = optVertex,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withContinue infixl 17 : CompCtxt * (Option Mode) -> CompCtxt 
  def withContinue (ctxt,optVertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = optVertex,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withInitial infixl 17 : CompCtxt * Mode -> CompCtxt 
  def withInitial (ctxt,vertex) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = vertex,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec ctxt,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }
  
  op withBSpec infixl 17 : CompCtxt * BSpec -> CompCtxt 
  def withBSpec (ctxt,bSpec) = {
      procedures = procedures ctxt,
      modeSpec = modeSpec ctxt,
      varCounter = varCounter ctxt,
      initial = initial ctxt,
      final = final ctxt,
      exit = exit ctxt,
      break = break ctxt,
      continue = continue ctxt,
      bSpec = bSpec,
      procId = procId ctxt,
      returnInfo = returnInfo ctxt
    }

  op CompCtxtEnv.withBSpec infixl 17 : CompCtxt * BSpec -> Env CompCtxt 
  def CompCtxtEnv.withBSpec (ctxt,bSpec) = return (ctxt withBSpec bSpec)
  
  op withExit infixl 17 : CompCtxt * Vrtx.Vertex -> CompCtxt 
  op withReturnInfo infixl 17 : CompCtxt * ReturnInfo -> CompCtxt 
endspec
\end{spec}
