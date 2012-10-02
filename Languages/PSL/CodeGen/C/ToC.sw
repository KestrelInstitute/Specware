\section{Code generation for PSL}

This is incomplete.

\begin{spec}
spec {
  import ../../Semantics/PSpec
  import /Languages/BSpecs/Predicative/CodeGen/C/ToC
  import /Languages/C/AbstractSyntax/Printer

  op programToC : PSpec -> String -> CSpec
  def programToC pSpec outFile =
    let procs = prg.procedures in
    let headerFile = 
      case (rev (explode outFile)) of
          ((#c)::(#.)::rest) -> implode (rev (Cons (#h, (Cons (#.,rest)))))
        | expOutFile -> implode (rev (Cons (#h, (Cons (#.,expOutFile))))) in
    let main = prg.main in
    let _ = writeLine("Main Proc: " ^ main) in
    let cspec_with_main_define = {
      includes = [headerFile],
      constDefns = [],
      vars = [],
      extVars = [],
      fns = [],
      axioms = [],
      typeDefns = [],
      structDefns = [],
      unionDefns = [],
      varDefns = [],
      fnDefns = [],
      defines = Cons((fixProcName main) ^ " Main", inputEvs)
      } in
    let procsAsList = mapToList procs in
    let procNames = map (fn(id,_) -> id) procsAsList in
    let localVars =
    let cProcs = map (procedureToC main globalDefns staticVars procNames) procsAsList in
    let result = mergeCSpecs (Cons(cspec_with_main_define,cProcs)) in
    let str = textToString (format(80, ppCSpec(result))) in
    let _ = withOpenFileForWrite (outFile, writeString str) in
    let _ = makeHeaderFile headerFile inputData outputData inputEvents outputEvents in
    result

  op fixProcName : String -> String
  def fixProcName oldName =
    let def validChar c = (isAlphaNum c) or (c = #_) in
    let newStr = implode (filter validChar (explode oldName)) in
    newStr

  op procedureToC : String -> List VarDefn -> List VarDecl -> List String  
                             -> String * Procedure_ms -> CSpec
  def procedureToC main globalDefns staticVars procNames (procname,proc) =
    let _ = writeLine("proc " ^ procname ^ "...") in
    let cguinfo = {
           funName = fixProcName procname,
           funParNames = proc.parameters,
           resultOpName = proc.return,
           procNames = procNames,
           globalVarNames = map (fn (x,y) -> x) staticVars
          }
    in
    let varCSpec : CSpec = { 
       includes    = [],
       defines     = [],
       constDefns  = [],
       vars        = staticVars,
       extVars     = [],
       fns         = [],
       axioms      = [],
       typeDefns   = [],
       structDefns = [],
       unionDefns  = [],
       varDefns    = globalDefns,
       fnDefns     = []
      } in
    let res = bSpecToC proc.code cguinfo  in
    let res =
      if procname = main then 
        mergeCSpecs([res,varCSpec])
      else
        res
    in
    let _ = writeLine("done.") in
    res
\end{spec}

The operator to get the main procedure. It will cause a system
failure, if the main procedure cannot be found.

\begin{spec}
  op getMainProc: Program_ms -> Procedure_ms
  def getMainProc(prg) =
    let procsAsList = mapToList prg.procedures in
    let mproc = find (fn(pname,proc) -> (pname = prg.main)) procsAsList in
    case mproc of
      | Some (_,proc) -> proc
      | None -> fail("cannot find main proc "^prg.main^" in program")
\end{spec}

The global variables are contained in the dynamic spec of the main procedure. The following operator extracts the names of the global variables.

\begin{spec}
  op getGlobalVarNames: Program_ms -> List String
  def getGlobalVarNames(prg) =
    let mainproc = getMainProc(prg) in
    let dspc = mainproc.dynamic in
    let glops = dspc.ops in
    StringMap_listDomain(glops)
}
\end{spec}
