\section{Oscar Specs (prototype)}

This defines the sort \Sort{Oscar.Spec}. It represents the semantic
value of evaluating an Oscar specification.

The field \Op{modeSpec} consists of all the (global) sorts, ops and variables
within scope in the procedures in \Op{procedures}.
## How does the latter differ from the modeSpec in \Sort{Procedure}.

\begin{spec}
Oscar qualifying spec
  import ModeSpec
  import TransSpec
  import SimpleMorph
  import Procedure
  import ProcMap

  sort Spec = {
    modeSpec : ModeSpec,
    procedures : ProcMap.Map
  }

  op empty : Spec
  def empty = {
      modeSpec = empty,
      procedures = empty
    }

  op make : ModeSpec -> ProcMap.Map -> Spec
  def make modeSpec procedures = {
      modeSpec = modeSpec,
      procedures = procedures
    }

  op modeSpec : Spec -> ModeSpec
  def modeSpec spc = spc.modeSpec

  op procedures : Spec -> ProcMap.Map
  def procedures spc = spc.procedures

  op withModeSpec infixl 17 : Spec * ModeSpec -> Spec
  def withModeSpec (oscSpec,newModeSpec) = {
      modeSpec = newModeSpec,
      procedures = procedures oscSpec
    }

  op withProcedures infixl 17 : Spec * ProcMap.Map -> Spec
  def withProcedures (oscSpec,newProcs) = {
      modeSpec = modeSpec oscSpec,
      procedures = newProcs
    }

  op addOp : Spec -> Op.OpInfo -> Position -> Env Spec
  def addOp spc opInfo position = {
      modeSpec <- addOp (modeSpec spc) opInfo position;
      return (spc withModeSpec modeSpec)
    }

  op addSort : Spec -> Sort.SortInfo -> Position -> Env Spec
  def addSort spc sortInfo position = {
      modeSpec <- addSort (modeSpec spc) sortInfo position;
      return (spc withModeSpec modeSpec)
    }

  op addVariable : Spec -> Op.OpInfo -> Position -> Env Spec
  def addVariable spc opInfo position = {
      modeSpec <- addVariable (modeSpec spc) opInfo position;
      return (spc withModeSpec modeSpec)
    }

  op addClaim : Spec -> Claim.Claim -> Position -> Env Spec
  def addClaim spc prop position = {
      modeSpec <- addClaim (modeSpec spc) prop position;
      return (spc withModeSpec modeSpec)
    }

  op addInvariant : Spec -> Claim.Claim -> Position -> Env Spec
  def addInvariant spc prop position = {
      modeSpec <- addInvariant (modeSpec spc) prop position;
      return (spc withModeSpec modeSpec)
    }

  op elaborate : Spec -> Env Spec
  def elaborate spc = {
      elabSpc <- elaborate (modeSpec spc);
      return (spc withModeSpec elabSpc)
    }

  op OscarSpec.foldVariables : fa(a) (a -> Op.OpInfo -> a) -> a -> Spec -> a
  op OscarSpecEnv.foldVariables : fa(a) (a -> Op.OpInfo -> Env a) -> a -> Spec -> Env a

  op Env.withModeSpec infixl 17 : Spec * ModeSpec -> Env Spec
  def Env.withModeSpec (oscSpec,newModeSpec) = return (oscSpec withModeSpec newModeSpec)

  op Env.withProcedures infixl 17 : Spec * ProcMap.Map -> Env Spec
  def Env.withProcedures (oscSpec,newProcs) = return (oscSpec withProcedures newProcs)

  op addProcedure : Spec -> Id.Id -> Procedure -> Env Spec
  def addProcedure spc id proc = spc withProcedures (update (procedures spc, id, proc))

  op join : SpecCalc.Term Position -> Spec -> Spec -> Position -> Env Spec
  def join term spc1 spc2 position = {
    newModeSpec <- join term (modeSpec spc1) (modeSpec spc2) position;
    newProcs <- fold (fn procMap -> fn id -> fn proc ->
      case evalPartial (procedures spc1, id) of
        | None -> return (update (procMap, id, proc))
        | Some _ -> raise (SpecError (noPos, "Procedure " ^ (show id) ^ " was redefined")))
      (procedures spc1) (procedures spc2);
    return (make newModeSpec newProcs)
  }

  op pp : Spec -> Doc
  def pp oscarSpec =
    ppConcat [
      pp "modeSpec=",
      ppNewline,
      ppIndent (ModeSpec.pp (modeSpec oscarSpec)),   % Why must pp be qualified?
      ppNewline,
      pp "procedures=",
      ppNewline,
      ppIndent (pp (procedures oscarSpec))
    ]

  op OscarEnv.show : Spec -> ModeSpec -> Env String
  def OscarEnv.show oscarSpec ms = {
      procsString <- show (procedures oscarSpec);
      modeSpecString <- return (ppFormat (ModeSpec.pp (subtract (modeSpec oscarSpec) ms)));
      return ("modeSpec=\n"
          ^ modeSpecString
          ^ "\nprocedures=\n"
          ^ procsString)
    }

  op OscarEnv.pp : Spec -> ModeSpec -> Env Doc
  def OscarEnv.pp oscarSpec ms = {
      procDoc <- pp (procedures oscarSpec);
      return
        (ppConcat [
          pp "modeSpec=",
          ppNewline,
          ppIndent (ModeSpec.pp (subtract (modeSpec oscarSpec) ms)),   % Why must pp be qualified?
          ppNewline,
          pp "procedures=",
          ppNewline,
          ppIndent procDoc
        ])
    }

  op ppLess : Spec -> ModeSpec -> Doc
  def ppLess oscarSpec ms =
    let
      def ppPair (name,proc) =
        ppConcat [
          pp name,
          pp "=",
          ppLess proc (modeSpec oscarSpec)
        ]
    in
      ppConcat [
        pp "modeSpec=",
        ppNewline,
        pp "  ",
        ppIndent (ModeSpec.pp (subtract (modeSpec oscarSpec) ms)),   % Why must pp be qualified?
        ppNewline,
        pp "procedures=",
        ppNewline,
        pp "  ",
        ppIndent (ppConcat [
          pp "{",
          ppNest 1
            (ppSep ppNewline (fold (fn (doc,pair) -> cons (ppPair pair, doc), [], procedures oscarSpec))),
          pp "}"
        ])
      ]

  op LocalProcMap.show : ProcMap.Map -> Env String
  def LocalProcMap.show map =
    let def showContents map =
      case takeOne map of
        | None -> return ""
        | One ((procId,proc),rest) -> {
           procDoc <- ProcEnv.pp procId proc;
           procString <- return (ppFormat procDoc);
           restString <- showContents rest;
           case takeOne rest of
             | None -> return procString
             | One (_,_) ->
                 return (procString ^ "\n" ^ restString)
           }
     in {
       procString <- showContents map;
       return ("{" ^ procString ^ "}")
     }

  op LocalProcMap.pp : ProcMap.Map -> Env Doc
  def LocalProcMap.pp map =
    let def ppContents map =
      case takeOne map of
        | None -> return ppNil
        | One ((procId,proc),rest) -> {
           procDoc <- ProcEnv.pp procId proc;
           restDoc <- ppContents rest;
           case takeOne rest of
             | None -> return procDoc
             | One (_,_) ->
                 return (ppGroup (ppConcat [
                   procDoc,
                   pp ",",
                   ppBreak,
                   restDoc
                 ]))
           }
     in {
       procDoc <- ppContents map;
       return (ppConcat [pp "{", procDoc, pp "}"])
     }
endspec
\end{spec}
