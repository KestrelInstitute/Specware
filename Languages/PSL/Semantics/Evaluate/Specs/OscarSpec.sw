\section{Oscar Specs (prototype)}

This defines the sort \verb+Oscar.Spec+ that represents the semantic
value of evaluating an Oscar specification.

The \verb+modeSpec+ consists of all the (global) sorts, ops and variables
within scope in the procedures in \verb+procedures+.

\begin{spec}
Oscar qualifying spec {
  import ModeSpec
  import ProcMap

  sort Spec = {
    modeSpec : ModeSpec,
    procedures : ProcMap.Map
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
  def withProcedures (oscSpec,newProcedures) = {
      modeSpec = modeSpec oscSpec,
      procedures = newProcedures
    }

  op addOp : Spec -> OpInfo -> Position -> Env Spec
  op addVariable : Spec -> OpInfo -> Position -> Env Spec
  op addSort : Spec -> SortInfo -> Position -> Env Spec
  op addProperty : Spec -> Property -> Position -> Env Spec

  op OscarSpec.foldVariables : fa(a) (a -> OpInfo -> a) -> a -> Spec -> a
  op OscarSpecEnv.foldVariables : fa(a) (a -> OpInfo -> Env a) -> a -> Spec -> Env a


  op pp : Spec -> Doc
  def pp oscarSpec =
    ppConcat [
      pp "modeSpec=",
      ppNewline,
      ppIndent (pp (modeSpec oscarSpec)),
      ppNewline,
      pp "procedures=",
      ppNewline,
      ppIndent (pp (procedures oscarSpec))
    ]
}
\end{spec}

We explicitly qualify the names with something like the name of the sort
for the abstract data type. This is so that the functions like \verb+pp+
can be overloaded.
