\section{Oscar Specs (prototype)}

This defines the sort \verb+Oscar.Spec+ that represents the semantic
value of evaluating an Oscar specification.

The \verb+modeSpec+ consists of all the (global) sorts, ops and variables
within scope in the procedures in \verb+procedures+.

\begin{spec}
Oscar qualifying spec {

  import ModeSpec
  import ProcedureMap qualifying
    (translate /Library/Structures/Data/Maps/Finite by {
      Dom.Dom +-> Id.Id,
      Cod.Cod +-> Procedure.Procedure
     })

  sort Spec = {
    modeSpec : ModeSpec,
    procedures : ProcedureMap.Map
  }

  op make : ModeSpec -> ProcedureMap.Map
  def make modeSpec procedures = {
      modeSpec = modeSpec,
      procedures = procedures
    }

  op modeSpec : Spec -> ModeSpec
  op procedures : Spec -> ProcedureMap.Map

  op withModeSpec infixl 17 : Spec * ModeSpec -> Spec
  def withModeSpec (oscSpec,newModeSpec) = {
      modeSpec = newModeSpec,
      procedures = procedures oscSpec
    }

  op withProcedures infixl 17 : Spec * ProcedureMap.Map -> Spec
  def withProcedures (oscSpec,newProcedures) = {
      modeSpec = modeSpec oscSpec,
      procedures = newProcedures
    }

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

In my opinon, it is unfortunate that the "with" functions are not curried.
Others might disagree.
