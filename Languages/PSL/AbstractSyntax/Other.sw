\section{Spec Calculus Other Term}

\begin{spec}
OscarAbsSyn qualifying spec
  import Types

  sort SpecCalc.OtherTerm a =
    | Specialize MS.Term * SpecCalc.Term a
    | Inline String * SpecCalc.Term a
    | OscarDecls List (OscarSpecElem a)
    | Project String * (SpecCalc.Term a) * String

  op mkSpecialize : MS.Term * (SpecCalc.Term Position) * Position -> SpecCalc.Term Position
  def mkSpecialize (metaSlangTerm,unit,position) =
    mkOther (Specialize (metaSlangTerm,unit),position)

  op mkInline : String * (SpecCalc.Term Position) * Position -> SpecCalc.Term Position
  def mkInline (name,unit,position) =
    mkOther (Inline (name,unit),position)

  op mkProject : String * (SpecCalc.Term Position) * String * Position -> SpecCalc.Term Position
  def mkProject (name,unit,fileName,position) =
    mkOther (Project (name,unit,fileName),position)

  op mkDecls : List (OscarSpecElem Position) * Position -> SpecCalc.Term Position
  def mkDecls (specElems,position) = mkOther (OscarDecls specElems, position)

endspec
\end{spec}
