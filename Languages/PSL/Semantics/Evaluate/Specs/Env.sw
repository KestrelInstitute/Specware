\section{The Specware Environment Monad}

We need support for exceptions and state (and later perhaps IO).

\begin{spec}
let Monad =
  spec
    import /Library/Structures/Data/Monad/Exception
    import /Library/Structures/Data/Monad/State
  endspec
in SpecCalc qualifying spec
  import translate (translate Monad by {Monad.Monad +-> SpecCalc.Env}) by {Monad._ +-> SpecCalc._}
  import /Languages/MetaSlang/Specs/Position

  op specError : fa(a) String -> Position -> Env a
  op EnvNoPos.specError : fa(a) String -> Env a
  def EnvNoPos.specError str = specError str internalPosition

  op fatalError : fa(a) String -> Position -> Env a
  op EnvNoPos.fatalError : fa(a) String -> Env a
  def EnvNoPos.fatalError str = fatalError str internalPosition
endspec
\end{spec}
