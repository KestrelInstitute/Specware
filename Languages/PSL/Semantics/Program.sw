\section{Program Sort}

This is the top-level sort for representing programs. In the
abstract syntax, a pror

\begin{spec}
spec {
  import Procedure
  import /Languages/MetaSlang/Specs/SimplePrinter

  sort Program = {
    procedures : PolyMap.Map (String, Procedure),
    main : String
  }

  op ppProgram : Program -> Pretty
  def ppProgram prg =
    let main = PolyMap.eval prg.procedures prg.main in
    ppConcat [
      ppString ("main=" ^ prg.main),
      ppBreak,
      ppString "procs={",
      ppBreak,
      ppNest 2 (PolyMap.ppMap ppString ppProcedure prg.procedures),
      ppBreak,
      ppString "static=",
      ppNest 2 (ppASpec main.static),
      ppString "}"
    ]

  op showProgram : Program -> String
  def showProgram prg =
    let main = PolyMap.eval prg.procedures prg.main in
    let pList = PolyMap.foldMap (fn l -> fn name -> fn prc ->
                  Cons (name ^ " |-> " ^ (ppFormat (ppProcedure prc)),l))
                    [] prg.procedures in
    "main="
    ^ prg.main
    ^ "\nprocs={\n"
    ^ (show "\n" pList)
    ^ "}"
}
\end{spec}
