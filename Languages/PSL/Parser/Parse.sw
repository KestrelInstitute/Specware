\section{MetaSlang Wrapper for the parser}

\begin{spec}
SpecCalc qualifying spec {
  import ../AbstractSyntax/Types
  import /Library/Legacy/Utilities/Lisp

  op parsePSLFile : fa(a) String -> Option (SpecTerm a)

  def parsePSLFile file =
    % let file   = Lisp.string (FilePath.toString file) in
    let file   = Lisp.string (file) in
    let result = Lisp.apply (Lisp.symbol ("PARSER4","PARSEPSLFILE"), [file]) in
    %  See semantics.lisp for definition of parsePSLFile
    Lisp.uncell result
}
\end{spec}
