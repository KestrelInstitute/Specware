\section{MetaSlang Wrapper for the parser}

Synchronized with r1.1.1.1 SW4/Languages/SpecCalculus/Parser/Parse.sl

\begin{spec}
SpecCalc qualifying spec {
  import ../AbstractSyntax/Types
  import /Library/Legacy/Utilities/Lisp

  op parseFile : fa(a) String -> Option (SpecFile a)

  def parseFile file =
    % let file   = Lisp.string (FilePath.toString file) in
    let file   = Lisp.string (file) in
    let result = Lisp.apply (Lisp.symbol ("PARSER4","PARSEFILE"), [file]) in
    %  See semantics.lisp for definition of parseFile
    Lisp.uncell result
}
\end{spec}
