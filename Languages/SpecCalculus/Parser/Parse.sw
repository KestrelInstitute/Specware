\section{MetaSlang Wrapper for the parser}

Synchronized with r1.1.1.1 SW4/Languages/SpecCalculus/Parser/Parse.sl

\begin{spec}
SpecCalc qualifying spec {
  import ../AbstractSyntax/Types
  import /Library/Legacy/Utilities/Lisp

  op parseSpecwareFile : fa(a) String -> Option (SpecTerm a)

  def parseSpecwareFile file =
    % let file   = Lisp.string (FilePath.toString file) in
    let file   = Lisp.string (file) in
    let result = Lisp.apply (Lisp.symbol ("PARSER4","PARSESPECWAREFILE"), [file]) in
    %  See Handwritten/Lisp/parser-interface.lisp for definition of parseSpecwareFile
    Lisp.uncell result
}
\end{spec}
