(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* MetaSlang Wrapper for the parser *)

(* Synchronized with r1.1.1.1 SW4/Languages/SpecCalculus/Parser/Parse.sl *)

SpecCalc qualifying spec
  import ../AbstractSyntax/Types
  import /Library/Legacy/Utilities/Lisp
  import SCConstructors

  op parseSpecwareFile : String -> Option SpecTerm

  def parseSpecwareFile file =
    % let file   = Lisp.string (FilePath.toString file) in
    let file   = Lisp.string (file) in
    let result = Lisp.apply (if caseSensitiveSubstrate?
                               then Lisp.symbol ("Parser4","parseSpecwareFile")
                               else Lisp.symbol ("PARSER4","PARSESPECWAREFILE"),
                             [file])
    in
    %  See Handwritten/Lisp/parser-interface.lisp for definition of parseSpecwareFile
    Lisp.uncell result
endspec
