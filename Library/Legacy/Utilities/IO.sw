\section{IO Primitives}

These are based upon Common Lisp IO primitives.

\begin{spec}
IO qualifying spec {
  import /Library/Base

  sort Stream
  sort FileString = String
  sort Format     = String
  % sort Line       = String

  op terminal : Stream
  op string   : Stream

  op withOpenFileForRead   : fa(A) FileString * (Stream -> A) -> A
  op withOpenFileForWrite  : fa(A) FileString * (Stream -> A) -> A
  op withOpenFileForAppend : fa(A) FileString * (Stream -> A) -> A

  op withOutputToString : fa(A) (Stream -> A) -> String


  op deleteFile      : String -> ()
  op fileExists?     : String -> Boolean

  op format1         : fa (a)     Stream * Format * a         -> ()
  op format2         : fa (a,b)   Stream * Format * a * b     -> ()
  op format3         : fa (a,b,c) Stream * Format * a * b * c -> ()

  op formatTerminal1 : fa (a)     Format * a         -> ()
  op formatTerminal2 : fa (a,b)   Format * a * b     -> ()
  op formatTerminal3 : fa (a,b,c) Format * a * b * c -> ()

  op formatString1   : fa (a)     Format * a         -> String
  op formatString2   : fa (a,b)   Format * a * b     -> String
  op formatString3   : fa (a,b,c) Format * a * b * c -> String

  op readLines       : fa(A) FileString * (String * A -> A) * A -> A

  % Write the lines to an indicated file
  % until the argument function returns NONE

  op writeLines : FileString * (() -> Option String) -> ()

  op read  : fa (a) Stream -> Option a
  op write : fa (a) Stream * a -> ()

  %% True iff both files exist and the first is older.
  %% Application:
  %%   fileOlder? ("foo.sl", "foo.lisp")
  %% means that we *don't* need to recompile.
 
  op fileOlder? : FileString * FileString -> Boolean
  op ensureDirectoriesExist : FileString -> ()

  %% Write Nat, Char, and String to terminal

  op writeNat        : Nat    -> ()
  op writeChar       : Char   -> ()
  op writeString     : String -> ()
  op writeLineNat    : Nat    -> ()
  op writeLineChar   : Char   -> ()
  op writeLineString : String -> ()

  %% Adds specware home directory to arg
  op FileNameInSpecwareHome: FileString -> FileString

  op gotoFilePosition: FileString * Nat * Nat -> ()
  op emacsEval: String -> {}

  op chooseMenu: List String -> Integer
  %% No defs here -- see ...
}
\end{spec}
