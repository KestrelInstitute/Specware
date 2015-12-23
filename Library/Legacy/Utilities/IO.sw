(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* IO Primitives

These are based upon Common Lisp IO primitives.
*)

IO qualifying spec

  type Stream
  type FileString = String
  type Format     = String
  % type Line       = String

  op terminal : Stream
  op string   : Stream

  op withOpenFileForRead   : [A] FileString * (Stream -> A) -> A
  op withOpenFileForWrite  : [A] FileString * (Stream -> A) -> A
  op withOpenFileForAppend : [A] FileString * (Stream -> A) -> A

  op withOutputToString : [A] (Stream -> A) -> String


  op deleteFile      : String -> ()
  op fileExists?     : String -> Bool

  op format1         : [a]     Stream * Format * a         -> ()
  op format2         : [a,b]   Stream * Format * a * b     -> ()
  op format3         : [a,b,c] Stream * Format * a * b * c -> ()

  op formatTerminal1 : [a]     Format * a         -> ()
  op formatTerminal2 : [a,b]   Format * a * b     -> ()
  op formatTerminal3 : [a,b,c] Format * a * b * c -> ()

  op formatString1   : [a]     Format * a         -> String
  op formatString2   : [a,b]   Format * a * b     -> String
  op formatString3   : [a,b,c] Format * a * b * c -> String

  op readLines       : [A] FileString * (String * A -> A) * A -> A

  % Write the lines to an indicated file
  % until the argument function returns NONE

  op writeLines : FileString * (() -> Option String) -> ()

  op read  : [a] Stream -> Option a
  op write : [a] Stream * a -> ()

  %% True iff both files exist and the first is older.
  %% Application:
  %%   fileOlder? ("foo.sl", "foo.lisp")
  %% means that we *don't* need to recompile.
 
  op fileOlder? : FileString * FileString -> Bool
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

  op chooseMenu: List String -> Int
  %% No defs here -- see ...
endspec
