(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Low Level Impure IO operations

This is a poorly named file in a poorly named directory. The idea,
however, is to keep the impure environment operations
separate from the pure (monadic) operations.

*)

IO qualifying spec
  import /Library/Base

  type Filename = String
  type Time     = Nat          % Not a fixnum
  type Byte     = {x : Nat | 0 <= x &&  x < 256} 

  op getCurrentDirectory   : () -> Filename
  op fileExistsAndReadable : Filename -> Bool
  op fileWriteTime         : Filename -> Time
  op nullFileWriteTime     : Time
  op currentTime           : () -> Time
  op convertToFileName     : String -> Filename

  op fileWritable          : Filename -> Bool
  op readBytesFromFile     : Filename -> List Byte
  op writeBytesToFile      : List Byte * Filename -> ()

  op readStringFromFile    : Filename -> String
  % All the cons's make the following overflow the stack
  % def readStringFromFile filename =
  %   implode (map chr (readBytesFromFile filename))

  op writeStringToFile : String *  Filename -> ()
%% Too inefficient
%  def writeStringToFile (string, filename) =
%    writeBytesToFile (map ord (explode string),
%		      filename)
endspec
