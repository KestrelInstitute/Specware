(* Low Level Impure IO operations

This is a poorly named file in a poorly named directory. The idea,
however, is to keep the impure environment operations
separate from the pure (monadic) operations.

*)

IO qualifying spec
  import /Library/Base

  sort Filename = String
  sort Time     = Nat          % Not a fixnum
  sort Byte     = {x : Nat | 0 <= x &  x < 256} 

  op getCurrentDirectory   : () -> Filename
  op fileExistsAndReadable : Filename -> Boolean
  op fileWriteTime         : Filename -> Time
  op nullFileWriteTime     : Time
  op currentTime           : () -> Time
  op convertToFileName     : String -> Filename

  op fileWritable          : Filename -> Boolean
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
