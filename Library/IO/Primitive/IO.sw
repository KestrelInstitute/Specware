\section{Low Level Impure IO operations}

This is a poorly named file in a poorly named directory. The idea,
however, is to keep the impure environment operations
separate from the pure (monadic) operations.

\begin{spec}
IO qualifying spec {
  import /Library/Base

  sort Filename = String
  sort Time     = Nat          % Not a fixnum
  sort Byte     = {x : Nat | 0 <= x &  x < 256} 

  op getCurrentDirectory   : () -> Filename
  op fileExistsAndReadable : Filename -> Boolean
  op fileWriteTime         : Filename -> Time
  op currentTime           : () -> Time

  op fileWritable          : Filename -> Boolean
  op readBytesFromFile     : Filename -> List Byte
  op writeBytesToFile      : List Byte * Filename -> ()

  op writeStringToFile : String *  Filename -> ()
  def writeStringToFile (string, filename) =
    writeBytesToFile (map ord (explode string),
		      filename)


}
\end{spec}

