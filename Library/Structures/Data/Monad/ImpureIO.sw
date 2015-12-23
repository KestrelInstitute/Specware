(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* 
 * This is the signature for a collection of primitive IO functions implemented
 * in Lisp. See Handwritten/Impure.lisp. Each of the functions here has
 * a (relatively) pure monadic counterpart under /Library/IO
 *)
ImpureIO qualifying spec

  type IO.Stream

  op IO.stdin  : Stream
  op IO.stdout : Stream

  type IO.FilePath = String

  type OpenMode =
    | Read
    | Write
    | ReadWrite
    | Append

  type Result a =
    | Ok a
    | EOF String
    | FileError ((Option Nat) * String * String)
    | StreamError (String * String * Nat * String)

  op openFileRead      : FilePath -> Result Stream
  op openFileWrite     : FilePath -> Result Stream
  op openFileReadWrite : FilePath -> Result Stream
  op openFileAppend    : FilePath -> Result Stream

  op openFile : FilePath -> OpenMode -> Result Stream
  def openFile name typ =
    case typ of
      | Read -> openFileRead name
      | Write -> openFileWrite name
      | ReadWrite -> openFileReadWrite name
      | Append -> openFileAppend name

  op closeFile    : Stream           -> Result ()
  op readChar     : Stream           -> Result Char
  op atEOF?       : Stream           -> Bool
  op readLine     : Stream           -> Result String (* Reads a line terminated by newline from the stream and returns the string less the newline *)
  op readString   : Stream           -> Result String
 %op readContents : Stream           -> Result String (* Returns the contents of a stream as a string. Newlines intact *)
  op writeChar    : Stream -> Char   -> Result ()
  op writeString  : Stream -> String -> Result ()     (* Write a string to a stream.  *)
  op writeLine    : Stream -> String -> Result ()     (* Write a string to a stream and terminates it with a newline.  *)
  op flushStream  : Stream           -> Result ()     (* Flushes an output stream *)
endspec

