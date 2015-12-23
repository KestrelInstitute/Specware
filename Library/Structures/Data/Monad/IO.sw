(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IO qualifying spec
  import Exception
  import ImpureIO

  op fileError : (Option Nat * String * String) -> Exception
  op eof : String -> Exception

  op openFile : FilePath -> OpenMode -> Monad Stream
  def openFile path mode =
    case ImpureIO.openFile path mode of
      | Ok stream -> return stream
      | FileError err -> raise (fileError err)

  op closeFile : Stream -> Monad ()
  def closeFile stream =
    case ImpureIO.closeFile stream of
      | Ok _ -> return ()
      | FileError err -> raise (fileError err)

  op readChar : Stream -> Monad Char
  def readChar stream =
    case ImpureIO.readChar stream of
      | Ok chr -> return chr
      | EOF str -> raise (eof str)

  op readString : Stream -> Monad String
  def readString stream =
    case ImpureIO.readString stream of
      | Ok line -> return line
      | EOF str -> raise (eof str)

  op readLine : Stream -> Monad String
  def readLine stream =
    case ImpureIO.readLine stream of
      | Ok line -> return line
      | EOF str -> raise (eof str)

  op readContents : Stream -> Monad String
  % def readContents stream =
    % case ImpureIO.readContents stream of
      % | Ok txt -> return txt
      % | EOF str -> raise (eof str)

  op atEOF? : Stream -> Monad Bool
  def atEOF? strm = return (ImpureIO.atEOF? strm)

  op writeLine : Stream -> String -> Monad ()
  def writeLine strm line =
    case ImpureIO.writeLine strm line of
      | Ok _ -> return ()
      
  op writeString : Stream -> String -> Monad ()
  def writeString strm line =
    case ImpureIO.writeString strm line of
      | Ok _ -> return ()

  op flushStream : Stream -> Monad ()
  def flushStream strm =
    case ImpureIO.flushStream strm of
      | Ok _ -> return ()

#translate Haskell Thy_Morphism IO
  type IO.Monad -> IO
  type IO.Stream -> Handle
  type IO.FilePath -> FilePath
  type ImpureIO.OpenMode -> IOMode
  IO.fileError -> IOError
  IO.eof -> userError
  IO.openFile -> openFile
  IO.closeFile -> hClose
  IO.readChar -> hGetChar
  IO.readString -> hGetLine
  IO.readLine -> hGetLine
  IO.readContents -> hGetContents
  IO.atEOF? -> hIsEOF
  IO.writeLine -> hPutStrLn
  IO.writeString -> hPutStr
  IO.flushStream -> hClose
#end

endspec
