\section{Low Level Impure IO operations}

This is a poorly named file in a poorly named directory. The idea,
however, is to keep the impure environment operations
separate from the pure (monadic) operations.

\begin{spec}
IO qualifying spec {
  import /Library/Base

  sort Time = Nat          % Not a fixnum

  op getEnv : String -> Option String
  op getCurrentDirectory : () -> String
  op fileExistsAndReadable : String -> Boolean
  op fileWriteTime : String -> Time
}
\end{spec}

