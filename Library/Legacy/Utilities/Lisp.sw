\section{Lisp Primitives}

These are based upon Common Lisp primitives.

\begin{spec}
Lisp qualifying spec {

  import /Library/Base

  sort LispCell

  op nat          : Nat                       -> LispCell
  op char         : Char                      -> LispCell
  op bool         : Boolean                   -> LispCell
  op string       : String                    -> LispCell
  op LispString   : LispCell                  -> String

  op symbol       : String * String           -> LispCell

  op nil          : ()                        -> LispCell
  op car          : LispCell                  -> LispCell
  op cdr          : LispCell                  -> LispCell
  op cons         : LispCell * LispCell       -> LispCell
  op list         : List LispCell             -> LispCell
  op ++ infixl 11 : LispCell * LispCell       -> LispCell

  op quote        : LispCell                  -> LispCell
  op apply        : LispCell * List LispCell  -> LispCell
  op eval         : LispCell                  -> LispCell

  op cell         : fa(A) A                   -> LispCell
  op uncell       : fa(A) LispCell            -> A

  op null         : LispCell -> Boolean

  %% No defs here -- see ...
}
\end{spec}
