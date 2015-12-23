(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Lisp Primitives 

These are based upon Common Lisp primitives.
*)

Lisp qualifying spec

  type LispCells = List LispCell
  type LispCell

  op nat          : Nat                   -> LispCell
  op char         : Char                  -> LispCell
  op bool         : Bool                  -> LispCell
  op string       : String                -> LispCell
  op LispString   : LispCell              -> String

  op symbol       : String * String       -> LispCell
  op findSymbol   : String * String       -> LispCell

  op nil          : ()                    -> LispCell
  op car          : LispCell              -> LispCell
  op cdr          : LispCell              -> LispCell
  op cons         : LispCell * LispCell   -> LispCell
  op list         : LispCells             -> LispCell
  op ++ infixl 25 : LispCell * LispCell   -> LispCell

  op quote        : LispCell             -> LispCell
  op apply        : LispCell * LispCells -> LispCell
  op eval         : LispCell             -> LispCell

  op cell         : [A] A                -> LispCell
  op uncell       : [A] LispCell         -> A

  op null         : LispCell -> Bool

  %% No defs here -- see ...
end-spec
