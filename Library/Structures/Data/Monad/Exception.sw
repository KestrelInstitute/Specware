(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Exception monad

An abstract specification for an exception monad. Needs work.
What are the axioms?
*)

Monad qualifying spec
  import ../Monad

  type Exception

  op raise : [a] Exception -> Monad a
  op catch : [a] Monad a -> (Exception -> Monad a) -> Monad a

  % op throw : fa (a) Exception -> Monad a
  % axiom throw_is_raise is throw = raise

%%% Not sure if this should go in IO.sw
#translate Haskell Thy_Morphism
  type Monad.Monad -> IO
  type Monad.Exception -> IOError
  Monad.catch -> catch
  Monad.raise -> ioError
#end
endspec
