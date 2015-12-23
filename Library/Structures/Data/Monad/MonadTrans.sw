(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
 * A spec for a monad transformer. Since Specware only allows
 * predicative 1st-order polymorphism, we model transformers as specs
 * that have two monads, an output monad Monad and an input monad
 * InputMonad.
 *)

MonadTrans qualifying spec
  import /Library/Structures/Data/Monad
  import translate /Library/Structures/Data/Monad by {Monad._ +-> MonadTrans._}

  op [a] monadLift : Monad.Monad a -> MonadTrans.Monad a

  axiom lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = return x
  axiom lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))

end-spec
