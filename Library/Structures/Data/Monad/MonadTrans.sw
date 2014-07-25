(*
 * A spec for a monad transformer. Since Specware only allows
 * predicative 1st-order polymorphism, we model transformers as specs
 * that have two monads, an output monad Monad and an input monad
 * InputMonad.
 *)

spec
  import /Library/Structures/Data/Monad
  import translate /Library/Structures/Data/Monad
    by { Monad +-> InputMonad, return +-> inputReturn,
        monadBind +-> inputMonadBind, monadSeq +-> inputMonadSeq,
        left_unit +-> input_left_unit, right_unit +-> input_right_unit,
        associativity +-> input_associativity,
        non_binding_sequence +-> input_non_binding_sequence
        }
  %import translate /Library/Structures/Data/Monad by {Monad._ +-> InputMonad._}

  op [a] monadLift : InputMonad.Monad a -> Monad.Monad a

  axiom lift_return is [a]
    fa (x:a) monadLift (InputMonad.return x) = return x
  axiom lift_bind is [a,b]
    fa (m:InputMonad.Monad a, f:a -> InputMonad.Monad b)
      monadLift (InputMonad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))

end-spec
