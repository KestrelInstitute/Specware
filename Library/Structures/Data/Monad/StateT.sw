(* The State monad transformer *)

spec
  %import translate MonadTrans by {Monad.Monad +-> Monad}
  import MonadTrans

  type St
  axiom St_nonempty is ex(st:St) true

  type Monad a = St -> InputMonad (St * a)

  refine def [a] return (x:a) : Monad a =
    fn st -> inputReturn (st, x)

  refine def [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    fn st -> inputMonadBind (m st, (fn (st', x) -> f x st'))

  refine def [a] monadLift (m:InputMonad a) : Monad a =
    fn st -> inputMonadBind (m, (fn x -> inputReturn (st, x)))

  theorem lift_return is [a]
    fa (x:a) monadLift (inputReturn x) = return x

  proof Isa lift_return
    sorry
  end-proof

end-spec
