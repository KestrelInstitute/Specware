(* The State monad transformer *)

StateT = spec
  %import translate ../Monad by { Monad._ +-> InputMonad._ }
  import ../Monad

  % The state type
  type MonadTrans.St
  axiom MonadTrans.St_nonempty is ex(st:St) true


  % A complete copy of the Monad spec, using the MonadTrans qualifier
  % and proving all the theorems

  type MonadTrans.Monad a = St -> Monad.Monad (St * a)

  op [a] MonadTrans.return (x:a) : MonadTrans.Monad a =
    fn st -> Monad.return (st, x)

  op [a,b] MonadTrans.monadBind (m:MonadTrans.Monad a,
                                  f:a -> MonadTrans.Monad b) : MonadTrans.Monad b =
    fn st -> Monad.monadBind (m st, (fn (st', x) -> f x st'))

  op [a,b] MonadTrans.monadSeq (m1:MonadTrans.Monad a, m2:MonadTrans.Monad b) : MonadTrans.Monad b =
    MonadTrans.monadBind (m1, fn _ -> m2)

  theorem MonadTrans.left_unit  is [a,b]
    fa (f: a -> MonadTrans.Monad b, x: a)
      MonadTrans.monadBind (MonadTrans.return x, f) = f x

  theorem MonadTrans.right_unit is [a]
    fa (m: MonadTrans.Monad a) MonadTrans.monadBind (m, MonadTrans.return) = m

  theorem MonadTrans.associativity is [a,b,c]
    fa (m: MonadTrans.Monad a, f: a -> MonadTrans.Monad b, h: b -> MonadTrans.Monad c)
      MonadTrans.monadBind (m, fn x -> MonadTrans.monadBind (f x, h))
        = MonadTrans.monadBind (MonadTrans.monadBind (m, f), h)

  theorem MonadTrans.non_binding_sequence is [a]
    fa (f : MonadTrans.Monad a, g: MonadTrans.Monad a)
    MonadTrans.monadSeq (f, g) = MonadTrans.monadBind (f, fn _ -> g) 


  % The monadic lifting operator for StateT

  op [a] MonadTrans.monadLift (m:Monad.Monad a) : MonadTrans.Monad a =
    fn st -> Monad.monadBind (m, (fn x -> Monad.return (st, x)))

  theorem MonadTrans.lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = MonadTrans.return x

  theorem MonadTrans.lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      MonadTrans.monadBind (monadLift m, fn x -> monadLift (f x))


  % Proofs

  proof Isa MonadTrans.left_unit
    by (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def Monad__left_unit)
  end-proof

  proof Isa MonadTrans.right_unit
    by (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def Monad__right_unit)
  end-proof

  proof Isa MonadTrans.associativity
    by (auto simp add: MonadTrans__monadBind_def Monad__associativity[symmetric]
           split_eta[symmetric, of "\<lambda> x . Monad__monadBind
                 (case x of (st_cqt, x) => f x st_cqt,
                  \<lambda>(st_cqt, x). h x st_cqt)"])
  end-proof

  proof Isa MonadTrans.non_binding_sequence
    by (simp add: MonadTrans__monadSeq_def)
  end-proof

  proof Isa lift_return
    by (simp add: MonadTrans__return_def MonadTrans__monadLift_def Monad__left_unit)    
  end-proof

  proof Isa lift_bind
    by (simp add: MonadTrans__monadBind_def MonadTrans__monadLift_def
          Monad__associativity[symmetric] Monad__left_unit)
  end-proof

end-spec


% The morphism showing that any StateT monad is a monad
StateT_M = morphism ../Monad -> StateT { Monad._ +-> MonadTrans._ }

% The morphism showing that StateT is a monad transformer
StateT_isa_Transformer = morphism MonadTrans -> StateT { }

% Example 1: the state monad
StateM = StateT[Identity#Identity_M]

% Example 2: two nested applications of the state monad, Monad2.Monad
% which is defined in terms of Monad1.Monad
StateDoubleM_1 = (translate StateT by {MonadTrans._ +-> Monad2._})[StateT_M]
StateDoubleM_2 = translate StateDoubleM_1 by {MonadTrans._ +-> Monad1._}
StateDoubleM_3 = StateDoubleM_2[Identity#Identity_M]

StateDoubleM =
  (translate (translate StateT by {MonadTrans._ +-> Monad2._})[StateT_M]
     by { MonadTrans._ +-> Monad1._})[Identity#Identity_M]
