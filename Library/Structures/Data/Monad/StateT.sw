(* The State monad transformer *)

StateT = MonadTrans qualifying spec
  %import translate ../Monad by { Monad._ +-> InputMonad._ }
  import ../Monad

  % The state type
  type St
  axiom St_nonempty is ex(st:St) true


  % A complete copy of the Monad spec, using the MonadTrans qualifier
  % and proving all the theorems

  type Monad a = St -> Monad.Monad (St * a)

  op [a] return (x:a) : Monad a =
    fn st -> Monad.return (st, x)

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    fn st -> Monad.monadBind (m st, (fn (st', x) -> f x st'))

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a)
      monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h))
        = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f : Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g) 


  % The monadic lifting operator for StateT

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    fn st -> Monad.monadBind (m, (fn x -> Monad.return (st, x)))

  theorem lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = return x

  theorem lift_bind is [a,b]
    fa (m:Monad.Monad a, f:a -> Monad.Monad b)
      monadLift (Monad.monadBind (m,f)) =
      monadBind (monadLift m, fn x -> monadLift (f x))


  % Proofs

  proof Isa left_unit
    by (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def Monad__left_unit)
  end-proof

  proof Isa right_unit
    by (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def Monad__right_unit)
  end-proof

  proof Isa associativity
    by (auto simp add: MonadTrans__monadBind_def Monad__associativity[symmetric]
           split_eta[symmetric, of "\<lambda> x . Monad__monadBind
                 (case x of (st_cqt, x) => f x st_cqt,
                  \<lambda>(st_cqt, x). h x st_cqt)"])
  end-proof

  proof Isa non_binding_sequence
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
StateDoubleM =
  (translate (translate StateT by {MonadTrans._ +-> Monad2._})[StateT_M]
     by { MonadTrans._ +-> Monad1._})[Identity#Identity_M]
