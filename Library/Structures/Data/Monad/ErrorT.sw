
ErrorT = spec
  import ../Monad

  % Something that could be a value of type a or could be an error
  type MaybeError a = | Ok a | Error String

  % The error transformer type
  type MonadTrans.Monad a = Monad.Monad (MaybeError a)

  % All the ops for the error transformer

  op [a] MonadTrans.return (x:a) : MonadTrans.Monad a =
    Monad.return (Ok x)

  op [a,b] MonadTrans.monadBind (m:MonadTrans.Monad a,
                                  f:a -> MonadTrans.Monad b) : MonadTrans.Monad b =
    Monad.monadBind (m, (fn x -> case x of
                                   | Ok a -> f a
                                   | Error str -> return (Error str)))

  op [a,b] MonadTrans.monadSeq (m1:MonadTrans.Monad a, m2:MonadTrans.Monad b) : MonadTrans.Monad b =
    MonadTrans.monadBind (m1, fn _ -> m2)

  % The monad theorems

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


  % The monadic lifting operator

  op [a] MonadTrans.monadLift (m:Monad.Monad a) : MonadTrans.Monad a =
    Monad.monadBind (m, (fn x -> Monad.return (Ok x)))

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
    apply (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def)
    apply (rule HOL.trans[OF _ Monad__right_unit])
    apply (rule arg_cong[of _ Monad__return])
    apply (rule ext)
    apply (case_tac x)
    apply (unfold MonadTrans__return_def)
    apply auto
    done
  end-proof

  proof Isa MonadTrans.associativity
    sorry
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


% The morphism showing that any ErrorT monad is a monad
ErrorT_M = morphism ../Monad -> ErrorT { Monad._ +-> MonadTrans._ }

% The morphism showing that ErrorT is a monad transformer
ErrorT_isa_Transformer = morphism MonadTrans -> ErrorT { }

% Example 1: the error monad
ErrorM = ErrorT[Identity#Identity_M]

% Example 2: the state-error monad
StateErrorM =
  (translate
     (translate StateT by {MonadTrans._ +-> Monad2._})[ErrorT_M]
     by { MonadTrans._ +-> Monad1._})[Identity#Identity_M]
