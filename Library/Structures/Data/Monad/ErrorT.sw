
ErrorT = MonadTrans qualifying spec
  import ../Monad

  % Something that could be a value of type a or could be an error
  type MaybeError a = | Ok a | Error String

  % The error transformer type
  type Monad a = Monad.Monad (MaybeError a)

  % All the ops for the error transformer

  op [a] return (x:a) : Monad a =
    Monad.return (Ok x)

  op [a,b] monadBind (m:Monad a, f:a -> Monad b) : Monad b =
    Monad.monadBind (m, (fn x -> case x of
                                   | Ok a -> f a
                                   | Error str -> return (Error str)))

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b =
    monadBind (m1, fn _ -> m2)

  % The monad theorems

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


  % The monadic lifting operator

  op [a] monadLift (m:Monad.Monad a) : Monad a =
    Monad.monadBind (m, (fn x -> Monad.return (Ok x)))

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
    apply (auto simp add: MonadTrans__return_def MonadTrans__monadBind_def)
    apply (rule HOL.trans[OF _ Monad__right_unit])
    apply (rule arg_cong[of _ Monad__return])
    apply (rule ext)
    apply (case_tac x)
    apply (unfold MonadTrans__return_def)
    apply auto
    done
  end-proof

  proof Isa associativity
    apply (auto simp add: MonadTrans__monadBind_def Monad__associativity[symmetric])
    apply (rule arg_cong[of _ _ "\<lambda>f . Monad__monadBind (m, f)"])
    apply (rule ext, case_tac x)
    apply (auto simp add: Monad__left_unit)
    done
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
