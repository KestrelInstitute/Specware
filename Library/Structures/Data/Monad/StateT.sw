(* The State monad transformer *)

StateT = spec
  %import translate ../Monad by { Monad._ +-> InputMonad._ }
  import ../Monad

  % The state type
  type St
  axiom St_nonempty is ex(st:St) true


  % A complete copy of the Monad spec, using the OutputMonad qualifier

  type OutputMonad.Monad a = St -> Monad.Monad (St * a)

  op [a] OutputMonad.return (x:a) : OutputMonad.Monad a =
    fn st -> Monad.return (st, x)

  op [a,b] OutputMonad.monadBind (m:OutputMonad.Monad a,
                                  f:a -> OutputMonad.Monad b) : OutputMonad.Monad b =
    fn st -> Monad.monadBind (m st, (fn (st', x) -> f x st'))

  op [a,b] OutputMonad.monadSeq (m1:OutputMonad.Monad a, m2:OutputMonad.Monad b) : OutputMonad.Monad b =
    OutputMonad.monadBind (m1, fn _ -> m2)

  theorem OutputMonad.left_unit  is [a,b]
    fa (f: a -> OutputMonad.Monad b, x: a)
      OutputMonad.monadBind (OutputMonad.return x, f) = f x

  theorem OutputMonad.right_unit is [a]
    fa (m: OutputMonad.Monad a) OutputMonad.monadBind (m, OutputMonad.return) = m

  theorem OutputMonad.associativity is [a,b,c]
    fa (m: OutputMonad.Monad a, f: a -> OutputMonad.Monad b, h: b -> OutputMonad.Monad c)
      OutputMonad.monadBind (m, fn x -> OutputMonad.monadBind (f x, h))
        = OutputMonad.monadBind (OutputMonad.monadBind (m, f), h)

  theorem OutputMonad.non_binding_sequence is [a]
    fa (f : OutputMonad.Monad a, g: OutputMonad.Monad a)
    OutputMonad.monadSeq (f, g) = OutputMonad.monadBind (f, fn _ -> g) 


  % The monadic lifting operator for StateT

  op [a] Monad.monadLift (m:Monad.Monad a) : OutputMonad.Monad a =
    fn st -> Monad.monadBind (m, (fn x -> Monad.return (st, x)))

  theorem Monad.lift_return is [a]
    fa (x:a) monadLift (Monad.return x) = OutputMonad.return x


  % Proofs

  proof Isa OutputMonad.left_unit
    by (auto simp add: OutputMonad__return_def OutputMonad__monadBind_def Monad__left_unit)
  end-proof

  proof Isa OutputMonad.right_unit
    by (auto simp add: OutputMonad__return_def OutputMonad__monadBind_def Monad__right_unit)
  end-proof

  proof Isa OutputMonad.associativity
    by (auto simp add: OutputMonad__monadBind_def Monad__associativity[symmetric]
           split_eta[symmetric, of "\<lambda> x . Monad__monadBind
                 (case x of (st_cqt, x) => f x st_cqt,
                  \<lambda>(st_cqt, x). h x st_cqt)"])
  end-proof

  proof Isa OutputMonad.non_binding_sequence
    by (simp add: OutputMonad__monadSeq_def)
  end-proof

  proof Isa lift_return
    by (simp add: OutputMonad__return_def Monad__monadLift_def Monad__left_unit)    
  end-proof

end-spec


% The morphism that takes an input monad Monad.Monad and builds a
% state monad OutputMonad.Monad from it
StateT_M = morphism ../Monad -> StateT { }

% The state monad
StateM = ../Monad[StateT_M][Identity#Identity_M]

% FIXME: why do neither of these work? None of the OutputMonad._ names get defined...
StateM2 = Identity#IdentityM[StateT_M]
StateM3 = ../Monad[Identity#Identity_M][StateT_M]

% FIXME: this also fails to add the OutputMonad._ names
StateM_double = (translate StateM by {Monad._ +-> Monad1._, OutputMonad._ +-> Monad._ })[StateT_M]


% The morphism that applies StateT "backwards", by refining the monad
% in the input spec into a state monad, which is itself defined in
% terms of a newly-introduced "underneath" monad
StateT2 = translate StateT by { Monad._ +-> InputMonad._, OutputMonad._ +-> Monad._ }

StateT_M_out = morphism ../Monad -> StateT2 { }

StateM4 = ../Monad[StateT_M_out]
StateM4_double = (../Monad[StateT_M_out])[StateT_M]


% Another approach: the transformer has InputMonad._ and OutputMonad._
% distinct from Monad._

StateT_io = spec
  import translate ../Monad by { Monad._ +-> InputMonad._ }

  % The state type
  type St
  axiom St_nonempty is ex(st:St) true


  % A complete copy of the Monad spec, using the OutputMonad qualifier

  type OutputMonad.Monad a = St -> InputMonad.Monad (St * a)

  op [a] OutputMonad.return (x:a) : OutputMonad.Monad a =
    fn st -> InputMonad.return (st, x)

  op [a,b] OutputMonad.monadBind (m:OutputMonad.Monad a,
                                  f:a -> OutputMonad.Monad b) : OutputMonad.Monad b =
    fn st -> InputMonad.monadBind (m st, (fn (st', x) -> f x st'))

  op [a,b] OutputMonad.monadSeq (m1:OutputMonad.Monad a, m2:OutputMonad.Monad b) : OutputMonad.Monad b =
    OutputMonad.monadBind (m1, fn _ -> m2)

  theorem OutputMonad.left_unit  is [a,b]
    fa (f: a -> OutputMonad.Monad b, x: a)
      OutputMonad.monadBind (OutputMonad.return x, f) = f x

  theorem OutputMonad.right_unit is [a]
    fa (m: OutputMonad.Monad a) OutputMonad.monadBind (m, OutputMonad.return) = m

  theorem OutputMonad.associativity is [a,b,c]
    fa (m: OutputMonad.Monad a, f: a -> OutputMonad.Monad b, h: b -> OutputMonad.Monad c)
      OutputMonad.monadBind (m, fn x -> OutputMonad.monadBind (f x, h))
        = OutputMonad.monadBind (OutputMonad.monadBind (m, f), h)

  theorem OutputMonad.non_binding_sequence is [a]
    fa (f : OutputMonad.Monad a, g: OutputMonad.Monad a)
    OutputMonad.monadSeq (f, g) = OutputMonad.monadBind (f, fn _ -> g) 


  % The monadic lifting operator for StateT

  op [a] monadLift (m:InputMonad.Monad a) : OutputMonad.Monad a =
    fn st -> InputMonad.monadBind (m, (fn x -> InputMonad.return (st, x)))

  theorem lift_return is [a]
    fa (x:a) monadLift (InputMonad.return x) = OutputMonad.return x


  % Proofs

  proof Isa OutputMonad.left_unit
    by (auto simp add: OutputMonad__return_def OutputMonad__monadBind_def Monad__left_unit)
  end-proof

  proof Isa OutputMonad.right_unit
    by (auto simp add: OutputMonad__return_def OutputMonad__monadBind_def Monad__right_unit)
  end-proof

  proof Isa OutputMonad.associativity
    by (auto simp add: OutputMonad__monadBind_def Monad__associativity[symmetric]
           split_eta[symmetric, of "\<lambda> x . Monad__monadBind
                 (case x of (st_cqt, x) => f x st_cqt,
                  \<lambda>(st_cqt, x). h x st_cqt)"])
  end-proof

  proof Isa OutputMonad.non_binding_sequence
    by (simp add: OutputMonad__monadSeq_def)
  end-proof

  proof Isa lift_return
    by (simp add: OutputMonad__return_def monadLift_def Monad__left_unit)    
  end-proof

end-spec


% The morphism that takes an input monad Monad.Monad and builds a
% state monad OutputMonad.Monad from it
StateT_io_M = morphism ../Monad -> StateT_io { Monad._ +-> InputMonad._ }

StateM_io = (translate ../Monad[StateT_io_M] by {InputMonad._ +-> Monad._})[Identity#Identity_M]

% FIXME: Why does this approach not work? Again, no OutputMonad._
% names. Also, the theorems have Monad._ names, not InputMonad._ names
StateM_io2 = Identity#IdentityM[StateT_io_M]
StateM_io3 = ../Monad[Identity#Identity_M][StateT_io_M]

% The morphism that applies StateT "backwards", by refining the monad
% in the input spec into a state monad, which is itself defined in
% terms of a newly-introduced "underneath" monad
StateT_io_M_out = morphism ../Monad -> StateT_io { Monad._ +-> OutputMonad._ }

% FIXME: why does this one not work?
StateM_io4 = (translate ../Monad[StateT_io_M_out] by { InputMonad._ +-> Monad._ })[Identity#Identity_M]


(*

 * FIXME: the following does not work, because we cannot (or, at
 * least, I cannot figure out how to) turn the axioms in Monad and
 * MonadTrans into theorems that I can prove here.
 *
 * Also, when I try to prove lift_return1 in Isabelle, it refers to
 * the old, imported version of OutputMonad.return instead of the new,
 * defined version
 *)

(*
spec
  import MonadTrans

  type St
  axiom St_nonempty is ex(st:St) true

  type OutputMonad.Monad a = St -> Monad.Monad (St * a)

  refine def [a] OutputMonad.return (x:a) : OutputMonad.Monad a =
    fn st -> Monad.return (st, x)

  refine def [a,b] OutputMonad.monadBind (m, f) : OutputMonad.Monad b =
    fn st -> Monad.monadBind (m st, (fn (st', x) -> f x st'))

  refine def [a] monadLift (m:Monad.Monad a) : OutputMonad.Monad a =
    fn st -> Monad.monadBind (m, (fn x -> Monad.return (st, x)))

  % FIXME: we want to turn the axiom lift_return into a theorem, but
  % this currently doesn't work, so we give this a different name
  theorem lift_return1 is [a]
    fa (x:a) monadLift (Monad.return x) = OutputMonad.return x

  proof Isa lift_return1
    sorry
  end-proof

end-spec
*)
