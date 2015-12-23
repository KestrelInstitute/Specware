(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* The identity monad *)

IdentityM_spec = IdentityM qualifying spec
  type Monad a = a

  op [a,b] monadBind (m: Monad a, f: a -> Monad b) : Monad b = f m
  op [a,b] monadSeq (m1: Monad a, m2: Monad b) : Monad b = m2
  op [a] return (x:a) : Monad a = x

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g) 

  proof Isa left_unit
    by (simp add: IdentityM__return_def IdentityM__monadBind_def)
  end-proof

  proof Isa right_unit
    by (simp add: IdentityM__return_def IdentityM__monadBind_def)
  end-proof

  proof Isa associativity
    by (simp add: IdentityM__monadBind_def)
  end-proof

  proof Isa non_binding_sequence
    by (auto simp add: IdentityM__monadSeq_def IdentityM__monadBind_def)
  end-proof


  % Add "congruence rules" for Isabelle

(*
  theorem monadBind_cong is [a,b]
    fa (m1,m2,f1:a -> Monad b,f2) m1 = m2 => f1 m1 = f2 m2 => monadBind(m1,f1) = monadBind(m2,f2)

  proof Isa monadBind_cong (fundef_cong)
    by (auto simp add: IdentityM__monadBind_def)
  end-proof
*)

  proof Isa -verbatim
    lemma IdentityM__monadBind_cong [fundef_cong]:
      "[| m1 = m2; f1 m1 = f2 m2 |] ==> IdentityM__monadBind(m1,f1) = IdentityM__monadBind(m2,f2)"
      by (auto simp add: IdentityM__monadBind_def)
  end-proof

end-spec


% The morphism that instantiates a monad into the identity monad
IdentityM = morphism ../Monad -> IdentityM_spec { Monad._ +-> IdentityM._ }
