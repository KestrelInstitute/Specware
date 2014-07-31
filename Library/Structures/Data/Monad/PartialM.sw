(* The partiality monad: for computations with full recursion *)

PartialM = Monad qualifying spec

  % A computation of type a in PartialM is, intuitively, an object of
  % type a that is defined by a fixed-point. All we can ask of such a
  % computation is whether it is defined after the nth step of
  % iterating the fixed-point. Once it has become defined, however,
  % iterating the fixed-point any more times keeps the same value.
  type Monad a = { f : Nat -> Option a
                    | fa (n1,n2) n1 <= n2 => f n1 ~= None => f n1 = f n2 }

  op [a] return (x:a) : Monad a = fn _ -> Some x

  op [a,b] monadBind (m: Monad a, f:a -> Monad b) : Monad b =
    fn n -> case m n of
              | Some x -> f x n
              | None -> None

  op [a,b] monadSeq (m1:Monad a, m2:Monad b) : Monad b = monadBind (m1, fn _ -> m2)


  % Monad axioms

  theorem left_unit is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g)


  % Proofs

  proof Isa Monad__monadBind_Obligation_subtype
    apply (simp add: Monad__Monad__subtype_pred_def, rule allI, rule allI)
    apply (case_tac "m n1", auto)
    apply (subgoal_tac "m n2 = m n1 \<and> f a n2 = f a n1")
    apply auto[1]
    proof -
      fix n1 n2 a y
      assume hyp_f: "\<forall>x n1 n2. n1 <= n2 \<and> (\<exists>y. f x n1 = Some y) --> f x n1 = f x n2"
      assume hyp_m: "\<forall>n1 n2. n1 <= n2  \<and> (\<exists>y. m n1 = Some y) --> m n1 = m n2"
      assume m_eq: "m n1 = Some a"
      assume f_eq: "f a n1 = Some y"
      assume leq: "n1 <= n2"
      show "m n2 = m n1 \<and> f a n2 = f a n1"
        apply (rule conjI)
        apply (rule HOL.sym,rule mp[OF spec[OF spec[OF hyp_m]]])
        apply (simp add: m_eq leq)
        apply (rule HOL.sym,rule mp[OF spec[OF spec[OF spec[OF hyp_f]]]])
        apply (simp add: f_eq leq)
        done
      qed
  end-proof

  proof Isa Monad__return_Obligation_subtype
    by (simp add: Monad__Monad__subtype_pred_def)
  end-proof

  proof Isa left_unit
    by (auto simp add: Monad__return_def Monad__monadBind_def)
  end-proof

  proof Isa right_unit
    apply (rule ext, auto simp add: Monad__return_def Monad__monadBind_def)
    apply (unfold Monad__return_def)
    apply (case_tac "m x", auto)
    done
  end-proof

  proof Isa associativity
    apply (auto simp add: Monad__return_def Monad__monadBind_def)
    apply (rule ext, case_tac "m n", auto)
    done
  end-proof

  proof Isa non_binding_sequence
    by (simp add: Monad__monadSeq_def)
  end-proof


end-spec
