Set qualifying spec

  (* In higher-order logic, it is customary to define a set as a predicate:
  the predicate is true exactly for (i.e. for all and only) the elements of
  the set.

  In this spec we follow that customary approach, which is very clear and
  simple. All the types and ops in this spec are defined, i.e. this spec is a
  definitional extension; therefore, it is readily seen to be consistent.

  The fact that type `Set' is defined means that sets as specified here cannot
  be later refined into a representation different from predicates. This should
  not be a problem because sets may be infinite and therefore cannot be refined
  to be executable (because equality is undecidable). Sets as defined here are
  useful for specification purposes, not for execution. Finite sets as defined
  in spec `FiniteSet' can instead be refined to be executable. *)

  type Predicate a = a -> Bool

  type Set a = Predicate a

  % membership:

  op [a] in? (x:a, s: Set a) infixl 20 : Bool = s x

  op [a] nin? (x:a, s: Set a) infixl 20 : Bool = ~(x in? s)

  % Lifting a predicate from elements to regularized sets
  op [a] Set_P (Pa: a -> Bool) (s: Set a): Bool =
    fa(x: a) ~(Pa x) => x nin? s     % contrapositive: x in? s => Pa x
  proof Isa
    by (simp add: Set_P_def)
  end-proof

  % (strict) sub/superset:

  op [a] <= (s1: Set a, s2: Set a) infixl 20 : Bool =
    fa(x) x in? s1 => x in? s2

  op [a] < (s1: Set a, s2: Set a) infixl 20 : Bool = (s1 <= s2 && s1 ~= s2)

  op [a] >= (s1: Set a, s2: Set a) infixl 20 : Bool = (s2 <= s1)

  op [a] > (s1: Set a, s2: Set a) infixl 20 : Bool = (s2 < s1)

  % complement, intersection, and union (lift `~', `&&', and `||' to sets):

  op [a] ~~ (s: Set a) : Set a = fn x:a -> x nin? s

  op [a] /\ (s1: Set a, s2: Set a) infixr 25 : Set a =
    fn x:a -> x in? s1 && x in? s2

  op [a] \/ (s1: Set a, s2: Set a) infixr 24 : Set a =
    fn x:a -> x in? s1 || x in? s2

  % intersection/union of all sets in a set:

  op [a] //\\ (ss: Set (Set a)) : Set a =
    fn x:a -> (fa(s) s in? ss => x in? s)

  op [a] \\// (ss: Set (Set a)) : Set a =
    fn x:a -> (ex(s) s in? ss && x in? s)

  % lift `=>' and `<=>' to sets:

  op [a] ==> (s1: Set a, s2: Set a) infixr 23 : Set a =
    fn x:a -> x in? s1 => x in? s2

  op [a] <==> (s1: Set a, s2: Set a) infixr 22 : Set a =
    fn x:a -> x in? s1 <=> x in? s2

  % difference:

  op [a] -- (s1: Set a, s2: Set a) infixl 25 : Set a =
    fn x:a -> x in? s1 && x nin? s2

  % cartesian product:

  op [a,b] * (s1: Set a, s2: Set b) infixl 27 : Set (a * b) =
    fn (x:a,y:b) -> x in? s1 && y in? s2

  % powerset:

  op [a] power (s: Set a) : Set (Set a) =
    fn sub: Set a -> sub <= s

  % set with no elements (lift `false' to sets):

  op empty : [a] Set a = fn _ -> false
  proof Isa
    by (auto simp add: mem_def)
  end-proof

  op [a] empty? (s: Set a) : Bool = (s = empty)
  proof Isa [simp] end-proof

  % sets with at least 1 element:

  op [a] nonEmpty? (s: Set a) : Bool = (s ~= empty)

  type NonEmptySet a = (Set a | nonEmpty?)

  % set with all elements (lift `true' to sets):

  op full : [a] Set a = fn _ -> true
  proof Isa
    by (auto simp add: mem_def)
  end-proof

  op [a] full? (s: Set a) : Bool = (s = full)
  proof Isa [simp] end-proof

  % sets with at least 1 missing element:

  op [a] nonFull? (s: Set a) : Bool = (s ~= full)
  proof Isa [simp] end-proof

  type NonFullSet a = (Set a | nonFull?)

  % sets with exactly one element:

  op [a] single(*ton*) (x:a) : Set a = fn y:a -> y = x

  op [a] single? (s:Set a) : Bool = (ex(x:a) s = single x)
  proof Isa [simp] end-proof

  op [a] onlyMemberOf (x:a, s: Set a) infixl 20 : Bool =
    single? s && x in? s
  proof Isa [simp] end-proof

  proof Isa -verbatim
  lemma Set_single_simp [simp]:
  "Set__single x = {x}"
   by (rule set_ext, simp, simp add: mem_def Set__single_def)
  end-proof

  type SingletonSet a = (Set a | single?)

  op [a] theMember (s: SingletonSet a) : a = the(x:a) x in? s
  proof Isa theMember__stp_Obligation_the
    apply(auto simp add: Set__single_p__stp_def)
  end-proof

  % add member to set (triangle points towards set):

  op [a] <| (s: Set a, x:a) infixl 25 : Set a = s \/ single x

  % remove member from set:

  op [a] - (s: Set a, x:a) infixl 25 : Set a = s -- single x
  proof Isa -> less [simp] end-proof

  % map (partial) function over set:

  op [a,b] map (f: a -> b) (s: Set a) : Set b =
    fn y:b -> (ex(x:a) x in? s && y = f x)

  op [a,b] mapPartial (f: a -> Option b) (s: Set a) : Set b =
    fn y:b -> (ex(x:a) x in? s && Some y = f x)

  % inversely map function over set:

  op [a,b] imap (f: a -> b) (s: Set b) : Set a = fn x:a -> f x in? s

  (* A function f from a to b generates a Set b, namely the set of all
  y:b such that y = f x for some x:a. *)

  op [a,b] setGeneratedBy (f: a -> b) : Set b = map f full

  % finite sets:

  op [a] finite? (s: Set a) : Bool =
    % this disjunct ensures that the definition is correct in case a is empty;
    % if a is empty, Nat -> a is empty and the disjunct below (ex ...) is false,
    % but of course the empty set over empty a is finite (note that there is
    % only one set over empty a, namely the empty set; so, if s is not empty, a
    % is not empty and Nat -> a is not empty):
    empty? s ||
    % there is a surjective function from {i:Nat | i < n} to {x:a | x in? s}
    % (which are "pseudo-types" because of the free variables `n' and `s'):
    (ex (f: Nat -> a, n:Nat)
      (fa(x:a) x in? s <=> (ex(i:Nat) i < n && f i = x)))
  proof Isa
  apply(simp)
  apply(rule iffI)

    apply(induct rule:finite_induct)
     apply(simp)
     apply(simp add: insert_not_empty)
     apply(auto)
      apply(rule_tac x="\_lambday::nat. x::'a" in exI)
      apply(rule_tac x="1" in exI)
      apply(simp add: eq_ac)
      apply(rule_tac x="\_lambdai::nat. if i = n then x::'a else f i" in exI)
      apply(rule_tac x="n + 1" in exI)
      apply(intro allI iffI impI)
      apply(elim disjE)
      apply(rule_tac x="n" in exI, simp)
(* List.ex_nat_less_eq: (\_existsm<?n. ?P m) = (\_existsm\_in{0..<?n}. ?P m) *)
      apply(simp add: ex_nat_less_eq)
      apply(erule bexE) (* \_lbrakk\_existsx\_in?A. ?P x; \_Andx. \_lbrakkx \_in ?A; ?P x\_rbrakk \_Longrightarrow ?Q\_rbrakk \_Longrightarrow ?Q *)
      apply(rule_tac x="i" in bexI)
      apply(simp)
      apply(simp)
      apply(simp add: ex_nat_less_eq)
      apply(erule bexE)
      apply(split split_if_asm)
      apply(simp)
      apply(rule disjI2)
      apply(rule_tac x="i" in bexI, assumption)
      apply(clarsimp)

(* finite_conv_nat_seg_image: "finite A = (\_exists (n::nat) f. A = f ` {i::nat. i<n})" *)

      apply(simp only: finite_conv_nat_seg_image)
      apply(rule_tac x="n" in exI)
      apply(rule_tac x="f" in exI)
      apply(auto)

  end-proof

  type FiniteSet a = (Set a | finite?)

  theorem finite_insert is [a]
    fa (s: FiniteSet a, x: a)
      finite? (s <| x)
  proof Isa Set__finite_insert__stp
  apply(case_tac "x \_in s")
  apply(simp only: insert_absorb Set_P_RSet)
 
  apply(simp add: Set__finite_p__stp_def Set__empty_p__stp_def)
  apply(rule disjI2)
  apply(erule disjE)

   apply(clarsimp)
   apply(rule_tac x="\_lambdai. x" in exI, simp)
   apply(rule_tac x="1" in exI, simp add: eq_ac)

   apply(erule exE)
   apply(elim conjE)
   apply(erule exE, simp)
   apply(rule_tac x="\_lambdai. if i = n then x else f i" in exI, simp)
   apply(rule_tac x="Suc n" in exI)
   apply(intro allI impI)
   apply(case_tac "xa=x", auto)
    apply(rule_tac x="i" in exI, simp)+
  end-proof

  theorem induction is [a]
    fa (p: FiniteSet a -> Bool)
      p empty &&
      (fa (s: FiniteSet a, x:a) p s => p (s <| x)) =>
      (fa (s: FiniteSet a) p s)

proof Isa Set__induction__stp
proof -
 txt {* We define a local predicate @{term "atMostOfSize s n"} saying when a set
 @{term s} has at most size @{term n}: all the elements of @{term s} are covered
 by a function @{term f} from the natural numbers @{text "0\<dots>n-1"}. *}
 def atMostOfSize \<equiv>
     "\<lambda> (s::'a set) (n::nat).
        \<exists> (f:: nat \<Rightarrow> 'a).
          \<forall>x \<in> s. \<exists>i < n. x = f i"
 txt {* The truth of the local predicate just defined implies the finiteness of
 the set as captured by the predicate @{const Set__finite_p__stp}, provided that
 all the elements of the set satisfy the (subtype) argument predicate of @{const
 Set__finite_p__stp}, of course. *}
 have FIN: "\<And> (s::'a set) n P.
            \<lbrakk> atMostOfSize s n ; Set_P P s \<rbrakk>
            \<Longrightarrow> Set__finite_p__stp P s"
 proof -
  fix s :: "'a set"
  fix n :: nat
  fix P :: "'a \<Rightarrow> bool"
  assume "atMostOfSize s n"
  assume "Set_P P s"
  show "Set__finite_p__stp P s"
  proof (unfold Set__finite_p__stp_def)
   show "Set__empty_p__stp P s \<or>
         (\<exists> (f :: nat \<Rightarrow> 'a) n.
           Fun_PR P f \<and>
             (\<forall>x. P x \<longrightarrow>
                  (x \<in> s) = (\<exists>i<n. f i = x)))"
   proof cases
    txt {* If @{term s} is empty, we are done because the first disjunct that
    defines @{const Set__finite_p__stp} is true. *}
    assume "Set__empty_p__stp P s"
    thus ?thesis by auto
   next
    txt {* Otherwise, since @{term s} is not empty, we find the function @{term
    f} that fulfills @{const Set__finite_p__stp} from a function @{term g} that
    fulfills @{term atMostOfSize}. *}
    assume "\<not> Set__empty_p__stp P s"
    txt {* We first single out an element @{term y} of @{term s}, which
    satisfies @{term P} because all the elements of @{term s} satisfy @{term P}
    by hypothesis. *}
    hence "s \<noteq> {}" by (auto simp add: Set__empty_p__stp_def)
    then obtain y where "y \<in> s" by auto
    with `Set_P P s` have "P y" by (auto simp add: Set_P_def)
    txt {* From the assumption that @{term s} has at most size @{term n}, we
    find a function @{term g} covering @{term s} from the natural numbers @{text
    "0\<dots>n-1"}, which fulfills @{term atMostOfSize}. *}
    from `atMostOfSize s n` obtain g
    where "\<forall>x \<in> s. \<exists>i < n. x = g i"
     by (auto simp add: atMostOfSize_def)
    txt {* According to the definition of @{term atMostOfSize}, each element of
    @{term s} is the image of some @{term "i < n"} under @{term g}, but there
    could be some @{term "i < n"} that @{term g} maps to something outside
    @{term s}. In contrast, the function @{term f} needed to fulfill @{const
    Set__finite_p__stp} must map every @{term "i < n"} to some element of
    @{term s}. This is easily achieved by remapping any @{term "i < n"} mapped
    by @{term g} outside @{term s}, to the element @{term y} that we singled
    out earlier. *}
    def f \<equiv> "\<lambda>i. if (g i \<notin> RSet P s) then y else g i"
    txt {* Now we prove that @{term f} and @{term n} fulfill (the second
    disjunct of) @{const Set__finite_p__stp}. *}
    have "Fun_PR P f \<and>
          (\<forall>x. P x \<longrightarrow>
               (x \<in> s) = (\<exists>i<n. f i = x))"
    proof
     from f_def `P y` show "Fun_PR P f" by auto
    next
     show "\<forall>x. P x \<longrightarrow>
              (x \<in> s) = (\<exists>i<n. f i = x)"
     proof (rule allI, rule impI)
      fix x
      assume "P x"
      show "(x \<in> s) = (\<exists>i<n. f i = x)"
      proof
       assume "x \<in> s"
       with `\<forall>x \<in> s. \<exists>i < n. x = g i`
       obtain i where "i < n" and "g i = x" by auto
       with `P x` `x \<in> s` f_def show "\<exists>i<n. f i = x" by auto
      next
       assume "\<exists>i<n. f i = x"
       then obtain i where "i < n" and "f i = x" by auto
       show "x \<in> s"
       proof cases
        assume "g i \<notin> RSet P s"
        with f_def `f i = x` `y \<in> s` show ?thesis by auto
       next
        assume "\<not> g i \<notin> RSet P s"
        with f_def `f i = x` show ?thesis by auto
       qed
      qed
     qed
    qed
    hence "\<exists> (f :: nat \<Rightarrow> 'a) n.
            Fun_PR P f \<and>
              (\<forall>x. P x \<longrightarrow>
                 (x \<in> s) = (\<exists>i<n. f i = x))"
     by auto
    thus ?thesis by (rule disjI2)
   qed
  qed
 qed
 txt {* Thus we have proved @{text FIN}. *}
 txt {* Conversely, if a set @{term s} is finite as defined by @{const
 Set__finite_p__stp}, and all its elements satisfy the subtype predicate @{term
 P}, the set has size at most @{term n} for some @{term n}. *}
 have FIN': "\<And> (s::'a set) P.
             \<lbrakk> Set__finite_p__stp P s ; Set_P P s \<rbrakk>
             \<Longrightarrow> \<exists>n. atMostOfSize s n"
 proof -
  fix s :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  assume "Set_P P s"
  assume "Set__finite_p__stp P s"
  txt {* We first unfold @{const Set__finite_p__stp}, obtaining a
  disjunction. *}
  hence "Set__empty_p__stp P s \<or>
         (\<exists> f (n::nat). Fun_PR P f \<and>
                        (\<forall>x. P x \<longrightarrow>
                                (x \<in> s) = (\<exists>i < n. f i = x)))"
   by (unfold Set__finite_p__stp_def)
  txt {* Then we prove the conclusion under each disjunct. *}
  thus "\<exists>n. atMostOfSize s n"
  proof (rule disjE)
   txt {* If @{term s} is empty, it has size at most 0. *}
   assume "Set__empty_p__stp P s"
   hence "s = {}" by (auto simp add: Set__empty_p__stp_def)
   have "atMostOfSize s 0"
   proof (auto simp add: atMostOfSize_def)
    fix x
    assume "x \<in> s"
    with `s = {}` show False by auto
   qed
   thus ?thesis by auto
  next
   txt {* If there is a function @{term f} and a natural number @{term n}
   fulfilling the second disjunct of the definition of @{const
   Set__finite_p__stp}, the set @{term s} has size at most @{term n} and
   this is witnessed by @{term f} itself. *}
   assume "\<exists> f (n::nat). Fun_PR P f \<and>
                         (\<forall>x. P x \<longrightarrow>
                               (x \<in> s) = (\<exists>i < n. f i = x))"
   then obtain f n
   where "Fun_PR P (f :: nat \<Rightarrow> 'a)" and
         "\<forall>x. P x \<longrightarrow>
             (x \<in> s) = (\<exists>i < n. f i = x)" by auto
   have "atMostOfSize s n"
   proof (auto simp add: atMostOfSize_def, rule exI, auto)
    fix x::'a
    assume "x \<in> s"
    with `Set_P P s` have "P x" by (auto simp add: Set_P_def)
    with `\<forall>x. P x \<longrightarrow>
            (x \<in> s) = (\<exists>i < n. f i = x)`
         `x \<in> s`
    show "\<exists>i < n. x = f i" by auto
   qed
   thus ?thesis by auto
  qed
 qed
 txt {* We define a local predicate @{term "q n"} saying when @{term p} (the
 predicate mentioned in the induction theorem) holds on all the sets of size at
 most @{term n} whose elements all satisfy @{term P__a} (the subtype
 predicate). *}
 def q \<equiv> "\<lambda> (n::nat).
                 \<forall>s. atMostOfSize s n \<and>
                             Set_P P__a s \<longrightarrow> p s"
 txt {* We state all the assumptions of the theorem. *}
 assume "Fun_PD
          (\<lambda> (x__l::'a set).
            Set__finite_p__stp P__a x__l \<and>
            Set_P P__a x__l)
          (p::'a set \<Rightarrow> bool)"
 assume "Set__finite_p__stp P__a s"
 assume "Set_P P__a s"
 assume "p {}"
 assume "\<forall> (s::'a set) (x::'a).
          (Set__finite_p__stp P__a s \<and> Set_P P__a s)
          \<and> P__a x 
          \<longrightarrow> (p s \<longrightarrow> p (insert x s))"
 txt {* We prove that @{term p} holds on all finite sets by proving that @{term
 q} holds on all natural numbers, by induction on the natural numbers. *}
 have "\<And>n. q n"
 proof -
  fix n
  show "q n"
  proof (induct n)
   txt {* The base case is proved by noticing that only the empty set has at
   most size 0, and the truth of @{term p} on the empty set is among the
   assumptions of the theorem. *}
   case 0
   show "q 0"
   proof (auto simp add: q_def)
    fix s
    assume "atMostOfSize s 0"
    have "s = {}"
    proof (rule ccontr)
     assume "s \<noteq> {}"
     then obtain x where "x \<in> s" by auto
     with `atMostOfSize s 0` have "\<exists>i < (0::nat). x = f i"
      by (auto simp add: atMostOfSize_def)
     thus False by auto
    qed
    with `p {}` show "p s" by auto
   qed
  next
   txt {* For the induction step, we first unfold @{term q} to get a useful
   induction hypothesis. *}
   case (Suc n)
   hence IH: "\<And>s. \<lbrakk> atMostOfSize s n ; Set_P P__a s \<rbrakk>
                       \<Longrightarrow> p s"
    by (auto simp add: q_def)
   txt {* We first unfold @{term q}. *}
   show "q (Suc n)"
   proof (auto simp add: q_def)
    txt {* We consider a set @{term s} of size at most @{term "Suc n"} whose
    elements all satisfy @{term P__a}. *}
    fix s
    assume "Set_P P__a s"
    assume "atMostOfSize s (Suc n)"
    txt {* We find a function @{term f} that fulfills @{term atMostOfSize}. *}
    then obtain f where "\<forall>x \<in> s. \<exists>i < Suc n. x = f i"
     by (auto simp add: atMostOfSize_def)
    txt {* We show the conclusion by distinguishing two cases. *}
    show "p s"
    proof cases
     txt {* If @{term s} also has size at most @{term n}, the conclusion
     immediately follows by inductive hypothesis. *}
     assume "atMostOfSize s n"
     with `Set_P P__a s` IH show ?thesis by auto
    next
     txt {* If @{term s} does not also have size at most @{term n}, there must
     be some @{term x} in @{term s} that is not the image of any @{term "i < n"}
     under @{term f}.*}
     assume "\<not> atMostOfSize s n"
     then obtain x where "x \<in> s" and "\<forall>i < n. x \<noteq> f i"
       by (auto simp add: atMostOfSize_def)
     txt {* But because @{term s} has size at most @{term "Suc n"}, that @{term
     x} must be the image of @{term n} under @{term f}. *}
     with `\<forall>x \<in> s. \<exists>i < Suc n. x = f i`
     obtain i where "i < Suc n" and "x = f i" by auto
     have "i = n"
     proof (rule ccontr)
      assume "i \<noteq> n"
      with `i < Suc n` have "i < n" by auto
      with `\<forall>i < n. x \<noteq> f i` have "x \<noteq> f i" by auto
      with `x = f i` show False by auto
     qed
     with `x = f i` have "x = f n" by auto
     txt {* Moreover, every other element @{term y} of @{term s} must be in the
     image of some @{term "i < n"} under @{term f}. *}
     have "\<forall>y \<in> s. y \<noteq> x \<longrightarrow>
                               (\<exists>i<n. f i = y)"
     proof auto
      fix y
      assume "y \<in> s"
      assume "y \<noteq> x"
      from `y \<in> s` `\<forall>y \<in> s. \<exists>i < Suc n. y = f i`
      obtain i where "i < Suc n" and "y = f i" by auto
      have "i < n"
      proof (rule ccontr)
       assume "\<not> i < n"
       with `i < Suc n` have "i = n" by auto
       with `x = f n` `y \<noteq> x` `y = f i` show False by auto
      qed
      with `y = f i` show "\<exists>i<n. f i = y" by auto
     qed
     txt {* Now consider the set @{term s0} obtained by removing @{term x} from
     @{term s}. *}
     def s0 \<equiv> "s - {x}"
     txt {* This set must have size at most @{term n}, as witnessed by the same
     function @{term f} that witnesses @{term s} having size at most @{term "Suc
     n"}. *}
     with `\<forall>y \<in> s.
             y \<noteq> x \<longrightarrow> (\<exists>i<n. f i = y)`
     have "\<forall>y \<in> s0. \<exists>i<n. y = f i" by auto
     hence "atMostOfSize s0 n" by (auto simp add: atMostOfSize_def)
     txt {* Since all the elements of @{term s} satisfy @{term P} by hypothesis,
     so do all the elements of @{term s0}. *}
     from `Set_P P__a s` s0_def have "Set_P P__a s0"
      by (auto simp add: Set_P_def)
     with `atMostOfSize s0 n` `q n` q_def have "p s0" by auto
     txt {* We now use the property @{text FIN} proved earlier, to prove that
     @{term s0} is finite. *}
     from `atMostOfSize s0 n` `Set_P P__a s0` FIN
     have "Set__finite_p__stp P__a s0" by auto
     txt {* From the hypothesis that all the elements of @{term s} satisfy
     @{term P__a}, in particular the element @{term x} that we removed from
     @{term s} to obtain @{term s0} satisfies @{term P__a}. *}
     from `Set_P P__a s` `x \<in> s` have "P__a x" by (auto simp add: Set_P_def)
     txt {* We can finally instantiate the induction step of the theorem that we
     are trying to prove (which is one of the assumptions of the theorem) to
     @{term s0} and @{term x}. *}
     with `\<forall> (s::'a set) (x::'a).
             (Set__finite_p__stp P__a s \<and> Set_P P__a s)
             \<and> P__a x  
             \<longrightarrow> (p s \<longrightarrow> p (insert x s))`
          `Set__finite_p__stp P__a s0`
          `Set_P P__a s0`
          `p s0`
     have "p (insert x s0)" by auto
     with s0_def have "insert x s0 = s" by auto
     with `p (insert x s0)` show "p s" by auto
    qed
   qed
  qed
 qed
 txt {* Recall that in order to prove the theorem we have to show @{term "p s"}
 (for arbitrary @{term s}) under the assumptions on @{term s} that we have
 already stated. The fact, just proved, that @{term "q n"} holds for arbitrary
 @{term n} is used as follows: the finiteness of @{term s} implies the existence
 of some @{term n} such that @{term s} has size at most @{term n}, and therefore
 we can conclude @{term "p s"} from @{term "q n"}. *}
 from `Set_P P__a s` `Set__finite_p__stp P__a s` FIN'
 obtain n where "atMostOfSize s n" by auto
 with `q n` `Set_P P__a s` show "p s" by (auto simp add: q_def)
qed
end-proof

  op size : [a] FiniteSet a -> Nat = the(size)
    (size empty = 0) &&
    (fa (s: FiniteSet a, x:a) size (s <| x) = 1 + size (s - x))

  proof Isa Set__size__stp_Obligation_the
  apply(rule_tac a="RFun (Fun_PD P__a) card" in ex1I)
  apply(simp)
  apply(intro conjI allI impI)
  end-proof

  op [a] hasSize (s: Set a, n:Nat) infixl 20 : Bool =
    finite? s && size s = n

  (* In order to fold over a finite set, we need the folding function to be
  insensitive to order (a kind of commutativity property). It is not necessary
  that it is also insensitive to repetitions (a kind of idempotence property),
  because we can remove elements from the set as we fold. It is also not
  necessary that the function is commutative on its whole domain: it is
  sufficient that it is commutative on the elements of the set that we are
  folding over. *)

  op [a,b] foldable? (c:b, f: b * a -> b, s: FiniteSet a) : Bool =
    %% Definition of foldable? doesn't depend on initial value c, but it's
    %% convenient to have foldable? apply to entire sequence of args to fold.
    (fa (x:a, y:a, z:b) x in? s && y in? s => f(f(z,x),y) = f(f(z,y),x))
  proof Isa [simp] end-proof

  op fold : [a,b] ((b * (b * a -> b) * FiniteSet a) | foldable?) -> b =
    the(fold)
      (fa (c: b, f: b * a -> b) fold (c, f, empty) = c) &&
      (fa (c: b, f: b * a -> b, s: FiniteSet a, x: a)
         foldable? (c, f, s <| x) =>
           fold (c, f, s <| x) = f (fold (c, f, s - x), x))

  % finite powerset:

  op [a] powerf (s: Set a) : Set (FiniteSet a) = power s /\ finite?

  % infinite, countable, and uncountable cardinality:

  op infinite? : [a] Set a -> Bool = ~~ finite?

  type InfiniteSet a = (Set a | infinite?)

  op [a] countable? (s: Set a) : Bool =
    infinite? s &&
    % there is a surjective function from Nat to {x:a | x in? s}
    % (the latter is a "pseudo-type" because of the free variable `s'):
    (ex (f : Nat -> a)
       (fa(x:a) x in? s => (ex(i:Nat) f i = x)))

  type CountableSet a = (Set a | countable?)

  op uncountable? : [a] Set a -> Bool = infinite? /\  ~~ countable?

  type UncountableSet a = (Set a | uncountable?)

  % minimum/maximum set:

  op [a] isMinIn (s: Set a, ss: Set (Set a)) infixl 20 : Bool =
    s in? ss && (fa(s1) s1 in? ss => s <= s1)

  op [a] hasMin? (ss: Set (Set a)) : Bool = (ex(s) s isMinIn ss)

  type SetOfSetsWithMin a = (Set (Set a) | hasMin?)

  op [a] min (ss: SetOfSetsWithMin a) : Set a = the(s) s isMinIn ss

  proof Isa  Set__min_Obligation_the
    apply(auto simp add: Set__hasMin_p_def Set__isMinIn_def)
  end-proof

  op [a] isMaxIn (s: Set a, ss: Set (Set a)) infixl 20 : Bool =
    s in? ss && (fa(s1) s1 in? ss => s >= s1)

  op [a] hasMax? (ss: Set (Set a)) : Bool = (ex(s) s isMaxIn ss)

  type SetOfSetsWithMax a = (Set (Set a) | hasMax?)

  op [a] max (ss: SetOfSetsWithMax a) : Set a = the(s) s isMaxIn ss

  proof Isa  Set__max_Obligation_the
    apply(auto simp add: Set__hasMax_p_def Set__isMaxIn_def)
  end-proof

  % mapping to Isabelle:

  proof Isa Thy_Morphism Set
    type Set.Set -> set (id,id)
    Set.collect -> Collect
    Set.Set_P -> Set_P
    Set.in? -> \<in> Left 20
    Set.nin? -> \<notin> Left 20
    Set.<= -> \<subseteq> Left 20
    Set.< -> \<subset> Left 20
    Set.>= -> \<subseteq> Left 20 reversed
    Set.> -> \<subset> Left 20 reversed
    Set.<| -> insert curried reversed
    Set.~~ -> -
    Set./\ -> \<inter> Left 25
    Set.//\\ -> \<Inter>
    Set.\/ -> \<union> Left 24 
    Set.\\// -> \<Union>
    Set.-- -> - Left 25
    Set.* -> <*> Left 27
    Set.power -> Pow
    Set.empty -> {}
    Set.full  -> UNIV
    Set.finite? -> finite
  end-proof

endspec
