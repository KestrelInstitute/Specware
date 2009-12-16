Set qualifying spec

(* In higher-order logic, it is customary to define a set as a predicate: the
predicate is true exactly for (i.e. for all and only) the elements of the set.

In this spec we follow that customary approach, which is very clear and
simple. All the types and ops in this spec are defined, i.e. this spec is a
definitional extension; therefore, it is readily seen to be consistent.

The fact that type `Set' is defined means that sets as specified here cannot be
later refined into a representation different from predicates. This should not
be a problem because sets may be infinite and therefore cannot be refined to be
executable (because equality is undecidable). Sets as defined here are useful
for specification purposes, not for execution. Finite sets as defined in spec
`FiniteSet' can instead be refined to be executable. *)

type Predicate a = a -> Bool

type Set a = Predicate a

%%% Generate stp versions of finite_insert and induction in case they are useful later
proof Isa -stp-theorems end-proof

(*** Lemmas About Set_P RSet and Fun_PD ***)
proof Isa -verbatim
lemma Set_Set_P_converse:
"Set_P P A \_Longrightarrow (\_forall x \_in A . P x)"
by (auto simp add: Set_P_def mem_def)
lemma Set_Fun_PD_Set_P:
"Fun_PD P A \_Longrightarrow Set_P P A"
by (auto simp add: Set_P_def mem_def)
lemma Set_Set_P_Fun_PD:
"Set_P P A \_Longrightarrow Fun_PD P A"
by (auto simp add: Set_P_def mem_def)
lemma Set_Set_P_RSet:
"Set_P P A \_Longrightarrow (RSet P A = A)"
by (auto simp add: Set_P_def mem_def)
end-proof

% membership:

op [a] in? (x:a, s:Set a) infixl 20 : Bool = s x

op [a] nin? (x:a, s:Set a) infixl 20 : Bool = ~(x in? s)

% Lifting a predicate from elements to regularized sets
op [a] Set_P (Pa: a -> Bool) (s:Set a): Bool =
  fa(x: a) ~(Pa x) => x nin? s     % contrapositive: x in? s => Pa x
proof Isa
  by (simp add: Set_P_def)
end-proof

% (strict) sub/superset:

op [a] <= (s1:Set a, s2:Set a) infixl 20 : Bool =
  fa(x) x in? s1 => x in? s2

op [a] < (s1:Set a, s2:Set a) infixl 20 : Bool = (s1 <= s2 && s1 ~= s2)

op [a] >= (s1:Set a, s2:Set a) infixl 20 : Bool = (s2 <= s1)

op [a] > (s1:Set a, s2:Set a) infixl 20 : Bool = (s2 < s1)

proof Isa -verbatim
lemma Set_Set_P_subsets_equiv:
"Set_P P__a A \_Longrightarrow 
 (Set__e_lt_eq__stp P__a ((A::'a set),(B::'a set)) = (A \_subseteq B))" 
by (auto simp add: Set__e_lt_eq__stp_def 
                   Set__e_lt_eq__def Set_P_def )
end-proof

% complement, intersection, and union (lift `~', `&&', and `||' to sets):

op [a] ~~ (s:Set a) : Set a = fn x:a -> x nin? s

op [a] /\ (s1:Set a, s2:Set a) infixr 25 : Set a =
  fn x:a -> x in? s1 && x in? s2

op [a] \/ (s1:Set a, s2:Set a) infixr 24 : Set a =
  fn x:a -> x in? s1 || x in? s2

% intersection/union of all sets in a set:

op [a] //\\ (ss:Set (Set a)) : Set a =
  fn x:a -> (fa(s) s in? ss => x in? s)

op [a] \\// (ss:Set (Set a)) : Set a =
  fn x:a -> (ex(s) s in? ss && x in? s)

% difference:

op [a] -- (s1:Set a, s2:Set a) infixl 25 : Set a =
  fn x:a -> x in? s1 && x nin? s2

% cartesian product:

op [a,b] * (s1:Set a, s2:Set b) infixl 27 : Set (a * b) =
  fn (x:a,y:b) -> x in? s1 && y in? s2

% powerset:

op [a] power (s:Set a) : Set (Set a) =
  fn sub:Set a -> sub <= s

% set with no elements (lift `false' to sets):

op empty : [a] Set a = fn _ -> false
proof Isa
  by (auto simp add: mem_def)
end-proof

op [a] empty? (s:Set a) : Bool = (s = empty)
proof Isa [simp] end-proof
proof Isa empty_p__stp [simp] end-proof

proof Isa -verbatim
lemma Set_empty_apply[simp]:
"{} x = False"
by(simp add:Set__empty__def)
lemma Set_RSet_empty[simp]:
"RSet P_a {} = {}"
by auto
lemma Set_Set_P_empty[simp]:
"Set_P P {} = True"
by (simp add:Set_P_def)
lemma Set_Fun_PD_empty[simp]:
"Fun_PD P {} = True"
by auto
lemma Set_empty_p_equiv_empty_p_stp:
"Set__empty_p s = Set__empty_p__stp P__a s"
by (auto simp add:Set__empty_p__stp_def Set__empty_p_def 
                  Set__empty__def mem_def)
end-proof

% sets with at least 1 element:

op [a] nonEmpty? (s:Set a) : Bool = (s ~= empty)

type Set1 a = (Set a | nonEmpty?)

proof Isa -verbatim
lemma Set__nonEmpty_p_stp_equ_nonEmpty_p_stp:
"Set__nonEmpty_p__stp P__a s = Set__nonEmpty_p s"
by (auto simp add:Set__nonEmpty_p__stp_def 
                  Set__nonEmpty_p_def mem_def)
lemma Set__nonEmpty_p_stp_EX_x_t:
"\_lbrakk Set_P P__a s; Set__nonEmpty_p__stp P__a (s::'a set)\_rbrakk \_Longrightarrow
 (\_exists (x::'a) (t::'a set) .
  P__a x \_and x \_notin t \_and (s = insert x t))"
proof(cases "s = {}")
 assume "Set_P P__a s" "Set__nonEmpty_p__stp P__a s" "s = {}"
 from this show ?thesis by(auto simp:Set__nonEmpty_p__stp_def mem_def)
next
 assume "Set_P P__a s" "Set__nonEmpty_p__stp P__a s" "s \_noteq {}"
 from `s \_noteq {}` have "\_exists x. x \_in s" by(auto)
 from this obtain x::'a and t::"'a set" 
 where "x \_in s" and "t = (s - {x})" by auto
 from this have "s =(insert x t)" by auto
 from this `Set_P P__a s` have "P__a x" by (auto simp:Set_P_def)
 from  `t = (s - {x})` have "x \_notin t" by auto
 from `P__a x` `x \_notin t` `s =(insert x t)` 
 show ?thesis by auto
qed
end-proof

% set with all elements (lift `true' to sets):

op full : [a] Set a = fn _ -> true
proof Isa
  by (auto simp add: mem_def)
end-proof

op [a] full? (s:Set a) : Bool = (s = full)
proof Isa [simp] end-proof

proof Isa -verbatim
lemma Set__full_apply[simp]:
"UNIV x = True"
by (auto simp add:Set__full__def)
lemma Set__full_stp_apply:
"\_lbrakkP__a x; Set__full_p__stp P__a s\_rbrakk \_Longrightarrow x \_in s"  
by (auto simp add:Set__full_p__stp_def)
end-proof

% sets with exactly one element:

op [a] single(*ton*) (x:a) :Set a = fn y:a -> y = x

op [a] single? (s:Set a) : Bool = (ex(x:a) s = single x)
proof Isa [simp] end-proof

op [a] onlyMemberOf (x:a, s:Set a) infixl 20 : Bool =
  single? s && x in? s
proof Isa [simp] end-proof

proof Isa -verbatim
lemma Set_single_simp [simp]:
"Set__single x = {x}"
 by (rule set_ext, simp, simp add: mem_def Set__single_def)
lemma Set_single_simp_app1:
"{x} x = True"
by(simp del:Set_single_simp 
        add:Set_single_simp[symmetric] Set__single_def)
lemma Set_single_simp_app2:
"{x} y = (x = y)"
by(simp del:Set_single_simp 
        add:Set_single_simp[symmetric] Set__single_def eq_ac)
lemma Set_Pa_Set_P_single:
"P__a (x::'a) \_Longrightarrow Set_P P__a (Set__single x)"
by(auto simp:Set_P_def)
lemma Set_Pa_RSet_single[simp]:
"P__a (x::'a)\_Longrightarrow RSet P__a (Set__single x) = Set__single x"
by(auto simp:Set_P_def)
lemma Set_single_single_stp:
"\_lbrakk P__a x; x \_in s; Set__single_p s\_rbrakk \_Longrightarrow Set__single_p__stp P__a s"
by (auto simp:Set__single_p__stp_def Set__single_p_def)
lemma Set_single_stp_single:
"\_lbrakkx \_in s; Set__single_p__stp P__a s\_rbrakk \_Longrightarrow Set__single_p s"
by (auto simp:Set__single_p__stp_def Set__single_p_def)
end-proof

type Singleton a = (Set a | single?)

op [a] theMember (s:Singleton a) : a = the(x:a) x in? s

% add member to set (triangle points towards set):

op [a] <| (s:Set a, x:a) infixl 25 : Set a = s \/ single x

proof Isa -verbatim
lemma Set__RSet_insert_simp[simp]:  
"\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk  
 \_Longrightarrow  (RSet P__a (insert x s) = (insert x s))"
by (auto simp add:Set_P_def)
lemma Set__Set_P_insert:
"\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk
 \_Longrightarrow Set_P P__a (insert x s)"
by (auto simp add:Set_P_def)
lemma Set__Fun_PD_insert:
"\_lbrakk Fun_PD P__a s; P__a (x::'a)\_rbrakk
 \_Longrightarrow Fun_PD P__a (insert x s)"
proof(rule Set_Set_P_Fun_PD)
 assume "Fun_PD P__a (s::'a set)"
        "P__a x" 
 thus "Set_P P__a (insert x s)"
by (simp add:Set_Fun_PD_Set_P Set__Set_P_insert)
qed
lemma Set_P_Set_P_insert2: 
"Set_P P__a (insert x s) \_Longrightarrow Set_P P__a s"
by (auto simp: Set_P_def)
lemma Set_P_insert_Pa_x:
"Set_P P__a (insert x s) \_Longrightarrow P__a x"
by (auto simp: Set_P_def)
end-proof

% remove member from set:

op [a] - (s:Set a, x:a) infixl 25 : Set a = s -- single x
proof Isa -> less [simp] end-proof

proof Isa -verbatim
lemma Set__RSet_less_simp[simp]:  
"\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk  
 \_Longrightarrow  (RSet P__a (s less x)) = (s less x)"
by (auto simp add:Set_P_def)
lemma Set__SetP_less:
"Set_P P__a s \_Longrightarrow Set_P P__a (s less x)"
by(auto simp add:Set_P_def)
lemma Set_P_Set_P_Less2: 
"\_lbrakk Set_P P__a (s less x); P__a (x::'a)\_rbrakk \_Longrightarrow 
 Set_P P__a s"
by (auto simp: Set_P_def) 
lemma Set_Fun_PD_less:
"\_lbrakk Fun_PD P__a s; P__a (x::'a)\_rbrakk
 \_Longrightarrow Fun_PD P__a (s less x)"
proof(rule Set_Set_P_Fun_PD)
 assume "Fun_PD P__a (s::'a set)"
        "P__a x"
 from this have "Set_P P__a s" by(simp add: Set_Fun_PD_Set_P) 
 from this show "Set_P P__a (s less x)"
 by (rule_tac s=s and P__a=P__a in Set__SetP_less)
qed
end-proof

% map (partial) function over set:

op [a,b] map (f: a -> b) (s:Set a) : Set b =
  fn y:b -> (ex(x:a) x in? s && y = f x)

op [a,b] mapPartial (f: a -> Option b) (s:Set a) : Set b =
  fn y:b -> (ex(x:a) x in? s && Some y = f x)

% inversely map function over set:

op [a,b] imap (f: a -> b) (s:Set b) : Set a = fn x:a -> f x in? s

(* A function f from a to b generates a Set b, namely the set of all
y:b such that y = f x for some x:a. *)

op [a,b] setGeneratedBy (f: a -> b) : Set b = map f full

% *** Isabelle finite set lemmas ***

proof Isa -verbatim
lemma finite_nat_seg:
"finite (s::'a set) \_Longrightarrow (\_exists(f::nat \_Rightarrow 'a) (n::nat). 
        \_forall(x::'a). (x \_in s) = (\_exists(i::nat). i < n \_and f i = x))"
by(auto simp add: finite_conv_nat_seg_image)
lemma nat_seq_finite:
"(\_exists(f::nat \_Rightarrow 'a) (n::nat). 
  \_forall(x::'a). (x \_in (s::'a set)) = (\_exists(i::nat). i < n \_and f i = x)) 
 \_Longrightarrow finite s"
by(elim exE, rule nat_seg_image_imp_finite, auto)
end-proof

% finite sets:

op [a] finite? (s:Set a) : Bool =
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
proof
 assume "finite (s::'a set)"
 thus "Set__empty_p s \_or 
       (\_exists(f::nat \_Rightarrow 'a) n::nat. \_forall x::'a. (x \_in s) = (\_exists i<n. f i = x))"
 by(auto simp:finite_nat_seg)
next
 assume "Set__empty_p s \_or 
      (\_exists(f::nat \_Rightarrow 'a) n::nat. \_forall x::'a. (x \_in s) = (\_exists i<n. f i = x))"
 thus "finite s"
 proof
  assume "Set__empty_p s" thus "finite s" 
  by(auto simp:Set__empty_p_def)
 next
  assume "\_exists(f::nat \_Rightarrow 'a) n::nat. \_forall x::'a. (x \_in s) = (\_exists i<n. f i = x)"
  thus ?thesis by(rule nat_seq_finite)
 qed
qed
end-proof

% **** Lemmas for subtyped predicate + finite 

proof Isa -verbatim
lemma finite_stp_nat_seg:
"Set__finite_p__stp (P__a::'a\_Rightarrow bool) (s::'a set) \_Longrightarrow
 (\_exists(f::nat \_Rightarrow 'a) (n::nat). 
        (\_forall(x::'a). P__a x  \_longrightarrow (x \_in s) = (\_exists(i::nat). i < n \_and f i = x)))"
proof (simp only:Set__finite_p__stp_def, erule disjE)
 fix s
 assume "Set__empty_p__stp P__a s"
 from this have "s = {}" by(simp add:Set__empty_p__stp_def)
 obtain f n where "(f::nat\_Rightarrow'a) = (\_lambda i. default_val)" 
              and "(n::nat)=(0::nat)" by auto
 from `s = {}` show "(\_exists(f::nat \_Rightarrow 'a) (n::nat). 
   (\_forall(x::'a). P__a x  \_longrightarrow (x \_in s) = (\_exists(i::nat). i < n \_and f i = x)))"
  by auto
next
 fix P__a s
 assume " \_exists(f::nat \_Rightarrow 'a) n::nat.
       Fun_PR P__a f \_and
       ( \_forall  x\_Colon'a.
           P__a x \_longrightarrow
           (x \_in s) =
           (\_exists i<n. f i = x))"
 thus "\_exists(f::nat \_Rightarrow 'a) n::nat.
        \_forall x\_Colon'a.
          P__a x \_longrightarrow
          (x \_in s) = (\_exists i<n. f i = x)" by auto
qed
(* lemma nat_seq_finite_stp:
"\_lbrakk Set_P P__a (s::'a set); 
   (\_exists(f::nat \_Rightarrow 'a) (n::nat). 
     \_forall(x::'a). (x \_in (s::'a set)) = (\_exists(i::nat). i < n \_and f i = x))\_rbrakk 
 \_Longrightarrow Set__finite_p__stp P__a s"
 sorry *)
end-proof

type FiniteSet a = (Set a | finite?)

(* Lemmas for proofs about finite sets *)
proof Isa -verbatim
lemma Set__finite_insert__stp_sans:
"\_lbrakk Set__finite_p__stp P__a (s::'a \_Rightarrow bool); Fun_PD P__a s; 
  P__a (x::'a)\_rbrakk \_Longrightarrow 
 Set__finite_p__stp P__a (insert x (s::'a set))"
proof -
assume ps:"Set__finite_p__stp P__a (s::'a set)"
           "Fun_PD P__a s"
           "P__a x"
thus "Set__finite_p__stp P__a (insert x s)"
 apply(simp add: Set__finite_p__stp_def)
 apply(erule disjE)
  apply(clarsimp)
  apply(rule_tac x="\_lambda i. x" in exI, simp)
  apply(rule_tac x="1" in exI, simp add: eq_ac)
 apply(elim exE conjE)
 apply(rule_tac x="\_lambda i. if i = n then x else f i" in exI, simp)
 apply(rule_tac x="Suc n" in exI)
  apply(intro allI impI)
  apply(case_tac "xa=x", auto)
 by(rule_tac x="i" in exI, simp)+
qed 
end-proof

theorem finite_insert is [a]
  fa (s: FiniteSet a, x: a)
    finite? (s <| x)
proof Isa finite_insert__stp
by (auto simp only: Set__finite_insert__stp_sans Set_Set_P_Fun_PD Set__RSet_insert_simp)
end-proof
proof Isa Set__finite_insert
by auto
end-proof

(* Additional Lemmas For Later Proofs *)
proof Isa -verbatim
lemma Set__finite_p_stp_imp_finite:
"\_lbrakk Set__finite_p__stp (P__a::'a\_Rightarrow bool) (s::'a set); Set_P P__a s\_rbrakk
 \_Longrightarrow finite s"
by(auto simp add:Set__finite_p__def Set__empty_p_def mem_def
           Set__finite_p__stp_def Set__empty_p__stp_def Set_P_def,
           blast)
lemma Set__finite_p_imp_finite_stp:
"\_lbrakk finite (s::'a set); Set_P (P__a::'a\_Rightarrow bool) s\_rbrakk \_Longrightarrow Set__finite_p__stp P__a s"
proof(induct s rule: finite.induct)
 show "Set__finite_p__stp P__a {}" 
 by(auto simp:Set__finite_p__stp_def Set__empty_p__stp_def mem_def) 
next
 fix A::"'a set" and a::"'a"
 assume "finite A" "Set_P P__a A \_Longrightarrow Set__finite_p__stp P__a A"
        "Set_P P__a (insert a A)"
 from `Set_P P__a (insert a A)`
 have "P__a a" by(rule Set_P_insert_Pa_x)
 from `Set_P P__a (insert a A)`
 have "Set_P P__a A" by (rule Set_P_Set_P_insert2)
 from `Set_P P__a A \_Longrightarrow Set__finite_p__stp P__a A` this 
 have "Set__finite_p__stp P__a A" by auto
 from `Set_P P__a A` have "Fun_PD P__a A" by (rule Set_Set_P_Fun_PD)
 from `Set__finite_p__stp P__a A` this `P__a a`
 have "Set__finite_p__stp P__a (RSet P__a (insert a A))" 
 by (simp only: Set__finite_insert__stp Set_Fun_PD_Set_P)
 from `Set_P P__a A` `P__a a` this 
 show "Set__finite_p__stp P__a (insert a A)" by (simp only: Set__RSet_insert_simp)
qed
lemma Set__finite_equiv_finite_stp:
"Set_P (P__a::'a\_Rightarrow bool) (s::'a set) \_Longrightarrow
 (Set__finite_p__stp P__a s = finite s)"
proof
 assume "Set_P (P__a::'a\_Rightarrow bool) (s::'a set)"
        "Set__finite_p__stp P__a s"
 thus "finite s" by(simp add: Set__finite_p_stp_imp_finite) 
next 
 assume "Set_P (P__a::'a\_Rightarrow bool) (s::'a set)"
        "finite s"
 thus "Set__finite_p__stp P__a s" by(simp add: Set__finite_p_imp_finite_stp) 
qed 
theorem Set__finite_less__stp_sans:
  "\_lbrakk Set__finite_p__stp P__a (s::'a \_Rightarrow bool); 
    Fun_PD P__a s; 
    P__a (x::'a)\_rbrakk \_Longrightarrow 
   Set__finite_p__stp P__a (s less x)"
proof (rule_tac s="s less x" in Set__finite_p_imp_finite_stp)
 assume "Set__finite_p__stp P__a (s::'a \_Rightarrow bool)" 
        "Fun_PD P__a s"
        "P__a (x::'a)"
 then have "finite s" by(auto simp: Set_Fun_PD_Set_P Set__finite_p_stp_imp_finite)
 thus "finite (s less x)" by(auto simp:less_def)
next
 assume "Fun_PD P__a s" 
 thus "Set_P P__a (SW_Set.less s x)" 
 by(simp only:Set_Fun_PD_Set_P Set__SetP_less)
qed
lemma Set__finite_less__stp:
  "\_lbrakk Set__finite_p__stp P__a (s::'a \_Rightarrow bool); 
    Fun_PD P__a s; 
    P__a (x::'a)\_rbrakk \_Longrightarrow 
   Set__finite_p__stp P__a (RSet P__a (s less x))"
by(simp only:Set_Fun_PD_Set_P Set__RSet_less_simp
                     Set__finite_less__stp_sans)
lemma finite_induct_stp[rule_format]:
"\_lbrakkfinite (S::'a set);
  (P::('a set) \_Rightarrow bool) {}; 
  \_forall(A::'a \_Rightarrow bool) a::'a. finite A \_and Set_P PA A \_and PA a \_and P A \_longrightarrow P (insert a A)\_rbrakk
 \_Longrightarrow  Set_P PA S \_longrightarrow P S"
  apply (erule finite.induct)
  apply (rule impI, assumption)
  apply (rule impI)
  apply (drule_tac x=A in spec)
  apply (drule_tac x=a in spec)
  apply (erule mp)
  apply (simp)
  apply (rule conjI)
  apply (rule Set_P_Set_P_insert2, simp)
  apply (rule conjI)
  apply (rule Set_P_insert_Pa_x, simp)
  apply (simp add:Set_P_Set_P_insert2)
done
end-proof


theorem induction is [a]
  fa (p: FiniteSet a -> Bool)
    p empty &&
    (fa (s: FiniteSet a, x:a) p s => p (s <| x)) =>
    (fa (s: FiniteSet a) p s)

proof Isa induction__stp_Obligation_subtype
  by (simp add: Set__finite_p__stp_def)
end-proof
proof Isa induction__stp_Obligation_subtype0
  by (rule Set__finite_insert__stp)
end-proof

proof Isa induction__stp
  proof -
 assume 
 "Fun_PD (Set__finite_p__stp (P__a::'a\_Rightarrowbool) &&& Set_P P__a) (p::'a set \_Rightarrow bool)"
 "Set__finite_p__stp P__a (s::'a set)"
 "Set_P P__a s" " p {}" and
 HI:" \_forall(s::'a \_Rightarrow bool) (x::'a). 
      Set__finite_p__stp P__a s 
        \_and (Set_P P__a s \_and (P__a x \_and p (s::'a set))) 
        \_longrightarrow p (insert x s)"
 thus "p s"
 proof(induct_tac s rule:finite_induct_stp)
  assume "Set__finite_p__stp P__a s" "Set_P P__a s"
  thus "finite s" 
  by(auto simp: Set_Fun_PD_Set_P Set__finite_p_stp_imp_finite)
 next
  assume "p {}" thus "p {}" .
 next
  fix A::"'a set" and a::"'a"
  from HI have "Set__finite_p__stp P__a A 
        \_and (Set_P P__a A \_and (P__a a \_and p A))  
        \_longrightarrow p (insert a A)" by auto
 moreover 
  assume asump:"finite A \_and Set_P P__a A \_and P__a a \_and p A"
  from this have "Set__finite_p__stp P__a A" 
  by (simp add:Set__finite_p_imp_finite_stp)
 moreover 
  from asump have "Fun_PD P__a A" by (simp only:Set_Set_P_Fun_PD)
 ultimately show "p (insert a A)" using asump 
  by (auto)
 next
  from `Set_P P__a s` show "Set_P P__a s" 
  by(simp)
 qed
qed
end-proof

proof Isa induction
  proof - (* induct_tac s rule:finite_induct, auto *)
 assume ASM: "Fun_PD finite (p::'a Set__FiniteSet \_Rightarrow bool)"
             "finite (s::'a set)"   "p {}" 
             "\_forall(s::'a set) (x::'a). finite s \_and p s \_longrightarrow p (insert x s)"
 thus "p (s::'a Set__FiniteSet)"
 proof (induct_tac s rule:finite_induct)
  assume "finite s" thus "finite s" by assumption
 next
  assume "p {}" thus "p {}" by assumption
 next    
  fix x F 
  assume "finite F" "x \_notin F" "p F"
  from ASM obtain s y where "s = s" and "x = x" 
                        and "finite s \_and p s \_longrightarrow p (insert x s)"
  by auto
  from this ASM `finite F` `p F` show "p(insert x F)" by blast
 qed
qed
end-proof
(*** SIZE HELPERS ***)
proof Isa -verbatim
fun SIZ::"('a\_Rightarrowbool) \_Rightarrow ('a set) \_Rightarrow nat"
where 
"SIZ p s = 
         (if (\_not (Set__finite_p__stp p s) \_or \_not (Fun_PD p s))
          then regular_val else card s)" 
lemma SIZ_CARD[rule_format]:
 "\_lbrakkSet__finite_p__stp p s; Fun_PD p s\_rbrakk
  \_Longrightarrow SIZ p s = card s" 
by simp
end-proof


op size : [a] FiniteSet a -> Nat = the(size)
  (size empty = 0) &&
  (fa (s: FiniteSet a, x:a) size (s <| x) = 1 + size (s - x))

proof Isa size_Obligation_the
 sorry
end-proof

op [a] hasSize (s:Set a, n:Nat) infixl 20 : Bool =
  finite? s && size s = n

(* In order to fold over a finite set, we need the folding function to be
insensitive to order (a kind of commutativity property). It is not necessary
that it is also insensitive to repetitions (a kind of idempotence property),
because we can remove elements from the set as we fold. It is also not necessary
that the function is commutative on its whole domain: it is sufficient that it
is commutative on the elements of the set that we are folding over. *)

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

proof Isa fold__stp_Obligation_the
 sorry
end-proof

proof Isa fold_Obligation_the
 sorry
end-proof

% finite powerset:

op [a] powerf (s:Set a) : Set (FiniteSet a) = power s /\ finite?

proof Isa powerf__stp_Obligation_subtype
 sorry
end-proof

proof Isa powerf_Obligation_subtype
 sorry
end-proof

% infinite, countable, and uncountable cardinality:

op infinite? : [a] Set a -> Bool = ~~ finite?

type InfiniteSet a = (Set a | infinite?)

op [a] countable? (s:Set a) : Bool =
  infinite? s &&
  % there is a surjective function from Nat to {x:a | x in? s}
  % (the latter is a "pseudo-type" because of the free variable `s'):
  (ex (f : Nat -> a)
     (fa(x:a) x in? s => (ex(i:Nat) f i = x)))

type CountableSet a = (Set a | countable?)

op uncountable? : [a] Set a -> Bool = infinite? /\  ~~ countable?

type UncountableSet a = (Set a | uncountable?)

% minimum/maximum set:

op [a] isMinIn (s:Set a, ss:Set (Set a)) infixl 20 : Bool =
  s in? ss && (fa(s1) s1 in? ss => s <= s1)
proof Isa -> isMinIn_s end-proof

op [a] hasMin? (ss:Set (Set a)) : Bool = (ex(s) s isMinIn ss)

type SetOfSetsWithMin a = (Set (Set a) | hasMin?)

op [a] min (ss: SetOfSetsWithMin a) : Set a = the(s) s isMinIn ss

proof Isa  Set__min_Obligation_the
  apply(auto simp add: Set__hasMin_p_def isMinIn_s_def)
end-proof

op [a] isMaxIn (s:Set a, ss:Set (Set a)) infixl 20 : Bool =
  s in? ss && (fa(s1) s1 in? ss => s >= s1)
proof Isa -> isMaxIn_s end-proof

op [a] hasMax? (ss:Set (Set a)) : Bool = (ex(s) s isMaxIn ss)

type SetOfSetsWithMax a = (Set (Set a) | hasMax?)

op [a] max (ss: SetOfSetsWithMax a) : Set a = the(s) s isMaxIn ss

proof Isa  Set__max_Obligation_the
  apply(auto simp add: Set__hasMax_p_def isMaxIn_s_def)
end-proof

% mapping to Isabelle:

proof Isa Thy_Morphism Set
  type Set.Set -> set (id,id)
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
