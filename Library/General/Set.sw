(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Set qualifying spec

(* In higher-order logic, it is customary to define a set as a predicate: the
predicate is true exactly for (i.e. for all and only) the elements of the set.

In this spec we follow that customary approach, which is very clear and
simple. All the types and ops in this spec are defined, i.e. this spec is a
definitional extension; therefore, it is readily seen to be consistent. *)

import Pred

%type Predicate a = a -> Bool
type Set a = Predicate a

%%% Generate stp versions of finite_insert and induction in case they are useful later
proof Isa -stp-theorems end-proof

% membership:

op [a] in? (x:a, s:Set a) infixl 20 : Bool = s x

op [a] nin? (x:a, s:Set a) infixl 20 : Bool = ~(x in? s)

%% Used for coercion between Isabelle sets and predicates
%% Seems to be used for special (not yet working) syntax for sets, using braces.
op [a] collect (P: Predicate a): Set a = P

op [a] r_in? (s:Set a) (x:a): Bool = s x
proof Isa -> setToPred end-proof


proof Isa -verbatim
lemma Collect__setToPred__inverses1 [simp]:
  "Collect(setToPred s) = s"
  by (rule set_eqI, simp add: setToPred_def)

lemma Collect__setToPred__inverses2 [simp]:
  "setToPred(Collect f) = f"
  by  (rule ext, simp add: setToPred_def)


(*** Lemmas About Set_P RSet and Fun_PD ***)

lemma Set_Set_P_converse: "Set_P P A \<Longrightarrow> (\<forall> x \<in> A . P x)"
  by (auto simp add: Set_P_def)
lemma Set_P_unfold:       "Set_P P A = (\<forall> x \<in> A . P x)"
  by (auto simp add: Set_P_def)
lemma Set_Fun_PD_Set_P:   "Fun_PD P A \<Longrightarrow> Set_P P (Collect A)"
  by (simp add: Set_P_def)
lemma Set_Set_P_Fun_PD:   "Set_P P A \<Longrightarrow> Fun_PD P (setToPred A)"
  by (simp add: setToPred_def Set_P_def)
lemma Set_Set_P_RSet:     "Set_P P A \<Longrightarrow> (RSet P A = A)"
  by (auto simp add: Set_P_def)
end-proof

% Lifting a predicate from elements to regularized sets
op [a] Set_P (Pa: a -> Bool) (s:Set a): Bool =
  fa(x: a) ~(Pa x) => x nin? s     % contrapositive: x in? s => Pa x

% (strict) sub/superset:

% subset:

op [a] <= (s1:Set a, s2:Set a) infixl 20 : Bool =
  fa(x) x in? s1 => x in? s2

% proper subset (strict subset):

op [a] < (s1:Set a, s2:Set a) infixl 20 : Bool = (s1 <= s2 && s1 ~= s2)

% superset:

op [a] >= (s1:Set a, s2:Set a) infixl 20 : Bool = (s2 <= s1)

% proper superset (strict superset):

op [a] > (s1:Set a, s2:Set a) infixl 20 : Bool = (s2 < s1)

proof Isa -verbatim
lemma Set_Set_P_subsets_equiv:
  "Set_P P__a A \_Longrightarrow
    (Set__e_lt_eq__stp P__a ((A::'a set),(B::'a set)) = (A \_subseteq B))"
  by (auto simp add: Set__e_lt_eq__stp_def Set__e_lt_eq__def Set_P_def )
end-proof

% complement, intersection, and union (lift `~', `&&', and `||' to sets):

%% op [a] ~~ (s:Set a) : Set a = fn x:a -> x nin? s

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

op [a] empty? (s:Set a) : Bool = (s = empty)

proof Isa -verbatim
lemma Set_empty_apply[simp]:  "x \<in> {} = False"       by auto
lemma Set_RSet_empty[simp]:   "RSet P_a {} = {}"   by auto
lemma Set_Set_P_empty[simp]:  "Set_P P {} = True"  by (simp add:Set_P_def)
lemma Set_Fun_PD_empty[simp]: "Fun_PD P (setToPred {}) = True" by (simp add: setToPred_def)
lemma Set_empty_p_equiv_empty_p_stp:
   "Set__empty_p s = Set__empty_p__stp P__a s"     by auto
end-proof

% sets with at least 1 element:

op [a] nonEmpty? (s:Set a) : Bool = (s ~= empty)

type Set1 a = (Set a | nonEmpty?)

proof Isa -verbatim
lemma Set__nonEmpty_p_stp_equ_nonEmpty_p_stp:
  "Set__nonEmpty_p__stp P__a s = Set__nonEmpty_p s"
  by (auto simp add:Set__nonEmpty_p__stp_def Set__nonEmpty_p_def)
lemma Set__nonEmpty_p_stp_EX_x_t:
  "\_lbrakk Set_P P__a s; Set__nonEmpty_p__stp P__a (s::'a set)\_rbrakk \_Longrightarrow
    (\_exists (x::'a) (t::'a set). P__a x \_and x \_notin t \_and (s = insert x t))"
proof(cases "s = {}")
 assume "Set_P P__a s" "Set__nonEmpty_p__stp P__a s" "s = {}"
 from this show ?thesis by(auto simp:Set__nonEmpty_p__stp_def)
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

op [a] full? (s:Set a) : Bool = (s = full)

proof Isa -verbatim
lemma Set__full_stp_apply:    "\_lbrakkP__a x; Set__full_p__stp P__a s\_rbrakk \_Longrightarrow x \_in s"
  by (auto simp add:Set__full_p__stp_def)
end-proof

% sets with exactly one element:

op [a] single(*ton*) (x:a) :Set a = fn y:a -> y = x

op [a] single? (s:Set a) : Bool = (ex(x:a) s = single x)

op [a] onlyMemberOf (x:a, s:Set a) infixl 20 : Bool =
  single? s && x in? s

proof Isa -verbatim
lemma Set_single_simp [simp]:   "Set__single x = {x}"
  by (rule set_eqI, simp, simp add: Set__single_def)
lemma Set_single_simp_app1:     "x \<in> {x} = True"
  by auto
lemma Set_single_simp_app2:     "y \<in> {x} = (x = y)"
  by auto
lemma Set_Pa_Set_P_single:      "P__a (x::'a) \_Longrightarrow Set_P P__a (Set__single x)"
  by(auto simp:Set_P_def)
lemma Set_Pa_RSet_single[simp]: "P__a (x::'a)\_Longrightarrow RSet P__a (Set__single x) = Set__single x"
  by(auto simp:Set_P_def)
lemma Set_single_single_stp:    "\_lbrakk P__a x; x \_in s; Set__single_p s\_rbrakk \_Longrightarrow Set__single_p__stp P__a s"
  by (auto simp:Set__single_p__stp_def)
lemma Set_single_stp_single:    "\_lbrakkx \_in s; Set__single_p__stp P__a s\_rbrakk \_Longrightarrow Set__single_p s"
  by (auto simp:Set__single_p__stp_def)
end-proof

type Singleton a = (Set a | single?)

op [a] theMember (s:Singleton a) : a = the(x:a) x in? s

% add member to set (triangle points towards set):

op [a] <| (s:Set a, x:a) infixl 25 : Set a = s \/ single x

proof Isa -verbatim
lemma Set__RSet_insert_simp[simp]:
  "\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk \_Longrightarrow  (RSet P__a (insert x s) = (insert x s))"
  by (auto simp add:Set_P_def)
lemma Set__Set_P_insert:
  "\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk \_Longrightarrow Set_P P__a (insert x s)"
  by (auto simp add:Set_P_def)
(* sjw
lemma Set__Fun_PD_insert:
  "\_lbrakk Fun_PD P__a s; P__a (x::'a)\_rbrakk \_Longrightarrow Fun_PD P__a (insert x s)"
  proof(rule Set_Set_P_Fun_PD)
   assume "Fun_PD P__a (s::'a set)"  "P__a x"
   thus "Set_P P__a (insert x s)"
     by (simp add:Set_Fun_PD_Set_P Set__Set_P_insert)
  qed *)
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
  "\_lbrakk Set_P P__a s; P__a (x::'a)\_rbrakk \_Longrightarrow  (RSet P__a (s less x)) = (s less x)"
  by (auto simp add:Set_P_def)
lemma Set__SetP_less:
  "Set_P P__a s \_Longrightarrow Set_P P__a (s less x)"
  by(auto simp add:Set_P_def)
lemma Set_P_Set_P_Less2:
  "\_lbrakk Set_P P__a (s less x); P__a (x::'a)\_rbrakk \_Longrightarrow Set_P P__a s"
  by (auto simp: Set_P_def)


(* sjw
lemma Set_Fun_PD_less:
  "\_lbrakk Fun_PD P__a s; P__a (x::'a)\_rbrakk \_Longrightarrow Fun_PD P__a (s less x)"
  proof(rule Set_Set_P_Fun_PD)
   assume "Fun_PD P__a (s::'a set)"
          "P__a x"
   from this have "Set_P P__a s" by(simp add: Set_Fun_PD_Set_P)
   from this show "Set_P P__a (s less x)"
   by (rule_tac s=s and P__a=P__a in Set__SetP_less)
  qed *)
end-proof

% map (partial) function over set:
%% This map function is given special treatment in
%% Languages/MetaSlang/Transformations/Coercions.sw (see op
%% lifterFuns).

op [a,b] map (f: a -> b) (s:Set a) : Set b =
  fn y:b -> (ex(x:a) x in? s && y = f x)

op [a,b] mapPartial (f: a -> Option b) (s:Set a) : Set b =
  fn y:b -> (ex(x:a) x in? s && Some y = f x)

% inversely map function over set:

op [a,b] imap (f: a -> b) (s:Set b) : Set a = fn x:a -> f x in? s

(* A function f from a to b generates a Set b, namely the set of all
y:b such that y = f x for some x:a. *)

op [a,b] setGeneratedBy (f: a -> b) : Set b = map f full


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

% **** Lemmas for subtyped predicate + finite

proof Isa -verbatim
lemma finite_stp_nat_seg:
  "Set__finite_p__stp (P__a::'a\_Rightarrow bool) (s::'a set) \_Longrightarrow
   (\_exists(f::nat \_Rightarrow 'a) (n::nat).
          (\_forall(x::'a). P__a x  \_longrightarrow (x \_in s) = (\_exists(i::nat). i < n \_and f i = x)))"
  proof (simp only:Set__finite_p__stp_def, erule disjE)
   fix s
   assume "Set__empty_p__stp P__a s"
   from this have "s = {}" by simp
   obtain f n where "(f::nat\_Rightarrow'a) = (\_lambda i. default_val)"
                and "(n::nat)=(0::nat)" by auto
   from `s = {}` show "(\_exists(f::nat \_Rightarrow 'a) (n::nat).
     (\_forall(x::'a). P__a x  \_longrightarrow (x \_in s) = (\_exists(i::nat). i < n \_and f i = x)))"
    by auto
  next
   fix P__a s
   assume " \_exists(f::nat \_Rightarrow 'a) n::nat.
         Fun_PR P__a f \_and
         ( \_forall  x::'a.
             P__a x \_longrightarrow
             (x \_in s) =
             (\_exists i<n. f i = x))"
   thus "\_exists(f::nat \_Rightarrow 'a) n::nat.
          \_forall x::'a.
            P__a x \_longrightarrow
            (x \_in s) = (\_exists i<n. f i = x)" by auto
  qed
end-proof

type FiniteSet a = (Set a | finite?)

(* Lemmas for proofs about finite sets *)
proof Isa -verbatim
lemma Set__finite_insert__stp_sans:
"\_lbrakk Set__finite_p__stp P__a (s::'a set); Set_P P__a s;
  P__a (x::'a)\_rbrakk \_Longrightarrow
 Set__finite_p__stp P__a (insert x (s::'a set))"
proof -
assume ps:"Set__finite_p__stp P__a (s::'a set)"
           "Set_P P__a s"
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

(* Additional Lemmas For Later Proofs *)
proof Isa -verbatim
lemma Set__finite_p_stp_imp_finite:
"\_lbrakk Set__finite_p__stp (P__a::'a\_Rightarrow bool) (s::'a set); Set_P P__a s\_rbrakk
 \_Longrightarrow finite s"
by (auto simp add:Set__finite_p__def Set__finite_p__stp_def Set_P_def,
    blast)
lemma Set__finite_p_imp_finite_stp:
"\_lbrakk finite (s::'a set); Set_P (P__a::'a\_Rightarrow bool) s\_rbrakk \_Longrightarrow Set__finite_p__stp P__a s"
proof(induct s rule: finite.induct)
 show "Set__finite_p__stp P__a {}"
 by (auto simp:Set__finite_p__stp_def)
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
 from `Set_P P__a A` have "Fun_PD P__a (setToPred A)" by (rule Set_Set_P_Fun_PD)
 from `Set__finite_p__stp P__a A` this `P__a a`
 have "Set__finite_p__stp P__a (RSet P__a (insert a A))"
   by (metis Set__finite_insert__stp `Set_P P__a A`)
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
  "\_lbrakk Set__finite_p__stp P__a (s::'a set);
    Set_P P__a s;
    P__a (x::'a)\_rbrakk \_Longrightarrow
   Set__finite_p__stp P__a (s less x)"
proof (rule_tac s="s less x" in Set__finite_p_imp_finite_stp)
 assume "Set__finite_p__stp P__a (s::'a set)"
        "Set_P P__a s"
        "P__a (x::'a)"
 then have "finite s" by(auto simp: Set_Fun_PD_Set_P Set__finite_p_stp_imp_finite)
 thus "finite (s less x)" by auto
next
 assume "Set_P P__a s"
 thus "Set_P P__a (SW_Set.less s x)"
 by(simp only:Set_Fun_PD_Set_P Set__SetP_less)
qed
lemma Set__finite_less__stp:
  "\_lbrakk Set__finite_p__stp P__a (s::'a set);
    Set_P P__a s;
    P__a (x::'a)\_rbrakk \_Longrightarrow
   Set__finite_p__stp P__a (RSet P__a (s less x))"
by(simp only:Set_Fun_PD_Set_P Set__RSet_less_simp
                     Set__finite_less__stp_sans)
lemma finite_induct_stp[rule_format]:
"\_lbrakkfinite (S::'a set);
  (P::('a set) \_Rightarrow bool) {};
  \_forall(A::'a set) a::'a. finite A \_and Set_P PA A \_and PA a \_and P A \_longrightarrow P (insert a A)\_rbrakk
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

% -------------------------------------------------------
proof Isa -verbatim
theorem Set__Finite_to_list:
  "\<lbrakk>Set__finite_p__stp P S; Set_P P S; Set__nonEmpty_p__stp P S\<rbrakk>
     \<Longrightarrow> \<exists>l. (l \<noteq> [] \<and> S = set l \<and> list_all P l)"
   apply (simp add: Set_P_def Set__finite_p__stp_def
                    Set__nonEmpty_p__stp_def list_all_iff,
          clarify)
   apply (rule_tac x="map f [0..<n]" in exI, auto)
done
end-proof
% -------------------------------------------------------

theorem induction is [a]
  fa (p: FiniteSet a -> Bool)
    p empty &&
    (fa (s: FiniteSet a, x:a) p s => p (s <| x)) =>
    (fa (s: FiniteSet a) p s)



(*** SIZE HELPERS ***)
proof Isa -verbatim
fun SIZ::"('a\_Rightarrowbool) \_Rightarrow ('a set) \_Rightarrow nat"
where
"SIZ p s =
         (if (\_not (Set__finite_p__stp p s) \_or \_not (Set_P p s))
          then regular_val else card s)"
lemma SIZ_CARD[rule_format]:
 "\_lbrakkSet__finite_p__stp p s; Set_P p s\_rbrakk
  \_Longrightarrow SIZ p s = card s"
by simp
end-proof


op size : [a] FiniteSet a -> Nat = the(size)
  (size empty = 0) &&
  (fa (s: FiniteSet a, x:a) size (s <| x) = 1 + size (s - x))



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

% ------------------------------------------------------------------------------
proof Isa -verbatim

(*******************************************************************************
* The following lemmas are similar to lemmas in Finite_Set.thy that have been
* proven in the context
*
*     "fun_left_comm f \<equiv> \<forall>x y z. f x (f y z) = f y (f x z)"
*
* We need to reprove them in the weakened context
*
*     "\<forall>x y z. x\<in>A \<and> y\<in>A  \<longrightarrow>  f x (f y z) = f y (f x z)"
*
* For this purpose we need to temporarily revive two rules that have been deleted
* from the set of rules at the end of Finite_Set.thy
*******************************************************************************)

declare
  empty_fold_graphE  [elim!]
  fold_graph.intros [intro!]

definition fun_left_comm_on :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> bool" where
  fun_left_comm_on_def:
  "fun_left_comm_on f A
     \<equiv> \<forall>x y z. x\<in>A \<and> y\<in>A  \<longrightarrow>  f x (f y z) = f y (f x z)"

(* Next 3 removed from Isabelle2009-2 Finite_Set.thy
   Ideally we should update our proof to be similar to the new ones in that theory *)
lemma image_less_Suc: "h ` {i. i < Suc m} = insert (h m) (h ` {i. i < m})"
  by (auto simp add: less_Suc_eq)

lemma insert_image_inj_on_eq:
     "[|insert (h m) A = h ` {i. i < Suc m}; h m \_notin A;
        inj_on h {i. i < Suc m}|]
      ==> A = h ` {i. i < m}"
apply (auto simp add: image_less_Suc inj_on_def)
apply (blast intro: less_trans)
done

lemma insert_inj_onE:
  assumes aA: "insert a A = h`{i::nat. i<n}" and anot: "a \_notin A"
      and inj_on: "inj_on h {i::nat. i<n}"
  shows "\_existshm m. inj_on hm {i::nat. i<m} & A = hm ` {i. i<m} & m < n"
proof (cases n)
  case 0 thus ?thesis using aA by auto
next
  case (Suc m)
  have nSuc: "n = Suc m" by fact
  have mlessn: "m<n" by (simp add: nSuc)
  from aA obtain k where hkeq: "h k = a" and klessn: "k<n" by (blast elim!: equalityE)
  let ?hm = "Fun.swap k m h"
  have inj_hm: "inj_on ?hm {i. i < n}" using klessn mlessn
    by (simp add: inj_on)
  show ?thesis
  proof (intro exI conjI)
    show "inj_on ?hm {i. i < m}" using inj_hm
      by (auto simp add: nSuc less_Suc_eq intro: subset_inj_on)
    show "m<n" by (rule mlessn)
    show "A = ?hm ` {i. i < m}"
    proof (rule insert_image_inj_on_eq)
      show "inj_on (Fun.swap k m h) {i. i < Suc m}" using inj_hm nSuc by simp
      show "?hm m \_notin A" by (simp add: swap_def hkeq anot)
      show "insert (?hm m) A = ?hm ` {i. i < Suc m}"
        using aA hkeq nSuc klessn
        by (auto simp add: swap_def image_less_Suc fun_upd_image
                           less_Suc_eq inj_on_image_set_diff [OF inj_on])
    qed
  qed
qed

lemma Diff1_fold_graph:
  "fold_graph f z (A - {x}) y \<Longrightarrow> x \<in> A \<Longrightarrow> fold_graph f z A (f x y)"
by (erule insert_Diff [THEN subst], rule fold_graph.intros, auto)

lemma fold_graph_imp_finite: "fold_graph f z A x \<Longrightarrow> finite A"
  by (erule fold_graph.induct, auto simp del: Set_empty_apply)

lemma fold_graph_determ_aux:
  "fun_left_comm_on f A  \<Longrightarrow> A = h`{i::nat. i<n} \<Longrightarrow> inj_on h {i. i<n}
   \<Longrightarrow> fold_graph f z A x \<Longrightarrow> fold_graph f z A x'
   \<Longrightarrow> x' = x"
proof (induct n arbitrary: A x x' h rule: less_induct)
  case (less n)
  have IH: "\<And>m h A x x'. m < n \<Longrightarrow> fun_left_comm_on f A  \<Longrightarrow>  A = h ` {i. i<m}
      \<Longrightarrow> inj_on h {i. i<m} \<Longrightarrow> fold_graph f z A x
      \<Longrightarrow> fold_graph f z A x' \<Longrightarrow> x' = x" by fact
  have  Afuncom: " fun_left_comm_on f A"
    and Afoldx: "fold_graph f z A x" and Afoldx': "fold_graph f z A x'"
    and A: "A = h`{i. i<n}" and injh: "inj_on h {i. i<n}" by fact+
  have FunLeftComm_fA: "fun_left_comm_on f A" by fact
  show ?case
  proof (rule fold_graph.cases [OF Afoldx])
    assume "A = {}" and "x = z"
    with Afoldx' show "x' = x" by auto
  next
    fix B b u
    assume  AbB:"A = insert b B" and x: "x = f b u"
      and notinB: "b \<notin> B" and Bu: "fold_graph f z B u"
    show "x'=x"
    proof (rule fold_graph.cases [OF Afoldx'])
      assume "A = {}" and "x' = z"
      with AbB show "x' = x" by blast
    next
      fix C c v
      assume AcC: "A = insert c C" and x': "x' = f c v"
        and notinC: "c \<notin> C" and Cv: "fold_graph f z C v"
      from A AbB have Beq: "insert b B = h`{i. i<n}" by simp
      from insert_inj_onE [OF Beq notinB injh]
      obtain hB mB where inj_onB: "inj_on hB {i. i < mB}"
        and Beq: "B = hB ` {i. i < mB}" and lessB: "mB < n" by auto
      from Afuncom AbB have Bfuncom: "fun_left_comm_on f B"
         by (simp add: fun_left_comm_on_def)
      from A AcC have Ceq: "insert c C = h`{i. i<n}" by simp
      from insert_inj_onE [OF Ceq notinC injh]
      obtain hC mC where inj_onC: "inj_on hC {i. i < mC}"
        and Ceq: "C = hC ` {i. i < mC}" and lessC: "mC < n" by auto
      from Afuncom AcC have Cfuncom: "fun_left_comm_on f C"
         by (simp add: fun_left_comm_on_def)
      show "x'=x"
      proof cases
        assume "b=c"
        then moreover have "B = C" using AbB AcC notinB notinC by auto
        ultimately show ?thesis
                   using Bu Cv x x' IH [OF lessC Cfuncom Ceq inj_onC]
          by auto
      next
        assume diff: "b \<noteq> c"
        let ?D = "B - {c}"
        have B: "B = insert c ?D" and C: "C = insert b ?D"
          using AbB AcC notinB notinC diff by(blast elim!:equalityE)+
        have "finite A" by(rule fold_graph_imp_finite [OF Afoldx])
        with AbB have "finite ?D" by simp
        then obtain d where Dfoldd: "fold_graph f z ?D d"
          using finite_imp_fold_graph by iprover
        moreover have cinB: "c \<in> B" using B by auto
        ultimately have "fold_graph f z B (f c d)" by(rule Diff1_fold_graph)
        hence "f c d = u"  by (rule IH [OF lessB Bfuncom Beq inj_onB Bu])
        moreover have "f b d = v"
        proof (rule IH[OF lessC Cfuncom Ceq inj_onC Cv])
          show "fold_graph f z C (f b d)" using C notinB Dfoldd by auto
        qed
        ultimately show ?thesis
          using Afuncom AbB AcC x x'  by (auto simp add: fun_left_comm_on_def)
      qed
    qed
  qed
qed

lemma fold_graph_determ:
  "\<lbrakk>fun_left_comm_on f A; fold_graph f z A x; fold_graph f z A y\<rbrakk> \<Longrightarrow> y = x"
apply (frule fold_graph_imp_finite [THEN finite_imp_nat_seg_image_inj_on])
apply (erule exE, erule exE, erule conjE)
apply (drule fold_graph_determ_aux, auto)
done

(* There is now a fold in List.thy - we need the one from Finite_Set *)

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "fold f z A = (THE y. fold_graph f z A y)"

lemma fold_equality:
  "\<lbrakk>fun_left_comm_on f A; fold_graph f z A y\<rbrakk> \<Longrightarrow> fold f z A = y"
by (unfold fold_def) (blast intro: fold_graph_determ)

lemma fold_insert_aux:
 "\<lbrakk>fun_left_comm_on f (insert x A); x \<notin> A\<rbrakk>
  \<Longrightarrow> fold_graph f z (insert x A) v = (\<exists>y. fold_graph f z A y \<and> v = f x y)"
apply auto
apply (rule_tac A1=A and f1=f and z1=z in finite_imp_fold_graph [THEN exE])
apply (auto dest: fold_graph_imp_finite)
apply (rule_tac x=xa in exI, auto)
apply (drule fold_graph.insertI, auto)
apply (thin_tac "fold_graph f z A xa")
apply (cut_tac x=v and y="f x xa" in fold_graph_determ)
apply auto
done

lemma fold_insert:
  "\<lbrakk>finite A; x \<notin> A; fun_left_comm_on f (insert x A)\<rbrakk>
   \<Longrightarrow> fold f z (insert x A) = f x (fold f z A)"
apply (simp add: fold_def fold_insert_aux)
apply (subgoal_tac "fun_left_comm_on f A")
apply (rule the_equality)
apply (auto intro: finite_imp_fold_graph
        cong add: conj_cong simp add: fold_def[symmetric] fold_equality)
apply (simp add: fun_left_comm_on_def)
done


lemma fold_insert_remove:
 "\<lbrakk>finite A; fun_left_comm_on f (insert x A)\<rbrakk>
  \<Longrightarrow>  fold f z (insert x A) = f x (fold f z (A - {x}))"
  by (cut_tac A="A - {x}" and x=x in fold_insert, auto)

declare
  empty_fold_graphE [rule del]  fold_graph.intros [rule del]

(******************************************************************************)

end-proof
% ------------------------------------------------------------------------------

op fold : [a,b] ((b * (b * a -> b) * FiniteSet a) | foldable?) -> b =
  the(fold)
    (fa (c: b, f: b * a -> b) fold (c, f, empty) = c) &&
    (fa (c: b, f: b * a -> b, s: FiniteSet a, x: a)
       foldable? (c, f, s <| x) =>
         fold (c, f, s <| x) = f (fold (c, f, s - x), x))


% convert list to finite set:

op [a] toSet (l:List a) : FiniteSet a = fn x:a -> x in? l

% finite powerset:

%% op [a] powerf (s:Set a) : Set (FiniteSet a) = (power s /\ finite?)

op [a] powerf (s:Set a) : Set (FiniteSet a) =
  fn sub:Set a -> (sub in? power s) && finite? sub


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


op [a] isMaxIn (s:Set a, ss:Set (Set a)) infixl 20 : Bool =
  s in? ss && (fa(s1) s1 in? ss => s >= s1)
proof Isa -> isMaxIn_s end-proof

op [a] hasMax? (ss:Set (Set a)) : Bool = (ex(s) s isMaxIn ss)

type SetOfSetsWithMax a = (Set (Set a) | hasMax?)

op [a] max (ss: SetOfSetsWithMax a) : Set a = the(s) s isMaxIn ss


% ------------------------------------------------------------------------------
% ------------------ Theory Morphisms ------------------------------------------
% ------------------------------------------------------------------------------

% mapping to Isabelle:

proof Isa Thy_Morphism
  type Set.Set -> set (setToPred, Collect)
  % Set.collect -> Collect
  Set.Set_P -> Set_P
  Set.in? -> \<in> Left 50
  Set.nin? -> \<notin> Left 50
  Set.<= -> \<subseteq> Left 50
  Set.< -> \<subset> Left 50
  Set.>= -> \<subseteq> Left 50 reversed
  Set.> -> \<subset> Left 50 reversed
  Set.<| -> insert curried reversed
%%  Set.~~ -> -
  Set./\ -> \<inter> Left 70
  Set.//\\ -> \<Inter>
  Set.\/ -> \<union> Left 65
  Set.\\// -> \<Union>
  Set.-- -> - Left 65
  Set.* -> \<times> Left 67
  Set.map   -> image
  Set.power -> Pow
  Set.empty -> {}
  Set.full  -> UNIV
  Set.finite? -> finite
  Set.size -> card
  Set.theMember -> the_elem
  Set.min -> Inter
  Set.max -> Union
end-proof


% ------------------------------------------------------------------------------
% ------------------ The proofs ------------------------------------------------
% ------------------------------------------------------------------------------

proof Isa Set_P__def
  by (simp add: Set_P_def)
end-proof

proof Isa empty__def
  by (auto)
end-proof

proof Isa empty? [simp] end-proof

proof Isa empty_p__stp [simp] end-proof

proof Isa full__def
  by (auto)
end-proof

proof Isa full? [simp] end-proof

proof Isa single? [simp] end-proof

proof Isa onlyMemberOf [simp] end-proof

proof Isa  finite?__def
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
  by auto
 next
  assume "\_exists(f::nat \_Rightarrow 'a) n::nat. \_forall x::'a. (x \_in s) = (\_exists i<n. f i = x)"
  thus ?thesis by(rule nat_seq_finite)
 qed
qed
end-proof

proof Isa finite_insert__stp
by (auto simp only: Set__finite_insert__stp_sans Set_Set_P_Fun_PD Set__RSet_insert_simp)
end-proof

proof Isa Set__finite_insert
by auto
end-proof

proof Isa induction__stp_Obligation_subtype
  by (simp add: Set__finite_p__stp_def)
end-proof

proof Isa induction__stp_Obligation_subtype0
  by (rule Set__finite_insert__stp)
end-proof

proof Isa induction__stp
 by (induct_tac s rule:finite_induct_stp,
     auto simp: Set__finite_p_stp_imp_finite)
end-proof

(* sjw
 ****** ck removed OLD proof
  proof -
 assume
 "Fun_PD (Set__finite_p__stp (P__a::'a\_Rightarrowbool) && Set_P P__a) (p::'a set \_Rightarrow bool)"
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
qed  *)

proof Isa induction
  proof - (* induct_tac s rule:finite_induct, auto *)
 assume ASM: "Fun_PD finite (p::'a Set__FiniteSet \_Rightarrow bool)"
             "finite (s::'a set)"   "p {}"
             "\_forall(s::'a set) (x::'a). finite s \_and p s \_longrightarrow p (insert x s)"
 thus "p (s::'a Set__FiniteSet)"
 proof (induct_tac s rule: finite_induct)
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

proof Isa size_Obligation_the
 apply (rule_tac a="RFun finite card" in ex1I, simp_all, safe)
 apply (frule_tac x=x in card_insert_if, clarsimp,
        drule_tac x=x in card_Suc_Diff1, simp_all)
 apply (rule ext, clarsimp)
 apply (thin_tac _, induct_tac xa rule: finite_induct)
 apply (simp, simp only: card_empty)
 apply (drule_tac x=F in spec, drule mp, simp)
 apply (drule_tac x=xb in spec, simp)
end-proof

proof Isa size__def
  apply (simp, rule ext, auto)
  apply (rule_tac P="\<lambda>size__v. (\<forall>x. \<not> finite x \<longrightarrow> size__v x = regular_val) \<and>
            size__v {} = 0 \<and>
            (\<forall>s. finite s \<longrightarrow> (\<forall>x. size__v (insert x s) = Suc (size__v (s - {x}))))"
         in the1I2,
         cut_tac Set__size_Obligation_the, simp)
  apply (clarify,
         thin_tac "\<forall>x. \<not> finite x \<longrightarrow> xa x = regular_val")
  apply (induct_tac x rule: finite_induct)
  apply (simp, simp only: card_empty)
  apply (drule_tac x=F in spec, drule mp, simp)
  apply (drule_tac x=xb in spec, simp)
end-proof

proof Isa foldable? [simp] end-proof

proof Isa fold_Obligation_the
  apply (rule_tac a="(\<lambda>(c,f,s). if finite s \<and> Set__foldable_p (c,f,s)
                                   then fold (\<lambda>x y. f (y,x)) c s
                                   else regular_val)" in ex1I, auto)
  apply (rule fold_equality,
         auto simp: fold_graph.intros fun_left_comm_on_def
                    finite_imp_fold_graph)
  apply (drule_tac f="\<lambda>x y. f_1 (y,x)" in fold_insert_remove,
         simp add:fun_left_comm_on_def, auto)
  apply (rule ext, simp only: split_paired_all)
  apply (case_tac "finite b", simp_all)
  apply (induct_tac b rule: finite_induct, auto simp add: empty_false)
  apply (rule fold_equality [symmetric],
         auto simp: fold_graph.intros fun_left_comm_on_def
                    finite_imp_fold_graph)
  apply (drule_tac A=F and x=xa and z=a and f="\<lambda>x y. aa (y,x)"
         in fold_insert, simp_all add: fun_left_comm_on_def)
end-proof

proof Isa Set__toSet_Obligation_subtype
  by (simp)
end-proof

proof Isa  Set__min_Obligation_the
  apply(auto simp add: Set__hasMin_p_def isMinIn_s_def)
end-proof

proof Isa  Set__min__def
  apply (rule_tac P = "\<lambda>s. s isMinIn_s ss" in the1I2)
  apply (erule Set__min_Obligation_the)
  apply (auto simp add: isMinIn_s_def)
end-proof

proof Isa  Set__max_Obligation_the
  apply(auto simp add: Set__hasMax_p_def isMaxIn_s_def)
end-proof

proof Isa  Set__max__def
  apply (rule_tac P = "\<lambda>s. s isMaxIn_s ss" in the1I2)
  apply (erule Set__max_Obligation_the)
  apply (auto simp add: isMaxIn_s_def)
end-proof

% ------------------------------------------------------------------------------
proof Isa -verbatim


(**************************************************************************)
(* Extensions to SW_Set                                                   *)
(**************************************************************************)


lemma Set_P__stp_unfold_aux:
 "Set__Set_P__stp P Q A = (\<forall>x\<in>A\<inter>Collect P. Q x)"
by (auto simp add: Set__Set_P__stp_def)

lemma Set_P__stp_unfold:
 "Set__Set_P__stp P Q A = (\<forall>x. (x \<in> A \<and> P x) \<longrightarrow> Q x)"
by (auto simp add: Set__Set_P__stp_def)

lemma Set__infinite_nat_growth:
  "\<lbrakk>Set__infinite_p {i::nat. p i}\<rbrakk>  \<Longrightarrow> \<forall>j. \<exists>i>j. p i"
  apply (auto simp: Set__infinite_p_def fun_Compl_def setToPred_def
                    finite_nat_set_iff_bounded Bex_def not_less)
  apply (drule_tac x="Suc j" in spec, clarify)
  apply(rule_tac x=x in exI, auto )
done
end-proof


end-spec
