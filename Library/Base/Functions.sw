Functions qualifying spec
  
  % ------------------------------------------------------------------------
  % Make sure that the extensions to standard Isabelle are loaded
  % This is done solely for verification purposes
  % ------------------------------------------------------------------------

  import IsabelleExtensions 

  (* Functions are built-in in Metaslang (A -> B is the type of all functions
  from type A to type B). This spec introduces some operations on functions and
  some subtypes of functions. *)

  % identity and composition:

  op id : [a] a -> a = fn x -> x

  op [a,b,c] o (g: b -> c, f: a -> b) infixl 24 : a -> c = fn x:a -> g (f x)

  theorem identity is [a,b]
    fa (f: a -> b) id o f = f
                && f o id = f
  proof Isa Functions__identity__stp
    apply(auto)
    apply(rule ext, simp)+
  end-proof

  theorem associativity is [a,b,c,d]
    fa (f: a -> b, g: b -> c, h: c -> d) (h o g) o f = h o (g o f)
  proof Isa
    apply(simp add: o_assoc)
  end-proof
  proof Isa Functions__associativity__stp
    apply(rule ext, simp)
  end-proof

  % forward (a.k.a. diagrammatic) composition:

  op [a,b,c] :> (f: a -> b, g: b -> c) infixl 24 : a -> c = g o f

  % injectivity, surjectivity, bijectivity:

  op [a,b] injective? (f: a -> b) : Boolean =
    fa (x1:a,x2:a) f x1 = f x2 => x1 = x2
  proof Isa
    apply(simp add: inj_on_def)
  end-proof
  proof Isa -verbatim
lemma Functions__injective_p__stp_simp [simp]:
  "Functions__injective_p__stp P f = (inj_on f P)"
  by (auto simp add: Functions__injective_p__stp_def inj_on_def mem_def)
  end-proof
  

  op [a,b] surjective? (f: a -> b) : Boolean =
    fa (y:b) (ex (x:a) f x = y)
  proof Isa
    apply(simp add: surj_def eq_commute)
  end-proof
  proof Isa -verbatim
lemma Functions__surjective_p__stp_simp[simp]:
  "Functions__surjective_p__stp (A,B) f = surj_on f A B"
  by (auto simp add: Functions__surjective_p__stp_def Ball_def Bex_def mem_def surj_on_def)
end-proof

  op [a,b] bijective? (f: a -> b) : Boolean =
    injective? f && surjective? f
  proof Isa
    apply(simp add: bij_def)
  end-proof
  proof Isa bijective_p__stp end-proof
  proof Isa -verbatim
lemma Functions__bijective_p__stp_simp[simp]:
  "Functions__bijective_p__stp (A,B) f = bij_ON f A B"
  by (simp add: Functions__bijective_p__stp_def bij_ON_def)
lemma Functions__bijective_p__stp_univ[simp]:
  "Functions__bijective_p__stp (A,\<lambda>x. True) f = bij_on f A UNIV"
  by (simp add: Functions__bijective_p__stp_simp univ_true bij_ON_UNIV_bij_on)

lemma Functions__bij_inv_stp:
   "Functions__bijective_p__stp (A,\<lambda>x. True) f \<Longrightarrow> Functions__bijective_p__stp (\<lambda>x. True, A) (inv_on A f)"
   by (simp add: Functions__bijective_p__stp_simp univ_true bij_ON_imp_bij_ON_inv)
end-proof

  type Injection (a,b) = ((a -> b) | injective?)

  type Surjection(a,b) = ((a -> b) | surjective?)

  type Bijection (a,b) = ((a -> b) | bijective?)

  % inversion:

  op [a,b] inverse (f: Bijection(a,b)) : Bijection(b,a) =
    fn y:b -> the(x:a) f x = y
  proof Isa
    apply(rule sym, rule the_equality)
    apply(auto simp add: bij_def surj_f_inv_f)
  end-proof
  proof Isa -verbatim
lemma Functions__inverse__stp_alt:
   "\<lbrakk>inj_on f A; y \<in> f`A\<rbrakk> \<Longrightarrow> Functions__inverse__stp A f y = inv_on A f y"
   by (auto simp add: Functions__inverse__stp_def, 
       rule the_equality, auto simp add:mem_def inj_on_def)

lemma Functions__inverse__stp_apply [simp]:
   "\<lbrakk>bij_ON f A B; y \<in> B\<rbrakk> \<Longrightarrow> Functions__inverse__stp A f y = inv_on A f y"
    by(auto simp add: bij_ON_def surj_on_def,
       erule Functions__inverse__stp_alt,
       simp add: image_def)

lemma Functions__inverse__stp_simp:
   "bij_on f A UNIV \<Longrightarrow> Functions__inverse__stp A f = inv_on A f"
   by (rule ext, simp add: bij_ON_UNIV_bij_on [symmetric])
end-proof

  proof Isa inverse__stp_Obligation_subsort
    apply(simp only: Functions__bijective_p__stp_simp univ_true)
    apply(subgoal_tac "(\<lambda>y. THE x. P__a x \<and> f x = y) = inv_on P__a f", simp)    
    apply(simp add: bij_ON_imp_bij_ON_inv)
    apply(auto simp add: bij_ON_def, 
          thin_tac "\<forall>x0. \<not> P__a x0 \<longrightarrow> f x0 = arbitrary")
    apply(rule ext)
    apply(rule the_equality, auto)
    apply(simp add: surj_on_def Bex_def)
    apply(drule_tac x="y" in spec, auto simp add: mem_def)
  end-proof

  proof Isa inverse__stp_Obligation_the
    apply(auto simp add: bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
    apply(rotate_tac -1, drule_tac x="y" in spec, auto)
  end-proof

  (* Since we map SpecWare's "inverse f = \<lambda>y. THE x. f x = y)"
     to Isabelle's           "inv f     = \<lambda>y. SOME x. f x = y)"
     we need to show that this is the same if f is a bijection
  *)

  proof Isa inverse_Obligation_subsort
    apply(subgoal_tac "( \<lambda>y. THE x. f x = y) = inv f")
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
    apply(rule ext, rule the_equality, auto simp add: surj_f_inv_f)
  end-proof

  proof Isa inverse_Obligation_the
    apply(auto simp add: bij_def surj_def inj_on_def)
    apply(drule spec, erule exE, drule sym, auto)
  end-proof

  proof Isa inverse_subtype_constr
    apply(auto simp add: bij_def)
    apply(erule surj_imp_inj_inv)
    apply(erule inj_imp_surj_inv)
  end-proof

  theorem inverse_comp is [a,b]
    fa(f:Bijection(a,b)) f o inverse f = id
                      && inverse f o f = id
  proof Isa
    apply(simp add: bij_def surj_iff inj_iff)
  end-proof
  proof Isa inverse_comp__stp [simp]
    apply(auto)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
    apply(rule ext, clarsimp simp add: mem_def bij_ON_def)
  end-proof

  theorem f_inverse_apply is [a,b]
    fa(f:Bijection(a,b), x: b) f(inverse f (x)) = x
  proof Isa
    apply(simp add: bij_def surj_f_inv_f)
  end-proof

  theorem inverse_f_apply is [a,b]
    fa(f:Bijection(a,b), x: a) inverse f(f (x)) = x
  proof Isa
    apply(simp add: bij_def inv_f_f)
  end-proof
  proof Isa f_inverse_apply__stp
    apply(auto simp add: mem_def bij_ON_def)
  end-proof
  proof Isa inverse_f_apply__stp
    apply(auto simp add: mem_def bij_ON_def)
  end-proof

  % eta conversion:

  theorem eta is [a,b]
    fa(f: a -> b) (fn x -> f x) = f
  proof Isa eta__stp
    apply(rule ext, simp)
  end-proof

  % used by obligation generator:

  op  wfo: [a] (a * a -> Boolean) -> Boolean

  % mapping to Isabelle:

  proof Isa ThyMorphism
    Functions.id          -> id
    Functions.o           -> o Left 24
    Functions.:>          -> o Left 24 reversed
    Functions.injective?  -> inj
    Functions.surjective? -> surj
    Functions.bijective?  -> bij
    Functions.inverse     -> inv
  end-proof

endspec
