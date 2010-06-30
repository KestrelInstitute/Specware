Function qualifying spec

import Boolean

proof Isa -subtype_constrs -free-theorems -stp-theorems -stp-op-obligations end-proof

(* Functions are built-in in Metaslang (A -> B is the type of all functions from
type A to type B). This spec introduces some operations on functions and some
subtypes of functions. *)

% identity and composition:

op id : [a] a -> a = fn x -> x

op [a,b,c] o (g: b -> c, f: a -> b) infixl 24 : a -> c = fn x:a -> g (f x)

theorem identity is [a,b]
  fa (f: a -> b) id o f = f
              && f o id = f
proof Isa identity__stp
  apply(auto)
  apply(rule ext, simp)+
end-proof

theorem associativity is [a,b,c,d]
  fa (f: a -> b, g: b -> c, h: c -> d) (h o g) o f = h o (g o f)
proof Isa
  apply(simp add: o_assoc)
end-proof
proof Isa associativity__stp
  apply(rule ext, simp)
end-proof

% forward (a.k.a. diagrammatic) composition:

op [a,b,c] :> (f: a -> b, g: b -> c) infixl 24 : a -> c = g o f

% injectivity, surjectivity, bijectivity:

op [a,b] injective? (f: a -> b) : Bool =
  fa (x1:a,x2:a) f x1 = f x2 => x1 = x2
proof Isa
  apply(simp add: inj_on_def)
end-proof

proof Isa -verbatim
lemma Function__injective_p__stp_simp [simp]:
  "Function__injective_p__stp P f = (inj_on f P)"
  by (auto simp add: Function__injective_p__stp_def inj_on_def mem_def)
end-proof

op [a,b] surjective? (f: a -> b) : Bool =
  fa (y:b) (ex (x:a) f x = y)
proof Isa
  apply(simp add: surj_def eq_commute)
end-proof

proof Isa -verbatim
lemma Function__surjective_p__stp_simp[simp]:
  "Function__surjective_p__stp (A,B) f = surj_on f A B"
  by (auto simp add: Function__surjective_p__stp_def
                     Ball_def Bex_def mem_def surj_on_def)
end-proof

op [a,b] bijective? (f: a -> b) : Bool =
  injective? f && surjective? f
proof Isa
  apply(simp add: bij_def)
end-proof

proof Isa -verbatim
lemma Function__bijective_p__stp_simp[simp]:
  "Function__bijective_p__stp (A,B) f = bij_ON f A B"
  by (simp add: Function__bijective_p__stp_def bij_ON_def)
end-proof

proof Isa -verbatim
lemma Function__bijective_p__stp_univ[simp]:
  "Function__bijective_p__stp (A,\_lambda x. True) f = bij_on f A UNIV"
  by (simp add: univ_true bij_ON_UNIV_bij_on)
end-proof

proof Isa -verbatim
lemma Function__bij_inv_stp:
  "Function__bijective_p__stp (A,\_lambda x. True) f \_Longrightarrow
   Function__bijective_p__stp (\_lambdax. True, A) (inv_on A f)"
  by (simp add: univ_true bij_ON_imp_bij_ON_inv)
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
lemma Function__inverse__stp_alt:
  "\_lbrakkinj_on f A; y \_in f`A\_rbrakk \_Longrightarrow
   Function__inverse__stp A f y = inv_on A f y"
  by (auto simp add: Function__inverse__stp_def, 
      rule the_equality, auto simp add:mem_def inj_on_def)
end-proof

proof Isa -verbatim
lemma Function__inverse__stp_apply [simp]:
  "\_lbrakkbij_ON f A B; y \_in B\_rbrakk \_Longrightarrow
   Function__inverse__stp A f y = inv_on A f y"
  by(auto simp add: bij_ON_def surj_on_def,
     erule Function__inverse__stp_alt,
     simp add: image_def)
end-proof

proof Isa -verbatim
lemma Function__inverse__stp_simp:
  "bij_on f A UNIV \_Longrightarrow Function__inverse__stp A f = inv_on A f"
  by (rule ext, simp add: bij_ON_UNIV_bij_on [symmetric])
end-proof

proof Isa -verbatim
lemma Function__inverse__stp_bijective:
  "\<lbrakk>Function__bijective_p__stp (A, B) f; defined_on f A B\<rbrakk>
   \<Longrightarrow>
   Function__bijective_p__stp (B, A) (Function__inverse__stp A f)"
proof -
 def fi \<equiv> "Function__inverse__stp A f"
 assume "defined_on f A B"
 assume "Function__bijective_p__stp (A, B) f"
 hence "inj_on f A" and "surj_on f A B" by (auto simp add: bij_ON_def)
 have "inj_on fi B"
 proof (auto simp add: inj_on_def)
  fix y1 y2
  assume "y1 \<in> B" and "y2 \<in> B" and "fi y1 = fi y2"
  from `surj_on f A B` `y1 \<in> B`
   obtain x1 where "x1 \<in> A" and "y1 = f x1"
    by (auto simp add: surj_on_def)
  hence "A x1 \<and> f x1 = y1" by (auto simp add: mem_def)
  with `inj_on f A` have "\<And>x. A x \<and> f x = y1 \<Longrightarrow> x = x1"
   by (auto simp add: inj_on_def mem_def)
  with `A x1 \<and> f x1 = y1`
   have "(THE x. A x \<and> f x = y1) = x1" by (rule the_equality)
  hence "x1 = fi y1" by (auto simp add: fi_def Function__inverse__stp_def)
  from `surj_on f A B` `y2 \<in> B`
   obtain x2 where "x2 \<in> A" and "y2 = f x2"
    by (auto simp add: surj_on_def)
  hence "A x2 \<and> f x2 = y2" by (auto simp add: mem_def)
  with `inj_on f A` have "\<And>x. A x \<and> f x = y2 \<Longrightarrow> x = x2"
   by (auto simp add: inj_on_def mem_def)
  with `A x2 \<and> f x2 = y2`
   have "(THE x. A x \<and> f x = y2) = x2" by (rule the_equality)
  hence "x2 = fi y2" by (auto simp add: fi_def Function__inverse__stp_def)
  with `x1 = fi y1` `fi y1 = fi y2` have "x1 = x2" by auto
  with `y1 = f x1` `y2 = f x2` show "y1 = y2" by auto
 qed
 have "surj_on fi B A"
 proof (auto simp add: surj_on_def)
  fix x
  assume "x \<in> A"
  def y \<equiv> "f x"
  with `x \<in> A` `defined_on f A B` have "y \<in> B"
   by (auto simp add: defined_on_def)
  have "x = fi y"
  proof -
   from `x \<in> A` y_def have "A x \<and> f x = y" by (auto simp add: mem_def)
   with `inj_on f A` have "\<And>z. A z \<and> f z = y \<Longrightarrow> z = x"
    by (auto simp add: inj_on_def mem_def)
   with `A x \<and> f x = y`
    have "(THE z. A z \<and> f z = y) = x" by (rule the_equality)
   thus "x = fi y" by (auto simp add: fi_def Function__inverse__stp_def)
  qed
  with `y \<in> B` show "\<exists>y \<in> B. x = fi y" by auto
 qed
 with `inj_on fi B` have "bij_ON fi B A" by (auto simp add: bij_ON_def)
 with fi_def show ?thesis by auto
qed
end-proof

proof Isa inverse__stp_Obligation_the
  apply(auto simp add:
          bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
  apply(rotate_tac -1, drule_tac x="y" in spec, auto)
end-proof

proof Isa inverse_Obligation_the
  apply(auto simp add: bij_def surj_def inj_on_def)
  apply(drule spec, erule exE, drule sym, auto)
end-proof


proof Isa -verbatim
lemma Function__inverse__stp_eq:
  "\_lbrakk\_exists!x. P x \_and f x = y; g = Function__inverse__stp P f\_rbrakk 
    \_Longrightarrow P (g y) \_and f (g y) = y "
  by (simp add: Function__inverse__stp_def, rule the1I2, simp_all)
end-proof

proof Isa -verbatim
lemma Function__inverse__stp_eq_props:
  "\_lbrakkbij_ON f P Q; Function__inverse__stp P f = g; Q y\_rbrakk 
     \_Longrightarrow P (g y) \_and f (g y) = y "  
  apply (cut_tac f=f and g=g and P=P and y=y in Function__inverse__stp_eq)
  apply(auto simp add:
          bij_ON_def surj_on_def Ball_def Bex_def inj_on_def mem_def)
done
end-proof

proof Isa -verbatim
lemma Function__inverse__stp_eq_props_true:
  "\_lbrakkbij_ON f P TRUE; Function__inverse__stp P f = g\_rbrakk 
     \_Longrightarrow P (g y) \_and f (g y) = y "  
  by (simp add: Function__inverse__stp_eq_props)
end-proof

proof Isa inverse_subtype_constr
  apply(auto simp add: bij_def)
  apply(erule surj_imp_inj_inv)
  apply(erule inj_imp_surj_inv)
end-proof

(* The following Isabelle lemma enables the use of SOME to define inverse, which
is sometimes more convenient than THE because only existence of a solution must
be shown in a proof, not uniqueness. *)
proof Isa -verbatim
lemma inverse_SOME:
 "\<lbrakk> Function__bijective_p__stp (domP,codP) f ; codP y \<rbrakk>
  \<Longrightarrow>
  Function__inverse__stp domP f y = (SOME x. domP x \<and> f x = y)"
proof (auto simp add: Function__bijective_p__stp_def Function__inverse__stp_def)
 assume CY: "codP y"
 assume INJ: "inj_on f domP"
 assume SURJ: "surj_on f domP codP"
 from SURJ have "\<forall>y \<in> codP. \<exists>x \<in> domP. f x = y"
  by (auto simp add: surj_on_def)
 with CY have "\<exists>x \<in> domP. f x = y" by (auto simp add: mem_def)
 then obtain x where DX: "domP x" and YX: "f x = y"
  by (auto simp add: mem_def)
 hence X: "domP x \<and> f x = y" by auto
 have "\<And>x'. domP x' \<and> f x' = y \<Longrightarrow> x' = x"
 proof -
  fix x'
  assume "domP x' \<and> f x' = y"
  hence DX': "domP x'" and YX': "f x' = y" by auto
  from INJ have
   "\<forall>x \<in> domP. \<forall>x' \<in> domP.
      f x = f x' \<longrightarrow> x = x'"
   by (auto simp add: inj_on_def)
  with DX DX' have "f x = f x' \<Longrightarrow> x = x'"
   by (auto simp add: mem_def)
  with YX YX' show "x' = x" by auto
 qed
 with X have "\<exists>!x. domP x \<and> f x = y" by (auto simp add: mem_def)
 thus "(THE x. domP x \<and> f x = y) = (SOME x. domP x \<and> f x = y)"
  by (rule THE_SOME)
qed
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
proof Isa f_inverse_apply__stp
  apply(auto simp add: mem_def bij_ON_def)
end-proof

theorem inverse_f_apply is [a,b]
  fa(f:Bijection(a,b), x: a) inverse f(f (x)) = x
proof Isa
  apply(simp add: bij_def inv_f_f)
end-proof
proof Isa inverse_f_apply__stp
  apply(auto simp add: mem_def bij_ON_def)
end-proof

theorem fxy_implies_inverse is [a,b]
  fa (f:Bijection(a,b), x:a, y:b) f x = y => x = inverse f y
proof Isa
proof -
 assume BIJ: "bij (f::'a \<Rightarrow> 'b)"
 assume FXY: "f x = y"
 have INV_SOME: "inv f y = (SOME x. f x = y)" by (auto simp add: inv_def)
 from FXY have "\<exists>x. f x = y" by auto
 hence "f (SOME x. f x = y) = y" by (rule someI_ex)
 with FXY have EQF: "f x = f (SOME x. f x = y)" by auto
 from BIJ have "\<And>x'. f x = f x' \<Longrightarrow> x = x'"
  by (auto simp add: bij_def inj_on_def)
 with EQF have "x = (SOME x. f x = y)" by auto
 with INV_SOME show "x = inv f y" by auto
qed
end-proof
proof Isa fxy_implies_inverse__stp
proof -
 assume BIJ: "Function__bijective_p__stp (P__a, P__b) f"
 assume PF: "Fun_P(P__a, P__b) f"
 assume PX: "P__a (x::'a)"
 assume PY: "P__b (y::'b)"
 assume FXY: "f x = y"
 have INV_THE:
      "Function__inverse__stp P__a f y = (THE x. P__a x \<and> f x = y)"
  by (auto simp add: Function__inverse__stp_def)
 from PX FXY have X: "P__a x \<and> f x = y" by auto
 have "\<And>x'. P__a x' \<and> f x' = y \<Longrightarrow> x' = x"
 proof -
  fix x'
  assume "P__a x' \<and> f x' = y"
  hence PX': "P__a x'" and FXY': "f x' = y" by auto
  from FXY FXY' have FXFX': "f x = f x'" by auto
  from BIJ have "inj_on f P__a"
   by (auto simp add: Function__bijective_p__stp_def)
  with PX PX' have "f x = f x' \<Longrightarrow> x = x'"
   by (auto simp add: inj_on_def mem_def)
  with FXFX' show "x' = x" by auto
 qed
 with X have "(THE x. P__a x \<and> f x = y) = x" by (rule the_equality)
 with INV_THE show ?thesis by auto
qed
end-proof

% eta conversion:

theorem eta is [a,b]
  fa(f: a -> b) (fn x -> f x) = f
proof Isa eta__stp
  apply(rule ext, simp)
end-proof

% mapping to Isabelle:

proof Isa ThyMorphism
  Function.id          -> id
  Function.o           -> o Left 55
  Function.:>          -> o Left 55 reversed
  Function.injective?  -> inj
  Function.surjective? -> surj
  Function.bijective?  -> bij
  Function.inverse     -> inv
end-proof

#translate Haskell ThyMorphism
  Function.id          -> id
  Function.o           -> . Right 9
  Function.:>          -> . Right 9 reversed
#end


endspec
