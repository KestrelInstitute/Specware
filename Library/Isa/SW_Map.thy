theory SW_Map
imports SW_Set Map
begin

theorem Map__domain__def: 
  "(x \<in> dom m) = (m x \<noteq> None)"
  by auto

theorem Map__range__def: 
  "(y \<in> ran m) = (\<exists>(x::'a). m x = Some y)"
   by (auto simp: ran_def)

consts Map__range__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> 'b set"
defs Map__range__stp_def: 
  "Map__range__stp P__a m
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). P__a x \<and> m x = Some y)"

consts definedAt_m :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt'_m" 60)
defs definedAt_m_def: "(m definedAt_m (x::'a)) \<equiv> (x \<in> dom m)"

consts undefinedAt_m :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt'_m" 60)
defs undefinedAt_m_def: 
  "(m undefinedAt_m (x::'a)) \<equiv> (x \<notin> dom m)"

theorem Map__e_cl_gt__def: 
  "\<lbrakk>Some y = m1 x\<rbrakk> \<Longrightarrow> (m2 o_m m1) x = m2 y"
  by auto

theorem Map__e_cl_gt__def1: 
  "\<lbrakk>None = m1 x\<rbrakk> \<Longrightarrow> (m2 o_m m1) x = None"
  by auto

theorem Map__o__def: 
  "m1 o_m m2 = m1 o_m m2"
  by auto

consts Map__map :: "('b \<Rightarrow> 'c) \<Rightarrow>  ('a, 'b)map \<Rightarrow>  ('a, 'c)map"
defs Map__map_def: 
  "Map__map f m
     \<equiv> (\<lambda> (x::'a). case m x of Some y \<Rightarrow> Some (f y)
                             | None \<Rightarrow> None)"

consts e_at_m :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_m" 70)
defs e_at_m_def: 
  "((m:: ('a, 'b)map) @_m (x::'a)) \<equiv> (case m x of Some y \<Rightarrow> y)"

theorem Map__maps_p_Obligation_subtype: 
  "\<lbrakk>m definedAt_m x\<rbrakk> \<Longrightarrow> x \<in> dom m"
   by (auto simp: definedAt_m_def)

consts Map__maps_p :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
defs Map__maps_p_def: 
  "Map__maps_p m x y \<equiv> (m definedAt_m x \<and> m @_m x = y)"

consts Map__applys :: " ('a, 'b)map \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Map__applys_def: 
  "Map__applys m xS
     \<equiv> (\<lambda> (y::'b). \<exists>(x::'a). x \<in> xS \<and> Map__maps_p m x y)"

consts Map__applys__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> 'a set \<Rightarrow> 'b set"
defs Map__applys__stp_def: 
  "Map__applys__stp P__a m xS
     \<equiv> (\<lambda> (y::'b). 
          \<exists>(x::'a). P__a x \<and> (x \<in> xS \<and> Map__maps_p m x y))"

consts Map__applyi :: " ('a, 'b)map \<Rightarrow> 'b \<Rightarrow> 'a set"
defs Map__applyi_def: 
  "Map__applyi m y \<equiv> (\<lambda> (x::'a). Map__maps_p m x y)"

consts Map__applyis :: " ('a, 'b)map \<Rightarrow> 'b set \<Rightarrow> 'a set"
defs Map__applyis_def: 
  "Map__applyis m yS
     \<equiv> (\<lambda> (x::'a). \<exists>(y::'b). y \<in> yS \<and> Map__maps_p m x y)"

consts Map__applyis__stp :: "('b \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> 'b set \<Rightarrow> 'a set"
defs Map__applyis__stp_def: 
  "Map__applyis__stp P__b m yS
     \<equiv> (\<lambda> (x::'a). 
          \<exists>(y::'b). P__b y \<and> (y \<in> yS \<and> Map__maps_p m x y))"

theorem Map__e_lt_eq__def: 
  "(m1 \<subseteq>\<^sub>m (m2:: ('a, 'b)map)) 
     = (\<forall>(x::'a). x \<in> dom m1 \<longrightarrow> m1 x = m2 x)"
  by (auto simp: map_le_def)

consts Map__e_lt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__e_lt_eq__stp_def: 
  "Map__e_lt_eq__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          \<forall>(x::'a). 
            P__a x \<and> x \<in> dom m1 \<longrightarrow> m1 x = m2 x)"

consts e_lt_m :: " ('a, 'b)map \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"	(infixl "<'_m" 60)
defs e_lt_m_def: 
  "((m1:: ('a, 'b)map) <_m (m2:: ('a, 'b)map))
     \<equiv> (m1 \<subseteq>\<^sub>m m2 \<and> m1 \<noteq> m2)"

consts Map__e_lt__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__e_lt__stp_def: 
  "Map__e_lt__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          Map__e_lt_eq__stp P__a(m1, m2) \<and> m1 \<noteq> m2)"

consts Map__e_gt_eq :: " ('a, 'b)map \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"	(infixl ">=" 60)
defs Map__e_gt_eq_def: 
  "((m1:: ('a, 'b)map) >= (m2:: ('a, 'b)map)) \<equiv> (m2 \<subseteq>\<^sub>m m1)"

consts Map__e_gt_eq__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__e_gt_eq__stp_def: 
  "Map__e_gt_eq__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          Map__e_lt_eq__stp P__a(m2, m1))"

consts e_gt_m :: " ('a, 'b)map \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"	(infixl ">'_m" 60)
defs e_gt_m_def: 
  "((m1:: ('a, 'b)map) >_m (m2:: ('a, 'b)map)) \<equiv> (m2 <_m m1)"

consts Map__e_gt__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__e_gt__stp_def: 
  "Map__e_gt__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          Map__e_lt__stp P__a(m2, m1))"

theorem Map__empty__def: 
  "empty x = None"
  by auto

consts Map__empty_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__empty_p_def [simp]: "Map__empty_p m \<equiv> (m = empty)"

consts Map__empty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__empty_p__stp_def: 
  "Map__empty_p__stp P__a m \<equiv> (m = RFun P__a empty)"

consts Map__nonEmpty_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__nonEmpty_p_def: "Map__nonEmpty_p m \<equiv> (m \<noteq> empty)"

consts Map__nonEmpty_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__nonEmpty_p__stp_def: 
  "Map__nonEmpty_p__stp P__a m \<equiv> (m \<noteq> RFun P__a empty)"

consts Map__single :: "'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)map"
defs Map__single_def: 
  "Map__single x y \<equiv> (\<lambda> (z::'a). if z = x then Some y else None)"

consts Map__single_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__single_p_def: 
  "Map__single_p m \<equiv> Set__single_p (dom m)"

consts Map__single_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__single_p__stp_def: 
  "Map__single_p__stp P__a m
     \<equiv> Set__single_p__stp P__a (RSet P__a (dom m))"

consts Map__id :: "'a set \<Rightarrow>  ('a, 'a)map"
defs Map__id_def: 
  "Map__id dom_v
     \<equiv> (\<lambda> (x::'a). if x \<in> dom_v then Some x else None)"

theorem Map__e_lt_lt_lt__def: 
  "\<lbrakk>Some y = m2 x\<rbrakk> \<Longrightarrow> (m1 ++ m2) x = Some y"
  by (auto simp: map_add_def split: option.split)

theorem Map__e_lt_lt_lt__def1: 
  "\<lbrakk>None = m2 x\<rbrakk> \<Longrightarrow> (m1 ++ m2) x = m1 x"
  by (auto simp: map_add_def)

consts Map__update :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)map"
defs Map__update_def: 
  "Map__update m x y
     \<equiv> (\<lambda> (z::'a). if z = x then Some y else m z)"

theorem Map__restrictDomain__def: 
  "\<lbrakk>x \<in> xS\<rbrakk> \<Longrightarrow> (m |` xS) x = m x"
  by auto

theorem Map__restrictDomain__def1: 
  "\<lbrakk>\<not> (x \<in> xS)\<rbrakk> \<Longrightarrow> (m |` xS) x = None"
  by auto

consts Map__restrictRange :: " ('a, 'b)map \<Rightarrow> 'b set \<Rightarrow>  ('a, 'b)map"	(infixl "restrictRange" 65)
defs Map__restrictRange_def: 
  "(m restrictRange yS)
     \<equiv> (\<lambda> (x::'a). 
          if x \<in> dom m \<and> m @_m x \<in> yS then 
            m x
          else 
            None)"

consts e_dsh_dsh_m :: " ('a, 'b)map \<Rightarrow> 'a set \<Rightarrow>  ('a, 'b)map"	(infixl "--'_m" 65)
defs e_dsh_dsh_m_def: 
  "((m:: ('a, 'b)map) --_m (xS::'a set))
     \<equiv> (\<lambda> (x::'a). if x \<in> xS then None else m x)"

consts mless :: " ('a, 'b)map \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)map"	(infixl "mless" 65)
defs mless_def [simp]: 
  "((m:: ('a, 'b)map) mless x) \<equiv> (m --_m Set__single x)"

consts Map__injective_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__injective_p_def: 
  "Map__injective_p m
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          x1 \<in> dom m \<and> (x2 \<in> dom m \<and> m x1 = m x2) 
            \<longrightarrow> x1 = x2)"

consts Map__injective_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__injective_p__stp_def: 
  "Map__injective_p__stp P__a m
     \<equiv> (\<forall>(x1::'a) (x2::'a). 
          P__a x1 
            \<and> (P__a x2 
             \<and> (x1 \<in> dom m \<and> (x2 \<in> dom m \<and> m x1 = m x2))) 
            \<longrightarrow> x1 = x2)"

typedef  ('a,'b)Map__InjectiveMap = "{x::  ('a, 'b)map. Map__injective_p x}"
   by (rule_tac x="Map__update empty x y" in exI,
     simp add: mem_def Map__injective_p_def Map__update_def dom_if Collect_def)

theorem Map__InjectiveMap_injective [simp]: 
  "Map__injective_p (Rep_Map__InjectiveMap m)"
  by (case_tac "m",
      simp add: Abs_Map__InjectiveMap_inverse Map__InjectiveMap_def 
                Collect_def mem_def)

(******************************************************************************)
declare Rep_Map__InjectiveMap_inverse [simp add]
declare Abs_Map__InjectiveMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Rep_Map__InjectiveMap_simp [simp]:
  "\<lbrakk>Map__injective_p y\<rbrakk>
   \<Longrightarrow>  (Rep_Map__InjectiveMap x = y) = (x = Abs_Map__InjectiveMap y)"
apply (subst Abs_Map__InjectiveMap_inject [symmetric],
       simp add: Rep_Map__InjectiveMap,
       simp add: Map__InjectiveMap_def Collect_def mem_def,
       simp add: Rep_Map__InjectiveMap_inverse)
done
(******************************************************************************)

lemma Map__Map__applyi_simp:
  "Map__applyi m y  = {x. x \<in> dom m \<and> m x = Some y}"
  by (simp add: Map__applyi_def Map__maps_p_def definedAt_m_def 
                Map__domain__def e_at_m_def,
      auto simp add: mem_def split: option.split)

lemma Map__Map__applys_simp:
  "Map__applys m S  = {y. \<exists>x. x \<in> S \<and> m x = Some y}"
  apply (simp add: Map__applys_def Map__maps_p_def definedAt_m_def 
                Map__domain__def e_at_m_def,
      auto simp add: mem_def split: option.split, 
      rule exI, auto)
(******************************************************************************)
  done

theorem Map__inverse_Obligation_subtype: 
  "Map__injective_p
      (\<lambda> (y::'b). 
         let yS = Map__applyi (Rep_Map__InjectiveMap m) y in 
         if yS = {} then None else Some (the_elem yS))"
  apply (case_tac "m", 
         simp add: Map__InjectiveMap_def Collect_def mem_def,
         auto simp add: Map__injective_p_def Let_def split: split_if_asm)
  apply (simp add: Map__Map__applyi_simp)
  apply (rotate_tac -2, thin_tac ?P, thin_tac ?P, erule notE)
  apply (subgoal_tac "the_elem {x \<in> dom y. y x = Some x1} = x
                    \<and> the_elem {x \<in> dom y. y x = Some x2} = xa",
         clarsimp, thin_tac "?a = ?b", auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=x in spec, auto)
  apply (simp add: the_elem_def set_eq_iff, rule the_equality, auto)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  apply (rotate_tac -1, drule_tac x=xa in spec, auto)
  done

theorem Map__inverse_Obligation_subtype0: 
  "\<lbrakk>Map__applyi (Rep_Map__InjectiveMap m) y = yS; 
    \<not> (yS = {})\<rbrakk> \<Longrightarrow> 
   Set__single_p yS"
  apply (case_tac "m", 
         simp add: Map__InjectiveMap_def Collect_def mem_def,
         auto simp add: Map__injective_p_def Let_def split: split_if_asm)
  apply (rotate_tac -2, drule_tac x=x in spec, simp add: Map__Map__applyi_simp)
  apply (erule notE, auto simp add: set_eq_iff)
  apply (drule spec, drule spec, erule mp, simp add: Map__domain__def)
  done

consts Map__inverse :: " ('a, 'b)Map__InjectiveMap \<Rightarrow>  ('b, 'a)Map__InjectiveMap"
defs Map__inverse_def: 
  "Map__inverse m
     \<equiv> Abs_Map__InjectiveMap
          (\<lambda> (y::'b). 
             let yS = Map__applyi (Rep_Map__InjectiveMap m) y 
             in 
             if yS = {} then None else Some (the_elem yS))"

consts Map__inverse__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)Map__InjectiveMap \<Rightarrow> 
                              ('b, 'a)Map__InjectiveMap"
defs Map__inverse__stp_def: 
  "Map__inverse__stp P__a m
     \<equiv> Abs_Map__InjectiveMap
          (\<lambda> (y::'b). 
             let yS = RSet P__a
                         (Map__applyi (Rep_Map__InjectiveMap m) y) 
             in 
             if yS = RSet P__a {} then 
               None
             else 
               Some (Set__theMember__stp P__a yS))"

consts Map__totalOn_p :: "'a set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__totalOn_p_def: "Map__totalOn_p s r \<equiv> (dom r = s)"

consts Map__totalOn_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__totalOn_p__stp_def: 
  "Map__totalOn_p__stp P__a s r \<equiv> (RSet P__a (dom r) = s)"

consts Map__surjectiveOn_p :: "'b set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__surjectiveOn_p_def: 
  "Map__surjectiveOn_p s r \<equiv> (ran r = s)"

consts Map__surjectiveOn_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                    'b set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__surjectiveOn_p__stp_def: 
  "Map__surjectiveOn_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::'b set). 
            \<lambda> (r:: ('a, 'b)map). 
              RSet P__b (Map__range__stp P__a r) = s)"

consts Map__bijectiveOn_p :: "'a set \<Rightarrow> 'b set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__bijectiveOn_p_def: 
  "Map__bijectiveOn_p s s_cqt
     \<equiv> (Map__totalOn_p s 
          \<inter> (Map__surjectiveOn_p s_cqt \<inter> Map__injective_p))"

consts Map__bijectiveOn_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   'a set \<Rightarrow> 'b set \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__bijectiveOn_p__stp_def: 
  "Map__bijectiveOn_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (s::'a set). 
            \<lambda> (s_cqt::'b set). 
              Map__totalOn_p__stp P__a s 
                \<inter> (Map__surjectiveOn_p__stp(P__a, P__b) s_cqt 
                     \<inter> Map__injective_p__stp P__a))"

consts Map__finite_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__finite_p_def [simp]: 
  "Map__finite_p m \<equiv> finite (dom m)"

consts Map__finite_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__finite_p__stp_def: 
  "Map__finite_p__stp P__a m
     \<equiv> Set__finite_p__stp P__a (RSet P__a (dom m))"

consts Map__infinite_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__infinite_p_def: 
  "Map__infinite_p m \<equiv> Set__infinite_p (dom m)"

consts Map__infinite_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__infinite_p__stp_def: 
  "Map__infinite_p__stp P__a m
     \<equiv> Set__infinite_p__stp P__a (RSet P__a (dom m))"

consts Map__countable_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__countable_p_def: 
  "Map__countable_p m \<equiv> Set__countable_p (dom m)"

consts Map__countable_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__countable_p__stp_def: 
  "Map__countable_p__stp P__a m
     \<equiv> Set__countable_p__stp P__a (RSet P__a (dom m))"

consts Map__uncountable_p :: " ('a, 'b)map \<Rightarrow> bool"
defs Map__uncountable_p_def: 
  "Map__uncountable_p m \<equiv> Set__uncountable_p (dom m)"

consts Map__uncountable_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow>  ('a, 'b)map \<Rightarrow> bool"
defs Map__uncountable_p__stp_def: 
  "Map__uncountable_p__stp P__a m
     \<equiv> Set__uncountable_p__stp P__a (RSet P__a (dom m))"

typedef  ('a,'b)Map__FiniteMap = "{x::  ('a, 'b)map. Map__finite_p x}"
   by (rule_tac x="empty" in exI, simp add: mem_def Map__finite_p_def Collect_def)

theorem Map__FiniteMap_finite [simp]: 
  "Map__finite_p (Rep_Map__FiniteMap m)"
  by (case_tac "m",
      simp add: Abs_Map__FiniteMap_inverse Map__FiniteMap_def 
                Collect_def mem_def)

(******************************************************************************)
declare Rep_Map__FiniteMap_inverse [simp add]
declare Abs_Map__FiniteMap_inverse [simp add]
(******************************************************************************)

(* Here is a very specific form that I need *)

lemma Map__FiniteMap_has_finite_domain [simp]:
  "finite (dom (Rep_Map__FiniteMap m))"
  by (case_tac "m",
      simp add: Abs_Map__FiniteMap_inverse Map__FiniteMap_def 
                Collect_def mem_def)

lemma Rep_Map__FiniteMap_simp [simp]:
  "\<lbrakk>Map__finite_p y\<rbrakk> \<Longrightarrow>  (Rep_Map__FiniteMap x = y) = (x = Abs_Map__FiniteMap y)"
apply (subst Abs_Map__FiniteMap_inject [symmetric],
       simp add: Rep_Map__FiniteMap,
       simp add: Map__FiniteMap_def Collect_def mem_def,
       simp add: Rep_Map__FiniteMap_inverse)
(******************************************************************************)
  done

theorem Map__update_preserves_finite1 [simp]: 
  "finite (dom (Map__update m x y)) 
     = finite (dom m)"
  apply (auto simp add: Map__update_def mem_def dom_if)
  apply (erule rev_mp,
         rule_tac t="{z. z \<noteq> x}" and s="UNIV - {x}" in subst, 
         auto simp add: Diff_Int_distrib)
  done

theorem Map__update_preserves_finite: 
  "Map__finite_p (Map__update m x y) = Map__finite_p m"
  by auto

type_synonym  ('a,'b)Map__InfiniteMap = " ('a, 'b)map"

type_synonym  ('a,'b)Map__CountableMap = " ('a, 'b)map"

type_synonym  ('a,'b)Map__UncountableMap = " ('a, 'b)map"

theorem Map__fromAssocList_Obligation_subtype: 
  "\<lbrakk>(xs, (zz__0::'b list)) = List__unzip alist; 
    distinct xs; 
    List__unzip alist = (xs_1, (ys::'b list))\<rbrakk> \<Longrightarrow> 
   Map__finite_p
      (\<lambda> (x::'a). 
         if x mem xs_1 then 
           Some (ys ! List__positionOf(xs_1, x))
         else 
           None)"
  by (simp add: member_def dom_if)

theorem Map__fromAssocList_Obligation_subtype0: 
  "\<lbrakk>(xs, (zz__0::'b list)) = List__unzip alist; 
    distinct xs; 
    List__unzip alist = (xs_1, (ys::'b list)); 
    (x::'a) mem xs_1\<rbrakk> \<Longrightarrow> 
   distinct xs_1"
  by auto

theorem Map__fromAssocList_Obligation_subtype1: 
  "\<lbrakk>(xs, (zz__0::'b list)) = List__unzip alist; 
    distinct xs; 
    List__unzip alist = (xs_1, ys); 
    x mem xs_1\<rbrakk> \<Longrightarrow> 
   List__positionOf(xs_1, x) < length ys"
  apply (cut_tac d__x=alist in List__unzip_subtype_constr)  
  apply (auto simp add: Collect_def dom_if member_def 
         List__positionOf_def List__theElement_def)
  apply (rule the1I2,
         rule List__theElement_Obligation_the, 
         rule List__positionOf_Obligation_subtype,
         simp_all add: member_def List__positionsOf_subtype_constr)
  apply (simp add: List__positionsOf_def List__positionsSuchThat_def)
  apply (rotate_tac -1, erule rev_mp)
  apply (rule the1I2,
         cut_tac l=xs_1 and p="\<lambda>z. z=x" 
            in List__positionsSuchThat_Obligation_the, 
         simp, clarify)
  apply (drule spec, auto)

(******************************************************************************
*** Note the correct type of Map__fromAssocList__stp is
consts Map__fromAssocList__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   ('a \<times> 'b) list \<Rightarrow>  ('a, 'b)Map__FiniteMap"
******************************************************************************)
  done

consts Map__fromAssocList :: "('a \<times> 'b) list \<Rightarrow>  ('a, 'b)Map__FiniteMap"
defs Map__fromAssocList_def: 
  "Map__fromAssocList alist
     \<equiv> (let (xs, ys) = List__unzip alist in 
        Abs_Map__FiniteMap
           (\<lambda> (x::'a). 
              if x mem xs then 
                Some (ys ! List__positionOf(xs, x))
              else 
                None))"

consts Map__fromAssocList__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                                   ('a \<times> 'b) list \<Rightarrow>  ('a, 'b)Map__FiniteMap"
defs Map__fromAssocList__stp_def: 
  "Map__fromAssocList__stp P__a alist
     \<equiv> (let (xs, ys) = List__unzip alist in 
        Abs_Map__FiniteMap
           (\<lambda> (x::'a). 
              if List__in_p__stp P__a(x, xs) then 
                Some (ys ! List__positionOf(xs, x))
              else 
                None))"

consts Map__agree_p :: " ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__agree_p_def: 
  "Map__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          \<forall>(x::'a). 
            x \<in> dom m1 \<and> x \<in> dom m2 
              \<longrightarrow> m1 x = m2 x)"

consts Map__agree_p__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 
                              ('a, 'b)map \<times>  ('a, 'b)map \<Rightarrow> bool"
defs Map__agree_p__stp_def: 
  "Map__agree_p__stp P__a
     \<equiv> (\<lambda> ((m1:: ('a, 'b)map), (m2:: ('a, 'b)map)). 
          \<forall>(x::'a). 
            P__a x \<and> (x \<in> dom m1 \<and> x \<in> dom m2) 
              \<longrightarrow> m1 x = m2 x)"

consts e_fsl_bsl_m :: " ('a, 'b)map \<Rightarrow>  ('a, 'b)map \<Rightarrow>  ('a, 'b)map"	(infixr "'/\\'_m" 65)
defs e_fsl_bsl_m_def: 
  "(m1 /\\_m m2)
     \<equiv> (\<lambda> (x::'a). 
          if x \<in> dom m1 \<and> x \<in> dom m2 then 
            m1 x
          else 
            None)"

consts e_bsl_fsl_m :: " ('a, 'b)map \<Rightarrow>  ('a, 'b)map \<Rightarrow>  ('a, 'b)map"	(infixr "\\'/'_m" 64)
defs e_bsl_fsl_m_def: 
  "(m1 \\/_m m2)
     \<equiv> (\<lambda> (x::'a). 
          if x \<in> dom m1 then 
            m1 x
          else 
            if x \<in> dom m2 then m2 x else None)"

theorem Map__dom_update: 
  "dom (Map__update m x y) = (insert x (dom m))"
  apply(auto simp: add Map__update_def)
  done

theorem Map__at_update_same_Obligation_subtype: 
  "x \<in> dom (Map__update m x y)"
  apply (simp add: Map__dom_update)
  done

theorem Map__at_update_same: 
  "Map__update m x y @_m x = y"
  apply(simp add:Map__update_def e_at_m_def)
  done

theorem Map__at_update_diff_Obligation_subtype: 
  "\<lbrakk>(x2::'a) \<in> dom m; x1 \<noteq> x2\<rbrakk> \<Longrightarrow> 
   x2 \<in> dom (Map__update m x1 y)"
  apply (simp add: Map__dom_update)
  done

theorem Map__at_update_diff: 
  "\<lbrakk>(x2::'a) \<in> dom m; x1 \<noteq> x2\<rbrakk> \<Longrightarrow> 
   Map__update m x1 y @_m x2 = m @_m x2"
  apply(simp add:Map__update_def e_at_m_def)
  done

theorem Map__double_update [simp]: 
  "Map__update (Map__update m x y) x z 
     = Map__update m x z"
  by (rule ext, simp add: Map__update_def)



(******************************************************************************)
lemma finiteRange [simp]: 
  "finite  (\<lambda> (x::int). l \<le> x \<and> x \<le> u)"
  by (rule_tac t="\<lambda>x. l \<le> x \<and> x \<le> u" and  s="{l..u}" 
      in subst, simp_all,
      auto simp add: atLeastAtMost_def atLeast_def atMost_def mem_def)

lemma finiteRange2 [simp]: 
  "finite  (\<lambda>(x::int). l \<le>  x \<and>  x < u)"
  by (rule_tac t="\<lambda>(x::int). l \<le>  x \<and>  x < u" and  s="{l..u - 1}" 
      in subst, simp_all,
      auto simp add: atLeastAtMost_def atLeast_def atMost_def mem_def)

(******************************************************************************)

(******* ZIP ... move into the base libraries ********)

lemma List__unzip_zip_inv [simp]:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> List__unzip (zip l1 l2) = (l1,l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule_tac t="zip l1 l2"
              and s="(\<lambda>(x_1, x_2). zip x_1 x_2)(l1,l2)" in subst, simp)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, simp)
  apply (subst inv_on_f_f, simp_all add: bij_on_def mem_def)
done

lemma List__unzip_as_zip [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow>  l = (zip l1 l2)"
  apply (simp add: List__unzip_def del: List__equiLong_def)
  apply (rule_tac t="zip l1 l2" and s="split zip (l1,l2)" in subst, simp)
  apply (drule sym, erule ssubst)
  apply (cut_tac List__unzip_Obligation_subtype,
         simp only: TRUE_def Function__bijective_p__stp_univ)
  apply (subst Function__inverse__stp_simp, auto)
  apply (cut_tac y=l and f="split zip" and A="\<lambda>(x, y). x equiLong y" 
             and B=UNIV in surj_on_f_inv_on_f)
  apply (simp_all add: bij_on_def del: List__equiLong_def)
done

lemma List__unzip_zip_conv:
  "\<lbrakk>l1 equiLong l2\<rbrakk> \<Longrightarrow> (List__unzip l = (l1,l2)) = (l = (zip l1 l2))"
  by auto

lemma List__unzip_empty [simp]:
  "List__unzip [] = ([],[])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_singleton [simp]:
  "List__unzip [(x,y)] = ([x],[y])"
  by (simp add:  List__unzip_zip_conv)

lemma List__unzip_cons [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk> \<Longrightarrow> List__unzip ((x,y) # l) = (x#l1,y#l2)"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_append [simp]:
  "\<lbrakk>List__unzip l = (l1,l2); List__unzip l' = (l1',l2')\<rbrakk>
   \<Longrightarrow> List__unzip (l @ l') = (l1@l1', l2@l2')"
  by (cut_tac d__x=l in List__unzip_subtype_constr,
      cut_tac d__x="l'" in List__unzip_subtype_constr,
      simp add: List__unzip_zip_conv)

lemma List__unzip_snoc [simp]:
  "\<lbrakk>List__unzip l = (l1,l2)\<rbrakk>
   \<Longrightarrow> List__unzip (l @ [(x,y)]) = (l1@[x], l2@[y])"
  by simp

lemma List__unzip_double [simp]:
  "List__unzip [(x,y),(u,v)] = ([x,u],[y,v])"
  by simp

(******* Increasing ********)


lemma List__increasingNats_p_nil [simp]:
   "List__increasingNats_p []"
  by (simp add: List__increasingNats_p_def)

lemma List__increasingNats_p_snoc [simp]:
   "List__increasingNats_p (l @ [i]) = 
        (List__increasingNats_p l \<and> (\<forall>j \<in> set l. j < i))"
  by (auto simp add: List__increasingNats_p_def 
                     nth_append not_less set_conv_nth,
      induct_tac ia rule: strict_inc_induct, auto)

lemma List__increasingNats_p_singleton [simp]:
   "List__increasingNats_p [i]" 
  by (simp add: List__increasingNats_p_def)

lemma sorted_equals_nth_mono2:
  "sorted xs = (\<forall>j < length xs. \<forall>i < length xs - j. xs ! j \<le> xs ! (j+i))"
  apply (auto simp add: sorted_equals_nth_mono)
  apply (drule_tac x=i in spec, simp,
         drule_tac x="j-i" in spec, auto)
done

lemma  List__increasingNats_p_is_sorted [simp]:
  "\<lbrakk>List__increasingNats_p l\<rbrakk> \<Longrightarrow> sorted l"
  apply (auto simp add: List__increasingNats_p_def sorted_equals_nth_mono2)
  apply (rotate_tac -1, erule rev_mp, rule_tac n="i" in nat_induct, auto)
  apply (drule_tac x="j+n" in spec, auto simp only: int_1 [symmetric] zdiff_int)
done

(****** Positions *********)

lemma List__positionsSuchThat_distinct [simp]: 
  "distinct (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_subtype_constr)

lemma List__positionsSuchThat_increasing [simp]: 
  "List__increasingNats_p (List__positionsSuchThat(l, p))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_membership [simp]: 
  "i mem  List__positionsSuchThat(l, p) = (i < length l \<and> p (l ! i))"
  by (simp add: List__positionsSuchThat_def,
      rule the1I2, 
      simp_all add: List__positionsSuchThat_Obligation_the)

lemma List__positionsSuchThat_membership2 [simp]: 
  "i \<in> set (List__positionsSuchThat(l, p)) = (i < length l \<and> p (l ! i))"
  by simp

lemma List__positionsSuchThat_nil [simp]:
  "List__positionsSuchThat ([], p) = []"
  by (simp add: List__positionsSuchThat_def member_def,
      rule the_equality, auto)

lemma List__positionsSuchThat_snoc1 [simp]:
  "\<lbrakk>p x\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p) @ [length l]"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe, simp_all)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsSuchThat_snoc2 [simp]:
  "\<lbrakk>\<not> (p x)\<rbrakk> \<Longrightarrow> 
   List__positionsSuchThat (l@[x], p) = List__positionsSuchThat (l, p)"
  apply (subst List__positionsSuchThat_def, simp)
  apply (rule the_equality, simp add: member_def nth_append, safe)
  apply (simp add: List__positionsSuchThat_def)
  apply (rule the1I2, simp add: List__positionsSuchThat_Obligation_the)
  apply (rule sorted_distinct_set_unique, 
         auto simp add: set_eq_iff less_Suc_eq nth_append)
done

lemma List__positionsOf_nil [simp]:
  "List__positionsOf ([], x) = []"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc1 [simp]:
  "List__positionsOf (l@[x], x) = List__positionsOf (l, x) @ [length l]"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_snoc2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l @ [a], x) = List__positionsOf (l, x)"
  by (simp add: List__positionsOf_def)

lemma List__positionsOf_singleton [simp]:
  "List__positionsOf ([x], x) = [0]"
  by (rule_tac t="[x]" and s="[]@[x]" in subst, simp,
      simp only: List__positionsOf_snoc1, simp)

lemma List__positionsOf_not_found [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l, x) = []"
  by (induct l rule: rev_induct, simp_all)

lemma List__positionsOf_not_found_later [simp]:
  "\<lbrakk>\<forall>a\<in>set l'. a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf (l@l', x) =  List__positionsOf (l, x)"
  by (induct l' rule: rev_induct, 
      simp_all add: append_assoc [symmetric] del: append_assoc)

lemma List__positionsOf_last [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x], x) = [length l]"
  by simp

lemma List__positionsOf_only_one [simp]:
  "\<lbrakk>\<forall>a\<in>set l. a \<noteq> x; \<forall>a\<in>set l'. a \<noteq> x\<rbrakk>
   \<Longrightarrow> List__positionsOf (l@[x]@l', x) = [length l]"
  by (simp only: append_assoc [symmetric], simp del: append_assoc)

lemma List__positionsOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionsOf ([a,x], x) = [1]"
 by (rule_tac t="[a,x]" and s="[a]@[x]" in subst, simp,
     subst List__positionsOf_last, auto)

lemma List__theElement_singleton [simp]:
  "List__theElement [x] = x"
  by (simp add: List__theElement_def)

lemma List__positionOf_singleton [simp]:
  "List__positionOf ([x], x) = 0"
  by (simp add:  List__positionOf_def)

lemma List__positionOf_2 [simp]:
  "\<lbrakk>a \<noteq> x\<rbrakk> \<Longrightarrow> List__positionOf ([a,x], x) = 1"
  by (simp add:  List__positionOf_def)

(*********************************)

lemma Map__fromAssocList_empty [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [])  = Map.empty"
  by (simp add: Map__fromAssocList_def Map__FiniteMap_def dom_if)


lemma Map__fromAssocList_singleton [simp]:
  "Rep_Map__FiniteMap (Map__fromAssocList [(x,y)]) = Map__update empty x y "
  by (simp add: Map__fromAssocList_def Map__FiniteMap_def dom_if 
                Map__update_def ext)


lemma Map__singleton_element [simp]: 
  "Map__update Map.empty x y x = Some y"
  by (simp add: Map__update_def)





end