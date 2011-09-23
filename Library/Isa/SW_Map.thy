theory SW_Map
imports SW_Relation
begin

(****************************************************************************
* Isabelle defines the type of maps as functions from 'a to 'b Option
* The following theorem establishes the conversion between specware maps
* and Isabelle maps
****************************************************************************)

consts MapAC__toIsaMap :: "('a, 'b)Relation__Map \<Rightarrow> ('a \<rightharpoonup> 'b)"
       MapAC__fromIsaMap :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b)Relation__Map "
defs
   MapAC__toIsaMap_def:
   "MapAC__toIsaMap m
    \<equiv> (\<lambda>(a::'a). if a \<in> Domain m 
                                   then Some (the_elem (Relation__apply m a)) 
                                   else None)"
   MapAC__fromIsaMap_def:
   "MapAC__fromIsaMap m
    \<equiv> {(a,b). m a = Some b}"

lemma Relation__functional_p_alt_def:
    "Relation__functional_p m = (\<forall>x \<in> Domain m. \<exists>!y. (x, y) \<in> m)" 
 apply (simp add: Relation__functional_p_def Relation__apply_def,
        auto simp add: mem_def)
 apply(drule_tac x=x in spec, safe)
 apply (simp add:set_eq_iff, 
        frule_tac x=ya in spec,drule_tac x=yb in spec,simp add: mem_def)
 apply (thin_tac "?P", simp only:set_eq_iff mem_def, simp)
 apply (drule_tac x=x in bspec)
 apply (simp add: Domain_def, auto simp add: mem_def)
 apply (drule_tac x=xa in spec, auto simp add: mem_def)
done

lemma Relation__functional_p_unfold:
    "Relation__functional_p m = (\<forall>x. (\<exists>y. {z. (x,z)\<in>m} = {y}) \<or>  {z. (x,z)\<in>m} ={})"
 apply (auto simp add: Relation__functional_p_alt_def)
 apply (drule_tac x=x in bspec, simp add: Domain_def, auto simp add: mem_def)
 apply (drule_tac x=x in spec, safe)
 apply (simp add:set_eq_iff, drule_tac x=ya in spec, simp add: mem_def)
done

lemma Relation__finite_if_finite_domain: 
  "\<lbrakk>Relation__functional_p m; finite (Domain m)\<rbrakk>  \<Longrightarrow> finite m"
  apply (rule_tac B="(\<lambda>x. (x, THE y. (x,y)\<in>m)) ` (Domain m)" in finite_subset)
  apply (thin_tac "finite ?m", auto simp add: image_def Bex_def Domain_def)
  apply (rule exI, auto)
  apply (rule the1I2, auto simp add: Relation__functional_p_alt_def)
done

lemma MapAC_unique:
  "\<lbrakk>Relation__functional_p m; a \<in> Domain m\<rbrakk>  
   \<Longrightarrow> Set__single_p (Relation__apply m a)"
 apply (simp add: Relation__functional_p_def)
 apply (drule_tac x=a in spec, simp add: Domain_def, clarify)
 apply (auto simp add: mem_def Relation__apply_def)
done


lemma MapAC__toIsaMap_bij:
  "bij_on MapAC__toIsaMap Relation__functional_p UNIV"
  apply (simp add: bij_on_def inj_on_def surj_on_def Ball_def Bex_def mem_def)
  apply (auto simp add:  MapAC__toIsaMap_def)
  apply (auto simp add:fun_eq_iff)
  apply (drule_tac x=a in spec, simp add: Relation__apply_def split: split_if_asm)
  apply (drule_tac a=a and m=x in MapAC_unique, simp,
         drule_tac a=a and m=xa in MapAC_unique, simp, 
         simp add: Relation__apply_def, auto)
  apply (drule sym, simp add:set_eq_iff,
         drule_tac x=b in spec, simp add: mem_def)
  apply (drule_tac x=a in spec, simp add: Relation__apply_def split: split_if_asm)
  apply (drule_tac a=a and m=x in MapAC_unique, simp,
         drule_tac a=a and m=xa in MapAC_unique, simp, 
         simp add: Relation__apply_def, auto)
  apply (drule sym, simp add:set_eq_iff,
         drule_tac x=b in spec, simp add: mem_def)
  apply (rule_tac x="MapAC__fromIsaMap x" in exI, 
         auto simp add: MapAC__fromIsaMap_def)
  apply (auto simp add: Relation__functional_p_def Relation__apply_def)
  apply (auto simp add: mem_def ex_in_conv [symmetric])
  apply (rule_tac t="the_elem (op = b)" and s="the_elem {x. x=b}" in subst)
  apply (rule_tac f="the_elem" in arg_cong)
  apply (simp only:set_eq_iff mem_def, auto)
done


lemma MapAC__fromIsa_inv_toIsa:
  "MapAC__fromIsaMap = inv_on Relation__functional_p MapAC__toIsaMap"
  apply (rule ext, rule sym,  simp add: inv_on_def inv_into_def mem_def)
  apply (rule some1_equality, simp add: inv_on_unique  MapAC__toIsaMap_bij)
  apply (auto simp add: MapAC__fromIsaMap_def MapAC__toIsaMap_def
                        Relation__functional_p_alt_def)
  apply (auto simp add:fun_eq_iff Relation__apply_def)
  apply (rule_tac t="the_elem (op = b)" and s="the_elem {x. x=b}" in subst)
  apply (rule_tac f="the_elem" in arg_cong)
  apply (simp only:set_eq_iff mem_def, auto)
done
  

notation
   MapAC__toIsaMap ("_\<triangleright>" [1000] 999) 

notation
   MapAC__fromIsaMap ("\<triangleleft>_" [1000] 999) 

(******************************************************************************)

consts MapAC__definedAt :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "definedAt" 60)
defs MapAC__definedAt_def [simp]: 
  "(m definedAt x) \<equiv> (x \<in> Domain m)"
consts MapAC__definedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                  ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> bool"
defs MapAC__definedAt__stp_def: 
  "MapAC__definedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          x \<in> Relation__domain__stp P__b m)"
consts MapAC__undefinedAt :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> bool"	(infixl "undefinedAt" 60)
defs MapAC__undefinedAt_def [simp]: 
  "(m undefinedAt x) \<equiv> (x \<notin> Domain m)"
consts MapAC__undefinedAt__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                    ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> bool"
defs MapAC__undefinedAt__stp_def: 
  "MapAC__undefinedAt__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          x \<notin> Relation__domain__stp P__b m)"
theorem MapAC__e_at_Obligation_the: 
  "\<lbrakk>Relation__functional_p m; m definedAt x\<rbrakk> \<Longrightarrow> 
   \<exists>!(y::'b). (x, y) \<in> m"
   apply (drule MapAC_unique, simp, simp)
 apply (simp add: unique_singleton Relation__apply_def)
  done
consts e_at_m :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b"	(infixl "@'_m" 70)
defs e_at_m_def: 
  "((m:: ('a, 'b)Relation__Map) @_m (x::'a)) \<equiv> (THE (y::'b). (x, y) \<in> m)"
consts MapAC__e_at__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                             ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> 'b"
defs MapAC__e_at__stp_def: 
  "MapAC__e_at__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          (THE (y::'b). P__b y \<and> (x, y) \<in> m))"
consts e_at_at_m :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b option"	(infixl "@@'_m" 70)
defs e_at_at_m_def: 
  "(m @@_m x) \<equiv> (if m definedAt x then Some (m @_m x) else None)"
consts MapAC__e_at_at__stp :: "('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)Relation__Relation \<times> 'a \<Rightarrow> 'b option"
defs MapAC__e_at_at__stp_def: 
  "MapAC__e_at_at__stp P__b
     \<equiv> (\<lambda> ((m:: ('a, 'b)Relation__Relation), (x::'a)). 
          if MapAC__definedAt__stp P__b(m, x) then 
            Some (m @_m x)
          else 
            None)"


lemma MapAC__e_at__stp_Obligation_the: 
  "\<lbrakk>Relation__functional_p__stp(P__a, P__b) m; P__a (x::'a); 
    MapAC__definedAt__stp P__b(m, x)\<rbrakk> \<Longrightarrow> 
   \<exists>!(y::'b). (x, y) \<in> m"
 apply (simp add: Relation__functional_p__stp_def MapAC__definedAt__stp_def)
 apply (drule_tac x=x in spec, simp add: Relation__domain__stp_def)
 apply (auto simp add: mem_def Relation__apply_def Set__single_p__stp_def)
 apply (simp add:set_eq_iff)
 apply (frule_tac x=yb in spec, drule_tac x=ya in spec, simp add: mem_def)
done

lemma MapAC__e_at_m_eq:
 "\<lbrakk>Relation__functional_p m; (a,b) \<in> m\<rbrakk> 
   \<Longrightarrow> m @_m a = b"
 apply (simp add: e_at_m_def Relation__functional_p_alt_def)
 apply (drule_tac x=a in bspec, auto simp add: Domain_def)
done


lemma MapAC__e_at_m_element:
  "\<lbrakk>Relation__functional_p m; a \<in> Domain m\<rbrakk> \<Longrightarrow> (a, m @_m a) \<in> m"
 apply (simp add: e_at_m_def Relation__functional_p_alt_def)
 apply (rule the1I2, drule_tac x=a in bspec, simp_all)
done

lemma MapAC__e_at_m_eq2:
  "\<lbrakk>P a\<rbrakk> \<Longrightarrow> {(a, b). P a \<and> b = f a } @_m a = f a"
 by (simp add: e_at_m_def)


theorem MapAC__map_result_in_range: 
  "\<lbrakk>Relation__functional_p m; m definedAt x\<rbrakk> \<Longrightarrow> 
   m @_m x \<in> Range m"
   apply (simp add: e_at_m_def)
 apply (rule the1I2, rule MapAC__e_at_Obligation_the, auto)
  done
theorem MapAC__map_result_in_range__stp: 
  "\<lbrakk>Relation__functional_p__stp(P__a, P__b) m; 
    Set_P (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) m; 
    P__a x; 
    MapAC__definedAt__stp P__b(m, x)\<rbrakk> \<Longrightarrow> 
   m @_m x \<in> Relation__range__stp P__a m"
   apply (simp add: e_at_m_def)
 apply (rule the1I2, rule_tac P__a=P__a in MapAC__e_at__stp_Obligation_the)
 apply (auto simp add:mem_def  Relation__range__stp_def)
  done
theorem MapAC__e_lt_lt_lt_Obligation_the: 
  "\<lbrakk>Relation__functional_p m2; Relation__functional_p m1\<rbrakk> \<Longrightarrow> 
   \<exists>!(m:: ('a, 'b)Relation__Map). 
     Relation__functional_p m 
       \<and> (Domain m = Domain m1 \<union> Domain m2 
        \<and> (\<forall>(x::'a). 
             x \<in> Domain m 
               \<longrightarrow> m @_m x 
                     = (if m2 definedAt x then 
                          m2 @_m x
                        else 
                          m1 @_m x)))"
  apply (simp add: Relation__functional_p_alt_def)
  apply (rule_tac 
         a="{(a,b).  a \<in> Domain m1 \<union> Domain m2 
                  \<and> b = (if a \<in> Domain m2 then m2 @_m a else m1 @_m a)}"
         in ex1I, simp_all)
  apply (simp_all add:  Relation__functional_p_alt_def [symmetric])
  apply (auto simp add: MapAC__e_at_m_eq, auto)
  apply (subgoal_tac "x \<in> Domain m2 \<and> (x \<in> Domain m1 \<or> x \<in> Domain m2)",
         simp add: MapAC__e_at_m_eq2 MapAC__e_at_m_eq, simp add: DomainI)
  apply (subgoal_tac "x \<in> Domain m1 \<and> (x \<in> Domain m1 \<or> x \<in> Domain m2)",
         simp add: MapAC__e_at_m_eq2 MapAC__e_at_m_eq, simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq)
  apply (drule_tac x=a in spec, clarify, rotate_tac -1, drule mp,
         subgoal_tac "a \<in> Domain x", simp, erule DomainI,
         simp add: MapAC__e_at_m_eq)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, rotate_tac -1, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
  apply (drule_tac x=a in spec, clarify, drule mp, simp add: DomainI,
         simp add: MapAC__e_at_m_eq,
         rotate_tac -1, drule sym, simp, erule MapAC__e_at_m_element,
         simp add: DomainI)
  done
theorem MapAC__e_lt_lt_lt_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p m2; 
    Relation__functional_p m1; 
    Relation__functional_p m; 
    Domain m = Domain m1 \<union> Domain m2; 
    x \<in> Domain m\<rbrakk> \<Longrightarrow> 
   m definedAt x"
  by auto
theorem MapAC__e_lt_lt_lt_Obligation_subtype0: 
  "\<lbrakk>Relation__functional_p m2; 
    Relation__functional_p m1; 
    Relation__functional_p m; 
    Domain m = Domain m1 \<union> Domain m2; 
    x \<in> Domain m; 
    \<not> (m2 definedAt x)\<rbrakk> \<Longrightarrow> 
   m1 definedAt x"
  by auto
consts MapAC__e_lt_lt_lt :: " ('a, 'b)Relation__Map \<Rightarrow> 
                              ('a, 'b)Relation__Map \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "<<<" 65)
defs MapAC__e_lt_lt_lt_def: 
  "(m1 <<< m2)
     \<equiv> (THE (m:: ('a, 'b)Relation__Map). 
       Relation__functional_p m 
         \<and> (Domain m = Domain m1 \<union> Domain m2 
          \<and> (\<forall>(x::'a). 
               x \<in> Domain m 
                 \<longrightarrow> m @_m x 
                       = (if m2 definedAt x then 
                            m2 @_m x
                          else 
                            m1 @_m x))))"
consts MapAC__e_lt_lt_lt__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation
                                     \<times>  ('a, 'b)Relation__Relation \<Rightarrow> 
                                   ('a, 'b)Relation__Relation"
defs MapAC__e_lt_lt_lt__stp_def: 
  "MapAC__e_lt_lt_lt__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)Relation__Relation), 
             (m2:: ('a, 'b)Relation__Relation)). 
            (THE (m:: ('a, 'b)Relation__Relation). 
            (Relation__functional_p__stp(P__a, P__b) m 
               \<and> Set_P
                    (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) m) 
              \<and> (RSet P__a (Relation__domain__stp P__b m) 
                   = RSet P__a
                        (Relation__domain__stp P__b m1 
                           \<union> Relation__domain__stp P__b m2) 
               \<and> (\<forall>(x::'a). 
                    P__a x 
                      \<and> x \<in> Relation__domain__stp P__b m 
                      \<longrightarrow> m @_m x 
                            = (if MapAC__definedAt__stp P__b(m2, x) then 
                                 m2 @_m x
                               else 
                                 m1 @_m x)))))"
theorem MapAC__update_Obligation_subtype: 
  "Relation__functional_p (Set__single(x, y))"
  by (auto simp add: Relation__functional_p_unfold)
consts MapAC__update :: " ('a, 'b)Relation__Map \<Rightarrow> 
                         'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)Relation__Map"
defs MapAC__update_def: 
  "MapAC__update m x y \<equiv> (m <<< Set__single(x, y))"
consts MapAC__update__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                               ('a, 'b)Relation__Relation \<Rightarrow> 
                              'a \<Rightarrow> 'b \<Rightarrow>  ('a, 'b)Relation__Relation"
defs MapAC__update__stp_def: 
  "MapAC__update__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> (m:: ('a, 'b)Relation__Relation). 
            \<lambda> (x::'a). 
              \<lambda> (y::'b). 
                MapAC__e_lt_lt_lt__stp(P__a, P__b)
                  (m, 
                   RFun
                      (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2)
                      (Set__single(x, y))))"
theorem MapAC__e_dsh_dsh_Obligation_subtype: 
  "\<lbrakk>Relation__functional_p m\<rbrakk> \<Longrightarrow> 
   Relation__functional_p (m restrictDomain - xS)"
   apply (simp add: Relation__functional_p_unfold Relation__restrictDomain_def,
        simp add: mem_def, auto)
 apply (drule_tac x=x in spec, auto)
  done
consts e_dsh_dsh_m :: " ('a, 'b)Relation__Map \<Rightarrow> 
                       'a set \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "--'_m" 65)
defs e_dsh_dsh_m_def: "(m --_m xS) \<equiv> (m restrictDomain - xS)"
consts mless :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow>  ('a, 'b)Relation__Map"	(infixl "mless" 65)
defs mless_def [simp]: 
  "((m:: ('a, 'b)Relation__Map) mless x) \<equiv> (m --_m Set__single x)"
consts MapAC__agree_p :: " ('a, 'b)Relation__Map \<times>  ('a, 'b)Relation__Map \<Rightarrow> 
                          bool"
defs MapAC__agree_p_def: 
  "MapAC__agree_p
     \<equiv> (\<lambda> ((m1:: ('a, 'b)Relation__Map), (m2:: ('a, 'b)Relation__Map)). 
          Relation__functional_p (m1 \<union> m2))"
consts MapAC__agree_p__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                ('a, 'b)Relation__Relation
                                  \<times>  ('a, 'b)Relation__Relation \<Rightarrow> bool"
defs MapAC__agree_p__stp_def: 
  "MapAC__agree_p__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          \<lambda> ((m1:: ('a, 'b)Relation__Relation), 
             (m2:: ('a, 'b)Relation__Relation)). 
            Relation__functional_p__stp(P__a, P__b)
               (RFun
                   (\<lambda> ((x_1::'a), (x_2::'b)). P__a x_1 \<and> P__b x_2) (m1 \<union> m2)))"
type_synonym  ('a,'b)MapAC__TotalMap = " ('a, 'b)Relation__Map"
theorem MapAC__fromFunction_Obligation_subtype: 
  "Relation__total_p (\<lambda> ((x::'a), (y::'b)). y = (f::'a \<Rightarrow> 'b) x)"
  by (auto simp add: Relation__total_p_def mem_def)
theorem MapAC__fromFunction_Obligation_subtype0: 
  "Relation__functional_p
      (\<lambda> ((x::'a), (y::'b)). y = (f::'a \<Rightarrow> 'b) x)"
  by (auto simp add: Relation__functional_p_alt_def mem_def)
consts MapAC__fromFunction :: "('a \<Rightarrow> 'b) \<Rightarrow>  ('a, 'b)MapAC__TotalMap"
defs MapAC__fromFunction_def: 
  "MapAC__fromFunction f \<equiv> (\<lambda> ((x::'a), (y::'b)). y = f x)"
theorem MapAC__toFunction_Obligation_subtype: 
  "Function__bijective_p__stp
     (TRUE, Relation__total_p &&& Relation__functional_p) MapAC__fromFunction"
  apply (simp add: bij_ON_def inj_on_def surj_on_def Ball_def Bex_def mem_def)
  apply (auto simp add: MapAC__fromFunction_def)
  apply (auto simp add:fun_eq_iff)
  apply (rule_tac x="\<lambda>a. x @_m a" in exI, auto)
  apply (rule sym, erule MapAC__e_at_m_eq, simp add: mem_def)
  apply (drule_tac a=a in MapAC__e_at_m_element,
         simp_all add: Relation__total_p_def mem_def)
  done
consts MapAC__toFunction :: " ('a, 'b)MapAC__TotalMap \<Rightarrow> 'a \<Rightarrow> 'b"
defs MapAC__toFunction_def: 
  "MapAC__toFunction \<equiv> inv MapAC__fromFunction"
consts MapAC__toFunction__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                   ('a, 'b)Relation__Relation \<Rightarrow> 'a \<Rightarrow> 'b"
defs MapAC__toFunction__stp_def: 
  "MapAC__toFunction__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Function__inverse__stp (Fun_P(P__a, P__b)) MapAC__fromFunction)"
theorem MapAC__fromPartialFun_Obligation_subtype: 
  "Relation__functional_p
      (\<lambda> ((x::'a), (y::'b)). (f::'a \<Rightarrow> 'b option) x = Some y)"
  by (auto simp add: Relation__functional_p_alt_def mem_def)
consts MapAC__fromPartialFun :: "('a \<Rightarrow> 'b option) \<Rightarrow>  ('a, 'b)Relation__Map"
defs MapAC__fromPartialFun_def: 
  "MapAC__fromPartialFun f
     \<equiv> (\<lambda> ((x::'a), (y::'b)). f x = Some y)"
theorem MapAC__toPartialFun_Obligation_subtype: 
  "Function__bijective_p__stp(TRUE, Relation__functional_p)
      MapAC__fromPartialFun"
  apply (auto simp add: bij_ON_def inj_on_def surj_on_def Ball_def Bex_def mem_def
                        MapAC__fromPartialFun_def,
         simp add:fun_eq_iff, auto)
  apply (drule_tac x=xb in spec, case_tac "x xb = None \<and> xa xb = None", auto)
  apply (rule_tac x="MapAC__toIsaMap x" in exI, simp add: MapAC__toIsaMap_def)
  apply (simp add:fun_eq_iff Relation__apply_def, clarify, rule conjI, clarify)
  apply (rule_tac t="(\<lambda>y. (a, y) \<in> x)" and s="{y}" in subst,
         simp_all only: the_elem_eq)
  apply (simp add: Relation__functional_p_alt_def set_eq_iff mem_def Domain_def, auto)
  apply (simp add: Relation__functional_p_alt_def mem_def Domain_def, auto)
  apply (simp add: mem_def)
  apply (simp add: Domain_def, simp add: mem_def)
  done
consts MapAC__toPartialFun :: " ('a, 'b)Relation__Map \<Rightarrow> 'a \<Rightarrow> 'b option"
defs MapAC__toPartialFun_def: 
  "MapAC__toPartialFun \<equiv> inv MapAC__fromPartialFun"
consts MapAC__toPartialFun__stp :: "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<Rightarrow> 
                                     ('a, 'b)Relation__Relation \<Rightarrow> 
                                    'a \<Rightarrow> 'b option"
defs MapAC__toPartialFun__stp_def: 
  "MapAC__toPartialFun__stp
     \<equiv> (\<lambda> ((P__a::'a \<Rightarrow> bool), (P__b::'b \<Rightarrow> bool)). 
          Function__inverse__stp (Fun_P(P__a, Option__Option_P P__b))
             MapAC__fromPartialFun)"
type_synonym  ('a,'b)MapAC__SurjectiveMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__InjectiveMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__BijectiveMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__FiniteMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__InfiniteMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__CountableMap = " ('a, 'b)Relation__Map"
type_synonym  ('a,'b)MapAC__UncountableMap = " ('a, 'b)Relation__Map"
end