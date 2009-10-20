theory SW_Option
imports Compare Function
begin
fun Option__Option_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool"
where
   "Option__Option_P P_a None = True"
 | "Option__Option_P P_a (Some x0) = (P_a::'a \<Rightarrow> bool) x0"
consts Option__some_p :: "'a option \<Rightarrow> bool"
defs Option__some_p_def [simp]: "Option__some_p x \<equiv> (x \<noteq> None)"
consts Option__none_p :: "'a option \<Rightarrow> bool"
defs Option__none_p_def [simp]: "Option__none_p x \<equiv> (x = None)"
theorem Option__compare_Obligation_exhaustive: 
  "\<lbrakk>(pV1::'a option) = fst (D::'a option \<times> 'a option); 
    (pV2::'a option) = snd D\<rbrakk> \<Longrightarrow> 
   if case pV1 of Some _ \<Rightarrow> True
                | _ \<Rightarrow> False then 
     (case pV2 of Some _ \<Rightarrow> True
                | _ \<Rightarrow> False) 
       \<or> (case pV2 of None \<Rightarrow> True
                    | _ \<Rightarrow> False)
   else 
     (case pV1 of None \<Rightarrow> True
                | _ \<Rightarrow> False) 
       \<and> ((case pV2 of Some _ \<Rightarrow> True
                     | _ \<Rightarrow> False) 
            \<or> (case pV2 of None \<Rightarrow> True
                         | _ \<Rightarrow> False))"
  by (cases D, cases pV1, cases pV2, auto, cases pV2, auto)
fun Option__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                        'a option \<times> 'a option \<Rightarrow> Compare__Comparison"
where
   "Option__compare comp_v(Some x, Some y) 
      = comp_v(x, y)"
 | "Option__compare comp_v(None, Some zzz_3) = Less"
 | "Option__compare comp_v(Some zzz_4, None) = Greater"
 | "Option__compare comp_v(None, None) = Equal"
theorem Option__mapOption_subtype_constr: 
  "\<lbrakk>Fun_PR P__b f\<rbrakk> \<Longrightarrow> 
   Option__Option_P P__b (Option.map f xx)"
  by (cases xx, auto)
theorem Option__mapOption__def: 
  "Option.map f None = None"
  by auto
theorem Option__mapOption__def1: 
  "Option.map f (Some x) = Some (f x)"
  by auto
consts Option__isoOption :: " ('a, 'b)Function__Bijection \<Rightarrow> 
                              ('a option, 'b option)Function__Bijection"
defs Option__isoOption_def: 
  "Option__isoOption
     \<equiv> (\<lambda> (iso_elem:: ('a, 'b)Function__Bijection). Option.map iso_elem)"
theorem Option__isoOption_subtype_constr: 
  "\<lbrakk>bij iso_elem\<rbrakk> \<Longrightarrow> bij (Option__isoOption iso_elem)"
   apply(simp add: Option__isoOption_def bij_def, auto)
 (** first subgoal **)
 apply(simp add: inj_on_def Option.map_def, auto)
 apply (simp split: option.split_asm)
 (** second subgoal **)
 apply(simp add:surj_def Option.map_def, auto)
 apply (induct_tac y)
 (** subgoal 2.1    **)
 apply (simp split: option.split)
 (** subgoal 2.2 needs some guidance   **)
 apply (drule_tac x = "a" in  spec, auto)
 apply (rule_tac x="Some x" in exI, auto)
  done
theorem Option__isoOption_subtype_constr1: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) iso_elem; 
    Fun_P(P__a, P__b) iso_elem\<rbrakk> \<Longrightarrow> 
   Fun_P(Option__Option_P P__a, Option__Option_P P__b)
      (RFun (Option__Option_P P__a) (Option__isoOption iso_elem))"
  apply(simp add: Option__isoOption_def, auto)
  apply (rule_tac P="x = None" in case_split, auto)
  done
theorem Option__isoOption_subtype_constr2: 
  "\<lbrakk>Function__bijective_p__stp(P__a, P__b) iso_elem; 
    Fun_P(P__a, P__b) iso_elem\<rbrakk> \<Longrightarrow> 
   Function__bijective_p__stp
     (Option__Option_P P__a, Option__Option_P P__b)
      (Option__isoOption iso_elem)"
   apply(simp add: bij_ON_def Option__isoOption_def, auto) 
 (** first subgoal **)
 apply(simp add: inj_on_def Option.map_def, auto)
 apply (simp split: option.split_asm add: Option__Option_P.simps mem_def)
 (** second subgoal **)
 apply(simp add:surj_on_def Option.map_def, auto)
 apply (simp add: Option__Option_P.simps mem_def)
 apply (rule_tac P="y = None" in case_split, auto)
 (** subgoal 2.1    **)
 apply (rule_tac x="None" in bexI, simp, simp add: mem_def)
 (** subgoal 2.2 needs some guidance   **)
 apply (drule_tac x = "ya" in  bspec, auto simp add: mem_def)
 apply (rule_tac x="Some x" in bexI, auto  simp add: mem_def)
  done
end