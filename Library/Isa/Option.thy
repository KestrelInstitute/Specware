theory Option
imports Compare Function
begin
fun Option__Option_P :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool"
where
   "Option__Option_P P_a None = True"
 | "Option__Option_P P_a (Some x0) = (P_a::'a \<Rightarrow> bool) x0"
consts Option__some :: "'a \<Rightarrow> 'a option"
defs Option__some_def: "Option__some \<equiv> Some"
consts Option__none :: "'a option"
defs Option__none_def: "Option__none \<equiv> None"
consts Option__some_p :: "'a option \<Rightarrow> bool"
defs Option__some_p_def: "Option__some_p x \<equiv> (x \<noteq> None)"
consts Option__none_p :: "'a option \<Rightarrow> bool"
defs Option__none_p_def: "Option__none_p x \<equiv> (x = None)"
fun Option__compare :: "('a \<times> 'a \<Rightarrow> Compare__Comparison) \<Rightarrow> 
                        'a option \<times> 'a option \<Rightarrow> Compare__Comparison"
where
   "Option__compare comp_v(Some x,Some y) = comp_v(x,y)"
 | "Option__compare comp_v(None,Some zzz_3) = Less"
 | "Option__compare comp_v(Some zzz_4,None) = Greater"
 | "Option__compare comp_v(None,None) = Equal"
theorem Option__mapOption__def: 
  "option_map f None = None"
  by auto
theorem Option__mapOption__def1: 
  "option_map f (Some x) = Some (f x)"
  by auto
theorem Option__isoOption_Obligation_subsort: 
  "\<lbrakk>bij iso_elem\<rbrakk> \<Longrightarrow> bij (option_map iso_elem)"
   apply(simp add: bij_def, auto) 
   (** first subgoal **)
   apply(simp add: inj_on_def option_map_def, auto)
   apply (simp split: option.split_asm)
   (** second subgoal **)
   apply(simp add:surj_def option_map_def, auto)
   apply (induct_tac y)
   (** subgoal 2.1    **)
   apply (simp split: option.split)
   (** subgoal 2.2 needs some guidance   **)
   apply (drule_tac x = "a" in  spec, auto)
   apply (rule_tac x="Some x" in exI, auto)
  done
consts Option__isoOption :: " ('a,'b)Function__Bijection \<Rightarrow> 
                              ('a option,'b option)Function__Bijection"
defs Option__isoOption_def: 
  "Option__isoOption iso_elem \<equiv> option_map iso_elem"
theorem Option__isoOption_subtype_constr: 
  "\<lbrakk>bij dom_isoOption\<rbrakk> \<Longrightarrow> bij (Option__isoOption dom_isoOption)"
   apply(simp add: Option__isoOption_def  Option__isoOption_Obligation_subsort)
  done
end