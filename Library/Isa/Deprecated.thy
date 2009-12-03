theory Deprecated
imports String
begin
consts Function__wfo :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> bool"
consts Option__some :: "'a \<Rightarrow> 'a option"
defs Option__some_def: "Option__some \<equiv> Some"
consts Option__none :: "'a option"
defs Option__none_def: "Option__none \<equiv> None"
types Integer__NonZeroInteger = "Integer__Int0"
consts Nat__natural_p :: "int \<Rightarrow> bool"
defs Nat__natural_p_def: "Nat__natural_p (i::int) \<equiv> (i \<ge> 0)"
theorem Integer__e_tld__def: 
  "(\<lambda> (i::int). - i) = (\<lambda> (i::int). - i)"
  by auto
theorem Integer__rem__def: 
  "RFun (\<lambda> (ignore1, (x_2::Integer__Int0)). x_2 \<noteq> 0) (\<lambda> (x,y). x modT y) 
     = RFun (\<lambda> (ignore1, (x_2::Integer__Int0)). x_2 \<noteq> 0) (\<lambda> (x,y). x modT y)"
  by auto
theorem Integer__non_zero_divides_iff_zero_remainder: 
  "\<lbrakk>x \<noteq> 0\<rbrakk> \<Longrightarrow> x zdvd y = (y modT x = 0)"
  apply (simp add: divides_iff_modT_0)
  done
theorem List__nil__def: 
  "[] = []"
  by auto
theorem List__cons__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  by auto
theorem List__insert__def: 
  "(\<lambda> (x,y). x # y) = (\<lambda> (x,y). x # y)"
  by auto
theorem List__null__def: 
  "null = null"
  by auto
theorem List__hd__def: 
  "RFun List__nonEmpty_p hd = RFun List__nonEmpty_p hd"
  by auto
theorem List__tl__def: 
  "RFun List__nonEmpty_p tl = RFun List__nonEmpty_p tl"
  by auto
theorem List__concat__def: 
  "(\<lambda> (x,y). x @ y) = (\<lambda> (x,y). x @ y)"
  by auto
theorem List__nth__def: 
  "RFun (\<lambda> ((l::'a list), (i::nat)). i < length l) (\<lambda> (x,y). x ! y) 
     = RFun (\<lambda> ((l::'a list), (i::nat)). i < length l) (\<lambda> (x,y). x ! y)"
  by auto
consts List__nthTail :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__nthTail_def [simp]: 
  "List__nthTail \<equiv> (\<lambda> ((x_1::'a list), (x_2::nat)). drop x_2 x_1)"
consts List__member__stp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'a list \<Rightarrow> bool"
defs List__member__stp_def: 
  "List__member__stp P__a \<equiv> List__in_p__stp P__a"
theorem List__member__def: 
  "(\<lambda> (x,y). x mem y) = (\<lambda> (x,y). x mem y)"
  by auto
consts List__removeFirstElems :: "'a list \<times> nat \<Rightarrow> 'a list"
defs List__removeFirstElems_def [simp]: 
  "List__removeFirstElems
     \<equiv> (\<lambda> ((x_1::'a list), (x_2::nat)). drop x_2 x_1)"
consts List__sublist :: "'a list \<times> nat \<times> nat \<Rightarrow> 'a list"
defs List__sublist_def [simp]: "List__sublist \<equiv> List__subFromTo"
theorem List__exists__def: 
  "list_ex = list_ex"
  by auto
theorem List__all__def: 
  "list_all = list_all"
  by auto
fun List__rev2 :: "'a list \<times> 'a list \<Rightarrow> 'a list"
where
   "List__rev2([], r) = r"
 | "List__rev2(Cons hd_v tl_v, r) 
      = List__rev2(tl_v, Cons hd_v r)"
theorem List__rev__def: 
  "rev = rev"
  by auto
consts List__find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
defs List__find_def [simp]: "List__find \<equiv> List__findLeftmost"
consts List__firstUpTo :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a list) option"
defs List__firstUpTo_def [simp]: 
  "List__firstUpTo \<equiv> List__findLeftmostAndPreceding"
consts List__splitList :: "('a \<Rightarrow> bool) \<Rightarrow> 
                           'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) option"
defs List__splitList_def [simp]: "List__splitList \<equiv> List__splitAtLeftmost"
consts List__locationOf :: "'a list \<times> 'a list \<Rightarrow> (nat \<times> 'a list) option"
defs List__locationOf_def [simp]: 
  "List__locationOf \<equiv> List__leftmostPositionOfSublistAndFollowing"
fun List__app :: "('a \<Rightarrow> unit) \<Rightarrow> 'a list \<Rightarrow> unit"
where
   "List__app f [] = ()"
 | "List__app f (Cons hd_v tl_v) = List__app f tl_v"
end