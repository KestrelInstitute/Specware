theory String
imports Character SW_List
begin
theorem String__implode_subtype_constr: 
  "bij id"
  by auto
theorem String__explode__def: 
  "id = inv id"
  by auto
theorem String__length__def: 
  "length s = length (id s)"
  by auto
theorem String__e_at_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length s; let ignore = id s in i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length (id s) \<and> i \<ge> 0"
  by auto
theorem String__e_at__def: 
  "\<lbrakk>i < length s\<rbrakk> \<Longrightarrow> s ! i = id s ! i"
  by auto
theorem String__subFromTo_Obligation_subtype: 
  "\<lbrakk>(i::nat) \<le> (j::nat); 
    j \<le> length s; 
    let ignore = id s in i \<ge> 0 \<and> j \<ge> 0\<rbrakk> \<Longrightarrow> 
   j \<le> length (id s) \<and> (i \<ge> 0 \<and> j \<ge> 0)"
  by auto
consts String__subFromTo :: "string \<times> nat \<times> nat \<Rightarrow> string"
defs String__subFromTo_def: 
  "String__subFromTo
     \<equiv> (\<lambda> ((s::string), (i::nat), (j::nat)). 
          id (List__subFromTo(id s, i, j)))"
theorem String__e_pls_pls__def: 
  "s1 @ s2 = id (id s1 @ id s2)"
  by auto
theorem String__forall_p__def: 
  "list_all p s = list_all p (id s)"
  by auto
theorem String__exists_p__def: 
  "list_ex p s = list_ex p (id s)"
  by auto
theorem String__map__def: 
  "map f s = id (map f (id s))"
  by auto
consts String__flatten :: "string list \<Rightarrow> string"
defs String__flatten_def: 
  "String__flatten ss \<equiv> id (concat (map id ss))"
consts String__translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
defs String__translate_def: 
  "String__translate subst s
     \<equiv> String__flatten (map subst (id s))"
consts String__compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
defs String__compare_def: 
  "String__compare
     \<equiv> (\<lambda> ((s1::string), (s2::string)). 
          List__compare Char__compare(id s1, id s2))"
consts e_lt_s :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<'_s" 60)
defs e_lt_s_def: 
  "(s1 <_s s2) \<equiv> (String__compare(s1, s2) = Less)"
consts e_lt_eq_s :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<='_s" 60)
defs e_lt_eq_s_def: 
  "((s1::string) <=_s (s2::string)) \<equiv> (s1 <_s s2 \<or> s1 = s2)"
consts e_gt_s :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">'_s" 60)
defs e_gt_s_def: "((s1::string) >_s (s2::string)) \<equiv> (s2 <_s s1)"
consts e_gt_eq_s :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">='_s" 60)
defs e_gt_eq_s_def: 
  "((s1::string) >=_s (s2::string)) \<equiv> (s2 <=_s s1)"
consts String__newline :: "string"
defs String__newline_def: "String__newline \<equiv> ''
''"
consts Boolean__show :: "bool \<Rightarrow> string"
defs Boolean__show_def: 
  "Boolean__show x \<equiv> (if x then ''true'' else ''false'')"
fun Nat__digitToString :: "nat \<Rightarrow> string"
where
   "Nat__digitToString 0 = ''0''"
 | "Nat__digitToString (Suc d) 
      = (if d + 1 = 1 then 
           ''1''
         else 
           if d + 1 = 2 then 
             ''2''
           else 
             if d + 1 = 3 then 
               ''3''
             else 
               if d + 1 = 4 then 
                 ''4''
               else 
                 if d + 1 = 5 then 
                   ''5''
                 else 
                   if d + 1 = 6 then 
                     ''6''
                   else 
                     if d + 1 = 7 then 
                       ''7''
                     else 
                       if d + 1 = 8 then 
                         ''8''
                       else 
                         if d + 1 = 9 then ''9'' else regular_val)"

lemma Nat__digitToString_singleton:
 "x<10 \<Longrightarrow> \<exists>(a::char). Nat__digitToString x = [a]"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString0 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''0'') = (x=0)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString1 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''1'') = (x=1)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString2 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''2'') = (x=2)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString3 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''3'') = (x=3)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString4 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''4'') = (x=4)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString5 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''5'') = (x=5)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString6 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''6'') = (x=6)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString7 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''7'') = (x=7)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString8 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''8'') = (x=8)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString9 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''9'') = (x=9)"
  by (induct x rule: Nat__digitToString.induct, auto)

lemma Nat__digitToString_of0 [simp]: "Nat__digitToString 0 = ''0''" by auto
lemma Nat__digitToString_of1 [simp]: "Nat__digitToString 1 = ''1''" by auto
lemma Nat__digitToString_of2 [simp]: "Nat__digitToString 2 = ''2''" by auto
lemma Nat__digitToString_of3 [simp]: "Nat__digitToString 3 = ''3''" by auto
lemma Nat__digitToString_of4 [simp]: "Nat__digitToString 4 = ''4''" by auto
lemma Nat__digitToString_of5 [simp]: "Nat__digitToString 5 = ''5''" by auto
lemma Nat__digitToString_of6 [simp]: "Nat__digitToString 6 = ''6''" by auto
lemma Nat__digitToString_of7 [simp]: "Nat__digitToString 7 = ''7''" by auto
lemma Nat__digitToString_of8 [simp]: "Nat__digitToString 8 = ''8''" by auto
lemma Nat__digitToString_of9 [simp]: "Nat__digitToString 9 = ''9''" by auto

lemma Nat__digitToString_not_empty [simp]: 
"x<10 \<Longrightarrow> (Nat__digitToString x = []) = False"
  by (cut_tac x=x in Nat__digitToString_singleton, auto)
lemma Nat__digitToString_not_sign [simp]: 
"x<10 \<Longrightarrow> (Nat__digitToString x = ''-'') = False"
  by (induct x rule: Nat__digitToString.induct, auto)

lemma Nat__digitToString_injective [simp]: 
"\<lbrakk>x<10; y<10; Nat__digitToString x = Nat__digitToString y\<rbrakk>
 \<Longrightarrow>  x = y"
  apply (subgoal_tac "x=0 \<or> x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or>
                      x=5 \<or> x=6 \<or> x=7 \<or> x=8 \<or> x=9",
         auto simp del: One_nat_def)
  apply (drule sym, simp)+
done

theorem Nat__natToString_Obligation_subtype: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> Nat__posNat_p 10"
  by auto
theorem Nat__natToString_Obligation_subtype0: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> Nat__posNat_p 10"
  by auto
theorem Nat__natToString_Obligation_subtype1: 
  "\<lbrakk>\<not> ((x::nat) < 10); x mod 10 \<ge> 0\<rbrakk> \<Longrightarrow> x mod 10 < 10"
  by auto
consts Nat__natToString :: "nat \<Rightarrow> string"
recdef Nat__natToString "measure size"
  "Nat__natToString x
     = (if x < 10 then 
          Nat__digitToString x
        else 
          Nat__natToString (x div 10) 
            @ Nat__digitToString (x mod 10))"


lemma Nat__natToString_small [simp]: 
"\<lbrakk>x < 10\<rbrakk>
 \<Longrightarrow> Nat__natToString x = Nat__digitToString x"
  by simp

lemma Nat__natToString_large:
"\<lbrakk>10 \<le> x\<rbrakk> \<Longrightarrow>
 Nat__natToString x =
 Nat__natToString (x div 10) @ Nat__digitToString (x mod 10)"
  by simp
  
lemma Nat__natToString_not_empty [simp]: "(Nat__natToString x = []) = False"
  by simp 

lemmas [simp del] = Nat__natToString.simps (* avoid loops in the simplifier *)

lemma Nat__natToString_no_sign [simp]:
"(Nat__natToString x = (CHR ''-'' # s)) = False"
  apply (cut_tac f="\<lambda>x. x div 10" 
             and P="\<lambda>x. \<forall>s.
                       (Nat__natToString x = CHR ''-'' # s) = False" 
             and a="x" in measure_induct, auto)
  apply (subgoal_tac "x<10 \<or> 10\<le>x", erule disjE, auto)
  apply (cut_tac x="x" in Nat__digitToString_singleton, simp, simp)
  apply (simp add: Nat__natToString_large)
  apply (drule_tac x="x div 10" in spec, drule mp, simp,
         simp add: append_eq_Cons_conv)
done

lemma Nat__natToString_no_sign2 [simp]:
"((CHR ''-'' # s) = Nat__natToString x) = False"
  by (simp add: not_sym)

consts Nat__show :: "nat \<Rightarrow> string"
defs Nat__show_def: "Nat__show \<equiv> Nat__natToString"
consts Nat__natConvertible :: "string \<Rightarrow> bool"
defs Nat__natConvertible_def: 
  "Nat__natConvertible s \<equiv> (\<exists>(x::nat). Nat__natToString x = s)"
theorem Nat__stringToNat_Obligation_the: 
  "\<lbrakk>Nat__natConvertible s\<rbrakk> \<Longrightarrow> \<exists>!(x::nat). Nat__natToString x = s"
  apply (simp add: Nat__natConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp) 
  apply (cut_tac xs=s and
                 P ="\<lambda>s. \<forall>z y.
                     (Nat__natToString z = s \<and> Nat__natToString y = s)
                     -->  (y = z)" 
         in rev_induct, auto,
         thin_tac "Nat__natToString xa = Nat__natToString x")
  apply (drule_tac x="z div 10" in spec, drule_tac x="y div 10" in spec)
  apply (cut_tac x=z in  Nat__natToString.simps, 
         cut_tac x=y in  Nat__natToString.simps, 
         simp split: split_if_asm, simp_all add: not_less)
  apply (cut_tac x="y mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="z" in Nat__digitToString_singleton, simp,
         erule exE, erule exE, simp)
  apply (cut_tac x="z mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="y" in Nat__digitToString_singleton, simp,
         erule exE, erule exE, simp)
  apply (cut_tac x="z mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="y mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         erule exE, erule exE, simp)
  apply (thin_tac "Nat__natToString z = xs @ [xb]", thin_tac "10 \<le> z",
         thin_tac "Nat__natToString y = xs @ [xb]", thin_tac "10 \<le> y",
         thin_tac "aa = xb",
         thin_tac "Nat__natToString (z div 10) = xs \<and> a = xb")
  apply (subgoal_tac "(y mod 10) = (z mod 10)", auto) 
  apply (rule_tac s="10 * (y div 10) + (y mod 10)" in ssubst)
  apply (rule_tac s="10 * (z div 10) + (z mod 10)" in ssubst)
  apply (simp, rule sym, rule mod_div_equality2, rule sym,
         rule mod_div_equality2)
  (*** there should be an easier way ***)
  done
consts Nat__stringToNat :: "string \<Rightarrow> nat"
defs Nat__stringToNat_def: 
  "Nat__stringToNat s \<equiv> (THE (x::nat). Nat__natToString x = s)"
theorem Integer__intToString_Obligation_subtype: 
  "\<lbrakk>\<not> ((x::int) \<ge> 0)\<rbrakk> \<Longrightarrow> - x \<ge> 0"
  by auto
consts Integer__intToString :: "int \<Rightarrow> string"
defs Integer__intToString_def: 
  "Integer__intToString x
     \<equiv> (if x \<ge> 0 then 
          Nat__natToString (nat x)
        else 
          ''-'' @ Nat__natToString (nat (- x)))"
consts Integer__show :: "int \<Rightarrow> string"
defs Integer__show_def: "Integer__show \<equiv> Integer__intToString"
consts Integer__intConvertible :: "string \<Rightarrow> bool"
defs Integer__intConvertible_def: 
  "Integer__intConvertible s
     \<equiv> (\<exists>(x::int). Integer__intToString x = s)"
theorem Integer__stringToInt_Obligation_the: 
  "\<lbrakk>Integer__intConvertible s\<rbrakk> \<Longrightarrow> 
   \<exists>!(x::int). Integer__intToString x = s"
  apply (simp add:Integer__intConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp)
  apply (simp add: Integer__intToString_def split: split_if_asm)
  apply (cut_tac s = "s" in Nat__stringToNat_Obligation_the)
  apply (simp add: Nat__natConvertible_def, rule_tac x="nat x" in exI, simp)
  apply (erule ex1E, frule_tac x="nat x" in spec, drule_tac x="nat xa" in spec,
         auto)
  apply (cut_tac s = "Nat__natToString (nat (- x))"
         in Nat__stringToNat_Obligation_the)
  apply (simp add: Nat__natConvertible_def, rule_tac x="nat (-x)" in exI, simp)
  apply (erule ex1E, frule_tac x="nat (-x)" in spec,
         drule_tac x="nat (-xa)" in spec)
  apply (drule mp, simp, drule mp, clarify, 
         thin_tac "Nat__natToString xb = Nat__natToString (nat (- x))",
         thin_tac "Nat__natToString (nat (- xa)) =
                   Nat__natToString (nat (- x))",
         auto)
  done
consts Integer__stringToInt :: "string \<Rightarrow> int"
defs Integer__stringToInt_def: 
  "Integer__stringToInt s \<equiv> (THE (x::int). Integer__intToString x = s)"
consts Char__show :: "char \<Rightarrow> string"
defs Char__show_def: "Char__show c \<equiv> id ([c])"
fun Compare__show :: "Compare__Comparison \<Rightarrow> string"
where
   "Compare__show Greater = ''Greater''"
 | "Compare__show Equal = ''Equal''"
 | "Compare__show Less = ''Less''"
fun Option__show :: "('a \<Rightarrow> string) \<Rightarrow> 'a option \<Rightarrow> string"
where
   "Option__show shw None = ''None''"
 | "Option__show shw (Some x) = (''(Some '' @ shw x) @ '')''"
fun List__show :: "string \<Rightarrow> string list \<Rightarrow> string"
where
   "List__show sep [] = ''''"
 | "List__show sep ([hd_v]) = hd_v"
 | "List__show sep (Cons hd_v tl_v) 
      = (hd_v @ sep) @ List__show sep tl_v"
theorem String__sub__def: 
  "RFun (\<lambda> ((s::string), (n::nat)). n < length s) (\<lambda> (x,y). x ! y) 
     = RFun (\<lambda> ((s::string), (n::nat)). n < length s) (\<lambda> (x,y). x ! y)"
  by auto
consts String__substring :: "string \<times> nat \<times> nat \<Rightarrow> string"
defs String__substring_def: "String__substring \<equiv> String__subFromTo"
theorem String__concat__def: 
  "(\<lambda> (x,y). x @ y) = (\<lambda> (x,y). x @ y)"
  by auto
theorem String__e_crt__def: 
  "(\<lambda> (x,y). x @ y) = (\<lambda> (x,y). x @ y)"
  by auto
theorem String__all__def: 
  "list_all = list_all"
  by auto
theorem String__exists__def: 
  "list_ex = list_ex"
  by auto
theorem String__concatList__def: 
  "concat = String__flatten"
   apply (rule ext, simp add: String__flatten_def id_def)
  done
consts String__toScreen :: "string \<Rightarrow> unit"
defs String__toScreen_def: "String__toScreen s \<equiv> ()"
consts String__writeLine :: "string \<Rightarrow> unit"
defs String__writeLine_def: "String__writeLine s \<equiv> ()"
consts String__lt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "lt" 60)
defs String__lt_def: "(s1 lt s2) \<equiv> (s1 <_s s2)"
consts String__leq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "leq" 60)
defs String__leq_def: "(s1 leq s2) \<equiv> (s1 <=_s s2)"
consts Boolean__toString :: "bool \<Rightarrow> string"
defs Boolean__toString_def: "Boolean__toString \<equiv> Boolean__show"
consts Nat__toString :: "nat \<Rightarrow> string"
defs Nat__toString_def: "Nat__toString \<equiv> Nat__show"
consts Integer__toString :: "int \<Rightarrow> string"
defs Integer__toString_def: "Integer__toString \<equiv> Integer__show"
consts Char__toString :: "char \<Rightarrow> string"
defs Char__toString_def: "Char__toString \<equiv> Char__show"
end