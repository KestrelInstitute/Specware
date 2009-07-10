theory Character
imports SW_Integer Char_nat
begin
theorem Char__chr_subtype_constr: 
  "Function__bijective_p__stp(\<lambda> (n::nat). n < 256, TRUE) char_of_nat"
   apply (auto simp add: bij_on_def inj_on_def surj_on_def mem_def Bex_def)
 apply (rule_tac s="nat_of_char (char_of_nat x)" in ssubst)
 apply (simp add: nat_of_char_of_nat,
        thin_tac  "char_of_nat x = char_of_nat y", simp add: nat_of_char_of_nat)
 apply (rule_tac x="nat_of_char y" in exI)
 apply (simp add: char_of_nat_of_char)
  done
theorem Char__ord_subtype_constr: 
  "Function__bijective_p__stp(TRUE, \<lambda> (n::nat). n < 256) nat_of_char"
   apply (auto simp add: bij_ON_def inj_on_def surj_on_def mem_def Bex_def)
 apply (rule_tac s="char_of_nat (nat_of_char x)" in ssubst)
 apply (simp add: char_of_nat_of_char,
        thin_tac  "nat_of_char x = nat_of_char y", simp add: char_of_nat_of_char)
 apply (rule_tac x="char_of_nat y" in exI)
 apply (simp add: nat_of_char_of_nat)
  done
theorem Char__ord_subtype_constr1: 
  "Fun_PR (\<lambda> (n::nat). n < 256) nat_of_char"
  by auto
theorem Char__ord__def: 
  "nat_of_char 
     = Function__inverse__stp (\<lambda> (n::nat). n < 256) char_of_nat"
   apply (cut_tac Char__chr_subtype_constr, simp add: Function__inverse__stp_simp )
 apply (rule ext)
 apply (rule inv_on_f_eq, auto simp add: bij_on_def mem_def char_of_nat_of_char)
  done

theorem Char_ord_inv:
"(i<256 \<longrightarrow> nat_of_char(char_of_nat i) = i)
 \<and> char_of_nat(nat_of_char c) = c"
  by (simp add: nat_of_char_of_nat char_of_nat_of_char)

consts Char__isUpperCase :: "char \<Rightarrow> bool"
defs Char__isUpperCase_def [simp]: 
  "Char__isUpperCase c
     \<equiv> (nat_of_char CHR ''A'' \<le> nat_of_char c 
          \<and> nat_of_char c \<le> nat_of_char CHR ''Z'')"
consts Char__isLowerCase :: "char \<Rightarrow> bool"
defs Char__isLowerCase_def [simp]: 
  "Char__isLowerCase c
     \<equiv> (nat_of_char CHR ''a'' \<le> nat_of_char c 
          \<and> nat_of_char c \<le> nat_of_char CHR ''z'')"
consts Char__isAlpha :: "char \<Rightarrow> bool"
defs Char__isAlpha_def [simp]: 
  "Char__isAlpha c \<equiv> (Char__isUpperCase c \<or> Char__isLowerCase c)"
consts Char__isNum :: "char \<Rightarrow> bool"
defs Char__isNum_def [simp]: 
  "Char__isNum c
     \<equiv> (nat_of_char CHR ''0'' \<le> nat_of_char c 
          \<and> nat_of_char c \<le> nat_of_char CHR ''9'')"
consts Char__isAlphaNum :: "char \<Rightarrow> bool"
defs Char__isAlphaNum_def [simp]: 
  "Char__isAlphaNum c \<equiv> (Char__isAlpha c \<or> Char__isNum c)"
consts Char__isAscii :: "char \<Rightarrow> bool"
defs Char__isAscii_def [simp]: 
  "Char__isAscii c \<equiv> (nat_of_char c < 128)"
theorem Char__toUpperCase_Obligation_subtype: 
  "\<lbrakk>Char__isLowerCase c\<rbrakk> \<Longrightarrow> 
   (int (nat_of_char c) - int (nat_of_char CHR ''a'')) 
     + int (nat_of_char CHR ''A'') 
     \<ge> 0"
  by auto
theorem Char__toUpperCase_Obligation_subtype0: 
  "\<lbrakk>Char__isLowerCase c\<rbrakk> \<Longrightarrow> 
   (int (nat_of_char c) - int (nat_of_char CHR ''a'')) 
     + int (nat_of_char CHR ''A'') 
     < 256"
  apply (simp add:nat_of_char_def)
  done
consts Char__toUpperCase :: "char \<Rightarrow> char"
defs Char__toUpperCase_def [simp]: 
  "Char__toUpperCase c
     \<equiv> (if Char__isLowerCase c then 
          char_of_nat
             (nat
                 ((int (nat_of_char c) - int (nat_of_char CHR ''a'')) 
                    + int (nat_of_char CHR ''A'')))
        else 
          c)"
theorem Char__toLowerCase_Obligation_subtype: 
  "\<lbrakk>Char__isUpperCase c\<rbrakk> \<Longrightarrow> 
   (int (nat_of_char c) - int (nat_of_char CHR ''A'')) 
     + int (nat_of_char CHR ''a'') 
     \<ge> 0"
   apply (simp add:nat_of_char_def)
  done
theorem Char__toLowerCase_Obligation_subtype0: 
  "\<lbrakk>Char__isUpperCase c\<rbrakk> \<Longrightarrow> 
   (int (nat_of_char c) - int (nat_of_char CHR ''A'')) 
     + int (nat_of_char CHR ''a'') 
     < 256"
   apply (simp add:nat_of_char_def)
  done
consts Char__toLowerCase :: "char \<Rightarrow> char"
defs Char__toLowerCase_def [simp]: 
  "Char__toLowerCase c
     \<equiv> (if Char__isUpperCase c then 
          char_of_nat
             (nat
                 ((int (nat_of_char c) - int (nat_of_char CHR ''A'')) 
                    + int (nat_of_char CHR ''a'')))
        else 
          c)"
consts Char__compare :: "char \<times> char \<Rightarrow> Compare__Comparison"
defs Char__compare_def: 
  "Char__compare
     \<equiv> (\<lambda> ((c1::char), (c2::char)). 
          Integer__compare
            (int (nat_of_char c1), int (nat_of_char c2)))"
end