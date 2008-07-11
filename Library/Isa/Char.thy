theory Char
imports SW_Nat
begin
consts Char__chr :: "nat \<Rightarrow> char"
theorem Char__chr_subtype_constr: 
  "Functions__bijective_p__stp(\<lambda> (n::nat). n < 256,\<lambda> ignore. True) Char__chr"
    sorry
consts Char__ord :: "char \<Rightarrow> nat"
defs Char__ord_def: 
  "Char__ord \<equiv> Functions__inverse__stp (\<lambda> (n::nat). n < 256) Char__chr"
theorem Char__ord_subtype_constr: 
  "Functions__bijective_p__stp(\<lambda> ignore. True,\<lambda> (n::nat). n < 256) Char__ord"
    sorry
consts Char__isUpperCase :: "char \<Rightarrow> bool"
defs Char__isUpperCase_def [simp]: 
  "Char__isUpperCase c
     \<equiv> (Char__ord CHR ''A'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''Z'')"
consts Char__isLowerCase :: "char \<Rightarrow> bool"
defs Char__isLowerCase_def [simp]: 
  "Char__isLowerCase c
     \<equiv> (Char__ord CHR ''a'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''z'')"
consts Char__isAlpha :: "char \<Rightarrow> bool"
defs Char__isAlpha_def [simp]: 
  "Char__isAlpha c \<equiv> (Char__isUpperCase c \<or> Char__isLowerCase c)"
consts Char__isNum :: "char \<Rightarrow> bool"
defs Char__isNum_def [simp]: 
  "Char__isNum c
     \<equiv> (Char__ord CHR ''0'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''9'')"
consts Char__isAlphaNum :: "char \<Rightarrow> bool"
defs Char__isAlphaNum_def [simp]: 
  "Char__isAlphaNum c \<equiv> (Char__isAlpha c \<or> Char__isNum c)"
consts Char__isAscii :: "char \<Rightarrow> bool"
defs Char__isAscii_def [simp]: "Char__isAscii c \<equiv> (Char__ord c < 128)"
theorem Char__toUpperCase_Obligation_subsort: 
  "\<lbrakk>Char__isLowerCase c\<rbrakk> \<Longrightarrow> 
   (int (Char__ord c) - int (Char__ord CHR ''a'')) + int (Char__ord CHR ''A'') 
     \<ge> 0"
  apply(auto)
  done
theorem Char__toUpperCase_Obligation_subsort0: 
  "\<lbrakk>Char__isLowerCase c\<rbrakk> \<Longrightarrow> 
   (int (Char__ord c) - int (Char__ord CHR ''a'')) + int (Char__ord CHR ''A'') 
     < 256"
    sorry
consts Char__toUpperCase :: "char \<Rightarrow> char"
defs Char__toUpperCase_def [simp]: 
  "Char__toUpperCase c
     \<equiv> (if Char__isLowerCase c then 
          Char__chr (nat ((int (Char__ord c) - int (Char__ord CHR ''a'')) 
                            + int (Char__ord CHR ''A'')))
        else 
          c)"
theorem Char__toLowerCase_Obligation_subsort: 
  "\<lbrakk>Char__isUpperCase c\<rbrakk> \<Longrightarrow> 
   (int (Char__ord c) - int (Char__ord CHR ''A'')) + int (Char__ord CHR ''a'') 
     \<ge> 0"
    sorry
theorem Char__toLowerCase_Obligation_subsort0: 
  "\<lbrakk>Char__isUpperCase c\<rbrakk> \<Longrightarrow> 
   (int (Char__ord c) - int (Char__ord CHR ''A'')) + int (Char__ord CHR ''a'') 
     < 256"
    sorry
consts Char__toLowerCase :: "char \<Rightarrow> char"
defs Char__toLowerCase_def [simp]: 
  "Char__toLowerCase c
     \<equiv> (if Char__isUpperCase c then 
          Char__chr (nat ((int (Char__ord c) - int (Char__ord CHR ''A'')) 
                            + int (Char__ord CHR ''a'')))
        else 
          c)"
consts Char__compare :: "char \<times> char \<Rightarrow> Compare__Comparison"
recdef Char__compare "{}"
  "Char__compare(c1,c2)
     = Integer__compare(int (Char__ord c1),int (Char__ord c2))"
end