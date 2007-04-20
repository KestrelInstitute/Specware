theory Char
imports SW_Integer
begin
consts Char__ord :: "char \<Rightarrow> nat"
axioms Char__ord_subtype_constr: 
  "Char__ord dom_ord < 256"
axioms Char__ord_is_isomorphism [simp]: 
  "bij Char__ord"
consts Char__chr :: "nat \<Rightarrow> char"
consts Char__isUpperCase :: "char \<Rightarrow> bool"
consts Char__isLowerCase :: "char \<Rightarrow> bool"
consts Char__isAlpha :: "char \<Rightarrow> bool"
consts Char__isNum :: "char \<Rightarrow> bool"
consts Char__isAlphaNum :: "char \<Rightarrow> bool"
consts Char__isAscii :: "char \<Rightarrow> bool"
consts Char__toUpperCase :: "char \<Rightarrow> char"
consts Char__toLowerCase :: "char \<Rightarrow> char"
consts Char__compare :: "char \<times> char \<Rightarrow> Compare__Comparison"
theorem Char__chr_def_Obligation_subsort: 
  "bij Char__ord"
  apply(auto)
  done
axioms Char__chr_def: 
  "Char__chr = inv Char__ord"
axioms Char__isUpperCase_def [simp]: 
  "Char__isUpperCase c 
     = (Char__ord CHR ''A'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''Z'')"
axioms Char__isLowerCase_def [simp]: 
  "Char__isLowerCase c 
     = (Char__ord CHR ''a'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''z'')"
axioms Char__isAlpha_def [simp]: 
  "Char__isAlpha c = (Char__isUpperCase c \<or> Char__isLowerCase c)"
axioms Char__isNum_def [simp]: 
  "Char__isNum c 
     = (Char__ord CHR ''0'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''9'')"
axioms Char__isAlphaNum_def [simp]: 
  "Char__isAlphaNum c = (Char__isAlpha c \<or> Char__isNum c)"
axioms Char__isAscii_def [simp]: 
  "Char__isAscii c = (Char__ord c < 128)"
theorem Char__toUpperCase_def_Obligation_subsort: 
  "\<lbrakk>Char__isLowerCase c\<rbrakk> \<Longrightarrow> 
   0 
     \<le> int (Char__ord c) - int (Char__ord CHR ''a'') 
             + int (Char__ord CHR ''A'')"
  apply(auto)
  done
axioms Char__toUpperCase_def [simp]: 
  "Char__toUpperCase c 
     = (if Char__isLowerCase c then 
          Char__chr (nat (int (Char__ord c) - int (Char__ord CHR ''a'') 
                            + int (Char__ord CHR ''A'')))
        else 
          c)"
theorem Char__toLowerCase_def_Obligation_subsort: 
  "\<lbrakk>Char__isUpperCase c\<rbrakk> \<Longrightarrow> 
   0 
     \<le> int (Char__ord c) - int (Char__ord CHR ''A'') 
             + int (Char__ord CHR ''a'')"
  apply(auto)
  done
axioms Char__toLowerCase_def [simp]: 
  "Char__toLowerCase c 
     = (if Char__isUpperCase c then 
          Char__chr (nat (int (Char__ord c) - int (Char__ord CHR ''A'') 
                            + int (Char__ord CHR ''a'')))
        else 
          c)"
recdef Char__compare "{}"
  "Char__compare(c1,c2)
     = Integer__compare(int (Char__ord c1),int (Char__ord c2))"
end