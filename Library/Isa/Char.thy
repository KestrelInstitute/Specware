theory Char
imports SW_Integer
begin
typedecl Char__Char
consts Char__ord :: "char \<Rightarrow> int"
axioms Char__ord_subtype_constr: 
  "Char__ord dom_ord \<ge> 0 \<and> Char__ord dom_ord < 256"
axioms Char__ord_is_isomorphism: "bij Char__ord"
consts Char__chr :: "int \<Rightarrow> char"
consts Char__isUpperCase :: "char \<Rightarrow> bool"
consts Char__isLowerCase :: "char \<Rightarrow> bool"
consts Char__isAlpha :: "char \<Rightarrow> bool"
consts Char__isNum :: "char \<Rightarrow> bool"
consts Char__isAlphaNum :: "char \<Rightarrow> bool"
consts Char__isAscii :: "char \<Rightarrow> bool"
consts Char__toUpperCase :: "char \<Rightarrow> char"
consts Char__toLowerCase :: "char \<Rightarrow> char"
consts Char__compare :: "char \<times> char \<Rightarrow> Compare__Comparison"
axioms Char__chr_def: "Char__chr = inv Char__ord"
axioms Char__isUpperCase_def: 
  "Char__isUpperCase c 
     = (Char__ord CHR ''A'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''Z'')"
axioms Char__isLowerCase_def: 
  "Char__isLowerCase c 
     = (Char__ord CHR ''a'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''z'')"
axioms Char__isAlpha_def: 
  "Char__isAlpha c = (Char__isUpperCase c \<or> Char__isLowerCase c)"
axioms Char__isNum_def: 
  "Char__isNum c 
     = (Char__ord CHR ''0'' \<le> Char__ord c 
          \<and> Char__ord c \<le> Char__ord CHR ''9'')"
axioms Char__isAlphaNum_def: 
  "Char__isAlphaNum c = (Char__isAlpha c \<or> Char__isNum c)"
axioms Char__isAscii_def: "Char__isAscii c = (Char__ord c < 128)"
axioms Char__toUpperCase_def: 
  "Char__toUpperCase c 
     = (if Char__isLowerCase c then 
          Char__chr (Char__ord c - Char__ord CHR ''a'' + Char__ord CHR ''A'')
        else 
          c)"
axioms Char__toLowerCase_def: 
  "Char__toLowerCase c 
     = (if Char__isUpperCase c then 
          Char__chr (Char__ord c - Char__ord CHR ''A'' + Char__ord CHR ''a'')
        else 
          c)"
defs Char__compare_def: 
  "Char__compare \<equiv> \<lambda> (c1,c2). Integer__compare(Char__ord c1,Char__ord c2)"
end