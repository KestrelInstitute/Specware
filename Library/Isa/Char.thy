theory Char
imports SW_Integer
begin
consts Char__ord :: "char \<Rightarrow> nat"
axioms Char__ord_subtype_constr: 
  "int (Char__ord dom_ord) \<ge> 0 \<and> int (Char__ord dom_ord) < 256"
axioms Char__ord_is_isomorphism: 
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
axioms Char__chr_def: 
  "Char__chr = inv Char__ord"
axioms Char__isUpperCase_def: 
  "Char__isUpperCase c 
     = (int (Char__ord CHR ''A'') \<le> int (Char__ord c) 
          \<and> int (Char__ord c) \<le> int (Char__ord CHR ''Z''))"
axioms Char__isLowerCase_def: 
  "Char__isLowerCase c 
     = (int (Char__ord CHR ''a'') \<le> int (Char__ord c) 
          \<and> int (Char__ord c) \<le> int (Char__ord CHR ''z''))"
axioms Char__isAlpha_def: 
  "Char__isAlpha c = (Char__isUpperCase c \<or> Char__isLowerCase c)"
axioms Char__isNum_def: 
  "Char__isNum c 
     = (int (Char__ord CHR ''0'') \<le> int (Char__ord c) 
          \<and> int (Char__ord c) \<le> int (Char__ord CHR ''9''))"
axioms Char__isAlphaNum_def: 
  "Char__isAlphaNum c = (Char__isAlpha c \<or> Char__isNum c)"
axioms Char__isAscii_def: 
  "Char__isAscii c = (int (Char__ord c) < 128)"
axioms Char__toUpperCase_def: 
  "Char__toUpperCase c 
     = (if Char__isLowerCase c then 
          Char__chr (nat (int (Char__ord c) - int (Char__ord CHR ''a'') 
                            + int (Char__ord CHR ''A'')))
        else 
          c)"
axioms Char__toLowerCase_def: 
  "Char__toLowerCase c 
     = (if Char__isUpperCase c then 
          Char__chr (nat (int (Char__ord c) - int (Char__ord CHR ''A'') 
                            + int (Char__ord CHR ''a'')))
        else 
          c)"
defs Char__compare_def: 
  "Char__compare
     \<equiv> \<lambda> (c1,c2). Integer__compare(int (Char__ord c1),int (Char__ord c2))"
end