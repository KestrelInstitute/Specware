theory String
imports Char SW_List
begin
axioms implode_subtype_constr: 
  "bij id"
theorem sub_Obligation_subsort: 
  "\<lbrakk>(n::nat) < length s; n < length s\<rbrakk> \<Longrightarrow> n < length (id s)"
  apply(auto)
  done
consts substring :: "string \<times> nat \<times> nat \<Rightarrow> string"
theorem substring_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> (j::nat); 
    j \<le> length s; 
    i \<le> j; 
    j \<le> length s\<rbrakk> \<Longrightarrow> i \<le> j \<and> j \<le> length (id s)"
  apply(auto)
  done
recdef substring "{}"
  "substring(s,i,j) = id (List__sublist(id s,i,j))"
consts translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
defs translate_def: "translate subst s \<equiv> concat (map subst (id s))"
consts compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
recdef compare "{}"
  "compare(s1,s2) = List__compare Char__compare(id s1,id s2)"
consts e_lt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<" 60)
defs e_lt_def: "s1 < s2 \<equiv> compare(s1,s2) = Less"
consts e_lt_eq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<=" 60)
defs e_lt_eq_def: 
  "(s1::string) <= (s2::string) \<equiv> (s1 < s2 \<or> s1 = s2)"
consts e_gt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">" 60)
defs e_gt_def: "(s1::string) > (s2::string) \<equiv> s2 < s1"
consts e_gt_eq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">=" 60)
defs e_gt_eq_def: "(s1::string) >= (s2::string) \<equiv> s2 <= s1"
consts newline :: "string"
defs newline_def: "newline \<equiv> ''
''"
consts toScreen :: "string \<Rightarrow> unit"
defs toScreen_def: "toScreen s \<equiv> ()"
consts writeLine :: "string \<Rightarrow> unit"
defs writeLine_def: "writeLine s \<equiv> ()"
consts Boolean__show :: "bool \<Rightarrow> string"
defs Boolean__show_def: 
  "Boolean__show x \<equiv> (if x then ''true'' else ''false'')"
consts Boolean__toString :: "bool \<Rightarrow> string"
defs Boolean__toString_def: "Boolean__toString \<equiv> Boolean__show"
consts Nat__natToString__digitToString :: "nat \<Rightarrow> string"
consts Nat__natToString__natToStringAux :: "nat \<times> string \<Rightarrow> string"
theorem Nat__natToString__natToStringAux_Obligation_subsort: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> 0 \<le> x div 10"
  apply(auto)
  done
theorem Nat__natToString__natToStringAux_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> 0 \<le> x mod 10"
  apply(auto)
  done
recdef Nat__natToString__natToStringAux "measure (\<lambda> (x,res). x)"
  "Nat__natToString__natToStringAux(x,res)
     = (if x < 10 then 
          Nat__natToString__digitToString x @ res
        else 
          Nat__natToString__natToStringAux(x div 10,
                                           Nat__natToString__digitToString (x 
                                                                              mod 10) 
                                             @ res))"
consts Nat__natToString :: "nat \<Rightarrow> string"
defs Nat__natToString_def: 
  "Nat__natToString x \<equiv> Nat__natToString__natToStringAux(x,'''')"
consts Nat__show :: "nat \<Rightarrow> string"
defs Nat__show_def: "Nat__show \<equiv> Nat__natToString"
consts Nat__toString :: "nat \<Rightarrow> string"
defs Nat__toString_def: "Nat__toString \<equiv> Nat__natToString"
consts Nat__natConvertible :: "string \<Rightarrow> bool"
defs Nat__natConvertible_def: 
  "Nat__natConvertible s
     \<equiv> (let cs = id s 
        in 
        (list_ex Char__isNum cs \<and> list_all Char__isNum cs))"
consts Nat__stringToNat__charToDigit :: "char \<Rightarrow> nat"
consts Nat__stringToNat__stringToNatAux :: "char list \<times> nat \<Rightarrow> nat"
theorem Nat__stringToNat__stringToNatAux_Obligation_subsort: 
  "\<lbrakk>list_all Char__isNum (Cons hd__v tl__v); 
    list_all Char__isNum (Cons hd__v tl__v)\<rbrakk> \<Longrightarrow> 
   0 \<le> (res::nat) * 10 + Nat__stringToNat__charToDigit hd__v"
  apply(auto)
  done
recdef Nat__stringToNat__stringToNatAux "measure (\<lambda>(chars,res). length chars)"
  "Nat__stringToNat__stringToNatAux([],res) = res"
  "Nat__stringToNat__stringToNatAux(Cons hd_v tl_v,res) 
     = Nat__stringToNat__stringToNatAux(tl_v,
                                        res * 10 
                                          + Nat__stringToNat__charToDigit hd_v)"
consts Nat__stringToNat :: "string \<Rightarrow> nat"
defs Nat__stringToNat_def: 
  "Nat__stringToNat s \<equiv> Nat__stringToNat__stringToNatAux(id s,0)"
consts Integer__intToString :: "int \<Rightarrow> string"
theorem Integer__intToString_Obligation_subsort: 
  "\<lbrakk>(x::int) \<ge> 0\<rbrakk> \<Longrightarrow> 0 \<le> x"
  apply(auto)
  done
theorem Integer__intToString_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::int) \<ge> 0)\<rbrakk> \<Longrightarrow> 0 \<le> - x"
  apply(auto)
  done
defs Integer__intToString_def: 
  "Integer__intToString x
     \<equiv> (if x \<ge> 0 then 
          Nat__natToString (nat x)
        else 
          ''-'' @ Nat__natToString (nat (- x)))"
consts Integer__show :: "int \<Rightarrow> string"
defs Integer__show_def: "Integer__show \<equiv> Integer__intToString"
consts Integer__toString :: "int \<Rightarrow> string"
defs Integer__toString_def: "Integer__toString \<equiv> Integer__intToString"
consts Integer__intConvertible :: "string \<Rightarrow> bool"
defs Integer__intConvertible_def: 
  "Integer__intConvertible s
     \<equiv> (let cs = id s 
        in 
        (list_ex Char__isNum cs 
           \<and> (list_all Char__isNum cs 
                \<or> hd cs = CHR ''-'' \<and> list_all Char__isNum (tl cs))))"
consts Integer__stringToInt :: "string \<Rightarrow> int"
consts Char__show :: "char \<Rightarrow> string"
defs Char__show_def: "Char__show c \<equiv> id ([c])"
consts Char__toString :: "char \<Rightarrow> string"
defs Char__toString_def: "Char__toString \<equiv> Char__show"
consts Compare__show :: "Compare__Comparison \<Rightarrow> string"
primrec 
  "Compare__show Greater = ''Greater''"
  "Compare__show Equal = ''Equal''"
  "Compare__show Less = ''Less''"
consts Option__show :: "('a \<Rightarrow> string) \<Rightarrow> 'a option \<Rightarrow> string"
primrec 
  "Option__show shw None = ''None''"
  "Option__show shw (Some x) = ''(Some '' @ shw x @ '')''"
consts List__show :: "string \<Rightarrow> string list \<Rightarrow> string"
end
