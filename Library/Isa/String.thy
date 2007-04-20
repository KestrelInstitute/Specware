theory String
imports Char SW_List
begin
axioms explode_is_isomorphism: 
  "bij id"
consts substring :: "string \<times> nat \<times> nat \<Rightarrow> string"
consts translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
consts lt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "lt" 60)
consts leq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "leq" 60)
consts e_lt_eq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<=" 60)
consts e_lt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<" 60)
consts e_gt_eq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">=" 60)
consts e_gt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">" 60)
consts newline :: "string"
consts toScreen :: "string \<Rightarrow> unit"
consts writeLine :: "string \<Rightarrow> unit"
consts compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
theorem implode_def_Obligation_subsort: 
  "bij id"
  apply(auto)
  done
axioms implode_def: 
  "id = inv id"
axioms length_def: 
  "length s = length (id s)"
axioms concat_def: 
  "s1 @ s2 = id (id s1 @ id s2)"
axioms concat2_def: 
  "s1 @ s2 = s1 @ s2"
axioms concat3_def: 
  "s1 @ s2 = s1 @ s2"
axioms map_def: 
  "map f s = id (map f (id s))"
axioms exists_def: 
  "list_ex p s = list_ex p (id s)"
axioms all_def: 
  "list_all p s = list_all p (id s)"
theorem sub_def_Obligation_subsort: 
  "\<lbrakk>(n::nat) < length s\<rbrakk> \<Longrightarrow> n < length (id s)"
  apply(auto)
  done
axioms sub_def: 
  "\<lbrakk>n < length s\<rbrakk> \<Longrightarrow> s ! n = id s ! n"
theorem substring_def_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> (j::nat); j \<le> length s\<rbrakk> \<Longrightarrow> 
   i \<le> j \<and> j \<le> length s"
  apply(auto)
  done
theorem substring_def_Obligation_subsort0: 
  "\<lbrakk>(i::nat) \<le> (j::nat); j \<le> length s\<rbrakk> \<Longrightarrow> 
   i \<le> j \<and> j \<le> length (id s)"
  apply(auto)
  done
axioms substring_def: 
  "\<lbrakk>i \<le> j; j \<le> length s\<rbrakk> \<Longrightarrow> 
   substring(s,i,j) = id (List__sublist(id s,i,j))"
axioms concatList_def: 
  "concat ss = (case ss of Nil \<Rightarrow> '''' | Cons s ss1 \<Rightarrow> s @ concat ss1)"
axioms translate_def: 
  "translate subst s = concat (map subst (id s))"
axioms lt_def: 
  "s1 < s2 = (compare(s1,s2) = Less)"
axioms leq_def: 
  "(s1::string) <= (s2::string) = (s1 < s2 \<or> s1 = s2)"
axioms newline_def: 
  "newline = ''
''"
theorem toScreen_def: 
  "toScreen s = ()"
  apply(auto)
  done
theorem writeLine_def: 
  "writeLine s = ()"
  apply(auto)
  done
defs e_gt_eq_def: "(x::string) >= (y::string) \<equiv> y <= x"
defs e_gt_def: "(x::string) > (y::string) \<equiv> y < x"
recdef compare "{}"
  "compare(s1,s2)
     = (if s1 < s2 then 
          Less
        else 
          if s2 < s1 then Greater else Equal)"
consts Boolean__toString :: "bool \<Rightarrow> string"
consts Integer__toString :: "int \<Rightarrow> string"
consts Nat__toString :: "nat \<Rightarrow> string"
consts Char__toString :: "char \<Rightarrow> string"
consts Integer__intToString :: "int \<Rightarrow> string"
consts Integer__stringToInt :: "string \<Rightarrow> int"
consts Nat__natToString :: "nat \<Rightarrow> string"
consts Nat__stringToNat :: "string \<Rightarrow> nat"
consts Boolean__show :: "bool \<Rightarrow> string"
consts Compare__show :: "Compare__Comparison \<Rightarrow> string"
consts Option__show :: "('a \<Rightarrow> string) \<Rightarrow> 'a option \<Rightarrow> string"
consts Integer__intConvertible :: "string \<Rightarrow> bool"
consts Integer__show :: "int \<Rightarrow> string"
consts Nat__natConvertible :: "string \<Rightarrow> bool"
consts Nat__show :: "nat \<Rightarrow> string"
consts List__show :: "string \<Rightarrow> string list \<Rightarrow> string"
consts Char__show :: "char \<Rightarrow> string"
axioms boolean_toString_def: 
  "Boolean__toString x = (if x then ''true'' else ''false'')"
theorem int_toString_def_Obligation_subsort: 
  "\<lbrakk>(x::int) \<ge> 0\<rbrakk> \<Longrightarrow> 0 \<le> x"
  apply(auto)
  done
theorem int_toString_def_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::int) \<ge> 0)\<rbrakk> \<Longrightarrow> 0 \<le> - x"
  apply(auto)
  done
axioms int_toString_def: 
  "Integer__toString x 
     = (if x \<ge> 0 then 
          Nat__toString (nat x)
        else 
          ''-'' @ Nat__toString (nat (- x)))"
consts nat_toString_def__digitToString :: "nat \<Rightarrow> string"
consts nat_toString_def__toStringAux :: "nat \<times> string \<Rightarrow> string"
theorem nat_toString_def__toStringAux_Obligation_subsort: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> 0 \<le> int (x div 10)"
  apply(auto)
  done
theorem nat_toString_def__toStringAux_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> 0 \<le> int (x mod 10)"
  apply(auto)
  done
recdef nat_toString_def__toStringAux "measure (\<lambda> (x,res). x)"
  "nat_toString_def__toStringAux(x,res)
     = (if x < 10 then 
          nat_toString_def__digitToString x @ res
        else 
          nat_toString_def__toStringAux(x div 10,
                                        nat_toString_def__digitToString (x 
                                                                           mod 10) 
                                          @ res))"
axioms nat_toString_def: 
  "Nat__toString x = nat_toString_def__toStringAux(x,'''')"
axioms char_toString_def: 
  "Char__toString c = id ([c])"
axioms intToString_def: 
  "Integer__intToString = Integer__toString"
theorem stringToInt_def_Obligation_subsort: 
  "\<lbrakk>Integer__intConvertible s; 
    id s = Cons CHR ''-'' (P::char list); 
    (j::nat) = length s\<rbrakk> \<Longrightarrow> 1 \<le> j \<and> j \<le> length s"
  apply(auto)
  done

axioms natToString_def: 
  "Nat__natToString = Nat__toString"
consts stringToNat_def__charToDigit :: "char \<Rightarrow> nat"
consts stringToNat_def__stringToNatAux :: "char list \<times> nat \<Rightarrow> nat"
theorem stringToNat_def__stringToNatAux_Obligation_subsort: 
  "\<lbrakk>list_all Char__isNum (Cons hd__v tl__v)\<rbrakk> \<Longrightarrow> list_all Char__isNum tl__v"
  apply(auto)
  done
theorem stringToNat_def__stringToNatAux_Obligation_subsort0: 
  "\<lbrakk>list_all Char__isNum (Cons hd__v tl__v)\<rbrakk> \<Longrightarrow> Char__isNum hd__v"
  apply(auto)
  done
theorem stringToNat_def__stringToNatAux_Obligation_subsort1: 
  "\<lbrakk>list_all Char__isNum (Cons hd__v tl__v)\<rbrakk> \<Longrightarrow> 
   0 
     \<le> int ((res::nat) * 10 + stringToNat_def__charToDigit hd__v)"
  apply(auto)
  done
recdef stringToNat_def__stringToNatAux "measure (\<lambda>(chars,res). length chars)"
  "stringToNat_def__stringToNatAux([],res) = res"
  "stringToNat_def__stringToNatAux(Cons hd_v tl_v,res) 
     = stringToNat_def__stringToNatAux(tl_v,
                                       res * 10 
                                         + stringToNat_def__charToDigit hd_v)"
axioms stringToNat_def: 
  "\<lbrakk>Nat__natConvertible s\<rbrakk> \<Longrightarrow> 
   Nat__stringToNat s = stringToNat_def__stringToNatAux(id s,0)"
defs Boolean__show_def: "Boolean__show b \<equiv> Boolean__toString b"
primrec 
  "Compare__show Greater = ''Greater''"
  "Compare__show Equal = ''Equal''"
  "Compare__show Less = ''Less''"
primrec 
  "Option__show shw None = ''None''"
  "Option__show shw (Some x) = ''(Some '' @ shw x @ '')''"
defs Integer__intConvertible_def: 
  "Integer__intConvertible s
     \<equiv> (let cs = id s
        in
        (list_ex Char__isNum cs 
           \<and> (list_all Char__isNum cs 
                \<or> hd cs = CHR ''-'' \<and> list_all Char__isNum (tl cs))))"
defs Integer__show_def: "Integer__show i \<equiv> Integer__toString i"
defs Nat__natConvertible_def: 
  "Nat__natConvertible s
     \<equiv> (let cs = id s
        in
        (list_ex Char__isNum cs \<and> list_all Char__isNum cs))"
defs Nat__show_def: "Nat__show n \<equiv> Nat__toString n"
defs Char__show_def: "Char__show c \<equiv> Char__toString c"
end