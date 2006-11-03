theory String
imports Char SW_List
begin
axioms explode_is_isomorphism: "bij id"
axioms length_subtype_constr: "length dom_length \<ge> 0"
consts substring :: "string \<times> int \<times> int \<Rightarrow> string"
consts translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
consts lt :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "lt" 60)
consts leq :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "leq" 60)
(*
consts <= :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<=" 60)
consts < :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl "<" 60)
consts >= :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">=" 60)
consts > :: "string \<Rightarrow> string \<Rightarrow> bool"	(infixl ">" 60) *)
consts newline :: "string"
consts toScreen :: "string \<Rightarrow> unit"
consts writeLine :: "string \<Rightarrow> unit"
consts compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
axioms implode_def: "id = inv id"
axioms length_def: "length s = length (id s)"
axioms concat_def: "s1 @ s2 = id (id s1 @ id s2)"
axioms concat2_def: "s1 @ s2 = s1 @ s2"
axioms concat3_def: "s1 @ s2 = s1 @ s2"
axioms map_def: "map f s = id (map f (id s))"
axioms exists_def: "list_ex p s = list_ex p (id s)"
axioms all_def: "list_all p s = list_all p (id s)"
axioms sub_def: 
  "\<lbrakk>n \<ge> 0; n < length s\<rbrakk> \<Longrightarrow> s ! n = id s ! n"
(*
axioms substring_def: 
  "\<lbrakk>j \<ge> 0; i \<ge> 0; i \<le> j; j \<le> length s\<rbrakk> \<Longrightarrow> 
   substring(s,i,j) = id (List__sublist(id s,i,j))" *)
axioms concatList_def: 
  "concat ss = (case ss of Nil \<Rightarrow> '''' | Cons s ss1 \<Rightarrow> s @ concat ss1)"
axioms translate_def: "translate subst s = concat (map subst (id s))"
(*
axioms lt_def: "(< s1 s2) = (compare(s1,s2) = Less)"
axioms leq_def: "(<= s1 s2) = ((< s1 s2) \<or> s1 = s2)" *)
(*
axioms newline_def: "newline = ''
''"*)
(*
defs >=_def: ">= \<equiv> \<lambda> (x,y). <= y x"
defs >_def: "> \<equiv> \<lambda> (x,y). < y x"
defs compare_def: 
  "compare
     \<equiv> \<lambda> (s1,s2). 
         if < s1 s2 then 
           Less
         else 
           if < s2 s1 then Greater else Equal" *)
consts Boolean__toString :: "bool \<Rightarrow> string"
consts Integer__toString :: "int \<Rightarrow> string"
consts Nat__toString :: "int \<Rightarrow> string"
consts Char__toString :: "char \<Rightarrow> string"
consts Integer__intToString :: "int \<Rightarrow> string"
consts Integer__stringToInt :: "string \<Rightarrow> int"
consts Nat__natToString :: "int \<Rightarrow> string"
consts Nat__stringToNat :: "string \<Rightarrow> int"
axioms Nat__stringToNat_subtype_constr: 
  "\<lbrakk>Nat__natConvertible dom_stringToNat\<rbrakk> \<Longrightarrow> 
   Nat__stringToNat dom_stringToNat \<ge> 0"
consts Boolean__show :: "bool \<Rightarrow> string"
consts Compare__show :: "Compare__Comparison \<Rightarrow> string"
consts Option__show :: "('a \<Rightarrow> string) \<Rightarrow> 'a option \<Rightarrow> string"
consts Integer__intConvertible :: "string \<Rightarrow> bool"
consts Integer__show :: "int \<Rightarrow> string"
consts Nat__natConvertible :: "string \<Rightarrow> bool"
consts Nat__show :: "int \<Rightarrow> string"
consts List__show :: "string \<Rightarrow> string list \<Rightarrow> string"
consts Char__show :: "char \<Rightarrow> string"
axioms boolean_toString_def: 
  "Boolean__toString x = (if x then ''true'' else ''false'')"
axioms int_toString_def: 
  "Integer__toString x 
     = (if x \<ge> 0 then 
          Nat__toString x
        else 
          ''-'' @ Nat__toString (- x))"
(*
axioms nat_toString_def: 
  "\<lbrakk>x \<ge> 0\<rbrakk> \<Longrightarrow> 
   Nat__toString x 
     = (let
        digitToString = 
        \<lambda> d. 
          case d
           of 0 \<Rightarrow> ''0''
            | 1 \<Rightarrow> ''1''
            | 2 \<Rightarrow> ''2''
            | 3 \<Rightarrow> ''3''
            | 4 \<Rightarrow> ''4''
            | 5 \<Rightarrow> ''5''
            | 6 \<Rightarrow> ''6''
            | 7 \<Rightarrow> ''7''
            | 8 \<Rightarrow> ''8''
            | 9 \<Rightarrow> ''9''
        in
        (let
         toStringAux = 
         \<lambda> (x,res). 
           if x < 10 then 
             digitToString x @ res
           else 
             toStringAux(x * 10,digitToString (x * 10) @ res)
         in
         toStringAux(x,'''')))" *)
axioms char_toString_def: "Char__toString c = id ([c])"
axioms intToString_def: "Integer__intToString = Integer__toString"
(*
axioms stringToInt_def: 
  "\<lbrakk>Integer__intConvertible s\<rbrakk> \<Longrightarrow> 
   Integer__stringToInt s 
     = (let Cons firstchar _ = id s
        in
        (if firstchar = CHR ''-'' then 
           - (Nat__stringToNat (substring(s,1,length s)))
         else 
           Nat__stringToNat s))" *)
axioms natToString_def: "Nat__natToString = Nat__toString"
(*
axioms stringToNat_def: 
  "\<lbrakk>Nat__natConvertible s\<rbrakk> \<Longrightarrow> 
   Nat__stringToNat s 
     = (let
        charToDigit = 
        \<lambda> c. case c of 0 \<Rightarrow> 0 | 1 \<Rightarrow> 1 | 2 \<Rightarrow> 2 | 3 \<Rightarrow> 3 | 4 \<Rightarrow> 4 | 5 \<Rightarrow> 5 | 6 \<Rightarrow> 6 | 7 \<Rightarrow> 
                                                                               7 | 8 \<Rightarrow> 
                                                                                   8 | 9 \<Rightarrow> 
                                                                                       9
        in
        (let
         stringToNatAux = 
         \<lambda> (chars,res). 
           case chars
            of Nil \<Rightarrow> res
             | Cons hd tl \<Rightarrow> stringToNatAux(tl,res * 10 + charToDigit hd)
         in
         stringToNatAux(id s,0)))" *)
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
(*
primrec 
  "List__show sep [] = ''''"
  "List__show sep [x] = x"
  "List__show sep (Cons x y) = x @ sep @ List__show sep y" *)
defs Char__show_def: "Char__show c \<equiv> Char__toString c"
end