theory String
imports Char SW_List
begin
theorem implode_subtype_constr: 
  "bij id"
  apply(auto)
  done
theorem sub_Obligation_subsort: 
  "\<lbrakk>(n::nat) < length s; let ignore = id s in n \<ge> 0\<rbrakk> \<Longrightarrow> 
   n < length (id s) \<and> n \<ge> 0"
  apply(auto)
  done
theorem substring_Obligation_subsort: 
  "\<lbrakk>(i::nat) \<le> (j::nat); 
    j \<le> length s; 
    let ignore = id s in i \<ge> 0 \<and> j \<ge> 0\<rbrakk> \<Longrightarrow> 
   j \<le> length (id s) \<and> (i \<ge> 0 \<and> j \<ge> 0)"
  apply(auto)
  done
consts substring :: "string \<times> nat \<times> nat \<Rightarrow> string"
recdef substring "{}"
  "substring(s,i,j) = id (List__sublist(id s,i,j))"
consts translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
defs translate_def: "translate subst s \<equiv> concat (map subst (id s))"
consts compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
recdef compare "{}"
  "compare(s1,s2) = List__compare Char__compare(id s1,id s2)"
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
primrec 
  "Nat__natToString__digitToString 0 = ''0''"
  "Nat__natToString__digitToString (Suc d) 
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
                        if d + 1 = 9 then ''9'' else arbitrary)"
theorem Nat__natToString__natToStringAux_Obligation_subsort: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> x div 10 \<ge> 0"
  apply(auto)
  done
theorem Nat__natToString__natToStringAux_Obligation_subsort0: 
  "\<lbrakk>\<not> ((x::nat) < 10)\<rbrakk> \<Longrightarrow> x mod 10 \<ge> 0"
  apply(auto)
  done
consts Nat__natToString__natToStringAux :: "nat \<times> string \<Rightarrow> string"
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
defs Nat__stringToNat__charToDigit_def: 
  "Nat__stringToNat__charToDigit c
     \<equiv> (if c = CHR ''0'' then 
          0
        else 
          if c = CHR ''1'' then 
            1
          else 
            if c = CHR ''2'' then 
              2
            else 
              if c = CHR ''3'' then 
                3
              else 
                if c = CHR ''4'' then 
                  4
                else 
                  if c = CHR ''5'' then 
                    5
                  else 
                    if c = CHR ''6'' then 
                      6
                    else 
                      if c = CHR ''7'' then 
                        7
                      else 
                        if c = CHR ''8'' then 
                          8
                        else 
                          if c = CHR ''9'' then 9 else arbitrary)"
theorem Nat__stringToNat__stringToNatAux_Obligation_subsort: 
  "\<lbrakk>list_all Char__isNum (Cons hd__v tl__v)\<rbrakk> \<Longrightarrow> 
   (res::nat) * 10 + Nat__stringToNat__charToDigit hd__v \<ge> 0"
  apply(auto)
  done
consts Nat__stringToNat__stringToNatAux :: "char list \<times> nat \<Rightarrow> nat"
recdef Nat__stringToNat__stringToNatAux "measure (\<lambda>(chars,res). length chars)"
  "Nat__stringToNat__stringToNatAux([],res) = res"
  "Nat__stringToNat__stringToNatAux(Cons hd_v tl_v,res) 
     = Nat__stringToNat__stringToNatAux(tl_v,
                                        res * 10 
                                          + Nat__stringToNat__charToDigit hd_v)"
consts Nat__stringToNat :: "string \<Rightarrow> nat"
defs Nat__stringToNat_def: 
  "Nat__stringToNat s \<equiv> Nat__stringToNat__stringToNatAux(id s,0)"
theorem Integer__intToString_Obligation_subsort: 
  "\<lbrakk>\<not> ((x::int) \<ge> 0)\<rbrakk> \<Longrightarrow> - x \<ge> 0"
  apply(auto)
  done
consts Integer__intToString :: "int \<Rightarrow> string"
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
theorem Integer__intConvertible_Obligation_subsort: 
  "\<lbrakk>id (s::string) = cs; list_ex Char__isNum cs; \<not> (list_all Char__isNum cs)\<rbrakk>
    \<Longrightarrow> \<not> (null cs)"
    sorry
theorem Integer__intConvertible_Obligation_subsort0: 
  "\<lbrakk>id (s::string) = cs; 
    list_ex Char__isNum cs; 
    \<not> (list_all Char__isNum cs); 
    hd cs = CHR ''-''\<rbrakk> \<Longrightarrow> \<not> (null cs)"
    sorry
consts Integer__intConvertible :: "string \<Rightarrow> bool"
defs Integer__intConvertible_def: 
  "Integer__intConvertible s
     \<equiv> (let cs = id s 
        in 
        (list_ex Char__isNum cs 
           \<and> (list_all Char__isNum cs 
                \<or> hd cs = CHR ''-'' \<and> list_all Char__isNum (tl cs))))"
theorem Integer__stringToInt_Obligation_subsort: 
  "\<lbrakk>Integer__intConvertible s; 
    id s = Cons CHR ''-'' (P::char list); 
    True; 
    length s \<ge> 0; 
    (j::nat) = length s\<rbrakk> \<Longrightarrow> 1 \<le> j \<and> j \<le> length s"
  apply(auto)
  done
theorem Integer__stringToInt_Obligation_subsort0: 
  "\<lbrakk>Integer__intConvertible s; id s = Cons CHR ''-'' P\<rbrakk> \<Longrightarrow> 
   Nat__natConvertible (substring(s,1,length s))"
    sorry
theorem Integer__stringToInt_Obligation_subsort1: 
  "\<lbrakk>Integer__intConvertible s; 
    id s = Cons (firstchar::char) (P::char list); 
    \<not> (firstchar = CHR ''-'')\<rbrakk> \<Longrightarrow> Nat__natConvertible s"
    sorry
consts Integer__stringToInt :: "string \<Rightarrow> int"
defs Integer__stringToInt_def: 
  "Integer__stringToInt s
     \<equiv> (case id s
         of Cons firstchar _ \<Rightarrow> 
            if firstchar = CHR ''-'' then 
              - (int (Nat__stringToNat (substring(s,1,length s))))
            else 
              int (Nat__stringToNat s))"
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
  "Option__show shw (Some x) = (''(Some '' @ shw x) @ '')''"
consts List__show :: "string \<Rightarrow> string list \<Rightarrow> string"
end