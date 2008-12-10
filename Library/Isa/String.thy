theory String
imports Character SW_List
begin
theorem String__implode_subtype_constr: 
  "bij id"
  apply(auto)
  done
theorem String__explode__def: 
  "id = inv id"
  apply(auto)
  done
theorem String__length__def: 
  "length s = length (id s)"
  apply(auto)
  done
theorem String__e_at_Obligation_subtype: 
  "\<lbrakk>(i::nat) < length s; let ignore = id s in i \<ge> 0\<rbrakk> \<Longrightarrow> 
   i < length (id s) \<and> i \<ge> 0"
  apply(auto)
  done

theorem String__subFromTo_Obligation_subtype: 
  "\<lbrakk>(i::nat) \<le> (j::nat); 
    j \<le> length s; 
    let ignore = id s in i \<ge> 0 \<and> j \<ge> 0\<rbrakk> \<Longrightarrow> 
   j \<le> length (id s) \<and> (i \<ge> 0 \<and> j \<ge> 0)"
  apply(auto)
  done
consts String__subFromTo :: "string \<times> nat \<times> nat \<Rightarrow> string"
defs String__subFromTo_def: 
  "String__subFromTo
     \<equiv> (\<lambda> ((s::string),(i::nat),(j::nat)). id (List__subFromTo(id s,i,j)))"



theorem String__map__def: 
  "map f s = id (map f (id s))"
  apply(auto)
  done
consts String__flatten :: "string list \<Rightarrow> string"
defs String__flatten_def: "String__flatten ss \<equiv> id (concat (map id ss))"
consts String__translate :: "(char \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string"
defs String__translate_def: 
  "String__translate subst s \<equiv> String__flatten (map subst (id s))"
consts String__compare :: "string \<times> string \<Rightarrow> Compare__Comparison"
defs String__compare_def: 
  "String__compare
     \<equiv> (\<lambda> ((s1::string),(s2::string)). List__compare Char__compare(id s1,id s2))"




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
theorem Nat__natToString_Obligation_subtype: 
  "True"
  apply(auto)
  done

theorem Nat__natToString_Obligation_subtype1: 
  "\<lbrakk>\<not> ((x::nat) < 10); (x_2::int) = int (x mod 10)\<rbrakk> \<Longrightarrow> 
   x_2 < 10 \<and> x_2 \<ge> 0"
  apply(auto)
  done
consts Nat__natToString :: "nat \<Rightarrow> string"
recdef Nat__natToString "measure size"
  "Nat__natToString x
     = (if x < 10 then 
          Nat__digitToString x
        else 
          Nat__natToString (x div 10) 
            @ Nat__digitToString (x mod 10))"
consts Nat__show :: "nat \<Rightarrow> string"
defs Nat__show_def: "Nat__show \<equiv> Nat__natToString"
consts Nat__natConvertible :: "string \<Rightarrow> bool"
defs Nat__natConvertible_def: 
  "Nat__natConvertible s \<equiv> (\<exists>(x::nat). Nat__natToString x = s)"

consts Nat__stringToNat :: "string \<Rightarrow> nat"
defs Nat__stringToNat_def: 
  "Nat__stringToNat s \<equiv> (THE (x::nat). Nat__natToString x = s)"

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
  "Integer__intConvertible s \<equiv> (\<exists>(x::int). Integer__intToString x = s)"

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
  "(\<lambda> (x::string \<times> nat). 
      if snd x < length (fst x) then 
        let (x,y) = x in x ! y
      else 
        regular_val) 
     = (\<lambda> (x::string \<times> nat). 
          if snd x < length (fst x) then 
            let (x,y) = x in x ! y
          else 
            regular_val)"
  apply(auto)
  done
consts String__substring :: "string \<times> nat \<times> nat \<Rightarrow> string"
defs String__substring_def: "String__substring \<equiv> String__subFromTo"


theorem String__all__def: 
  "list_all = list_all"
  apply(auto)
  done
theorem String__exists__def: 
  "list_ex = list_ex"
  apply(auto)
  done

consts String__toScreen :: "string \<Rightarrow> unit"
defs String__toScreen_def: "String__toScreen s \<equiv> ()"
consts String__writeLine :: "string \<Rightarrow> unit"
defs String__writeLine_def: "String__writeLine s \<equiv> ()"
theorem String__lt__def: 
  "(\<lambda> (x,y). x < y) = (\<lambda> (x,y). x < y)"
  apply(auto)
  done
theorem String__leq__def: 
  "(\<lambda> (x,y). x <= y) = (\<lambda> (x,y). x <= y)"
  apply(auto)
  done
consts Boolean__toString :: "bool \<Rightarrow> string"
defs Boolean__toString_def: "Boolean__toString \<equiv> Boolean__show"
consts Nat__toString :: "nat \<Rightarrow> string"
defs Nat__toString_def: "Nat__toString \<equiv> Nat__show"
consts Integer__toString :: "int \<Rightarrow> string"
defs Integer__toString_def: "Integer__toString \<equiv> Integer__show"
consts Char__toString :: "char \<Rightarrow> string"
defs Char__toString_def: "Char__toString \<equiv> Char__show"
end