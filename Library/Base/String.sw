(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

String qualifying spec

% (Note that the generated proofs for this spec go into SW_String.thy
% rather than String.thy, because String is already a theory in the
% Isabelle libary.)

import Character, List

(* A string is a finite sequence of characters (of type Char). Thus, we define type
   String by isomorphism with lists of characters. *)

type String.String  % qualifier required for internal parsing reasons

proof Isa -hook helperlemma end-proof

% string that consists of argument list of characters:

op implode : Bijection (List Char, String)

(* Metaslang's string literals are simply syntactic shortcuts for expressions of
the form implode l, where l is a list of characters. For example, "Specware"
stands for implode [#S,#p,#e,#c,#w,#a,#r,#e]. *)

% list of constituent characters of a string:

op explode : String -> List Char = inverse implode

% analogues of some list ops:

op length (s:String) : Nat = length (explode s)

op @ (s:String, i:Nat | i < length s) infixl 30 : Char = (explode s) @ i

% Also could be called "substring":
op subFromTo (s:String, i:Nat, j:Nat | i <= j && j <= length s) : String =
  implode (subFromTo (explode s, i, j))

op ^ (s1:String, s2:String) infixl 25 : String =
  implode ((explode s1) ++ (explode s2))

op forall? (p: Char -> Bool) (s: String) : Bool =
  forall? p (explode s)

op exists? (p: Char -> Bool) (s: String) : Bool =
  exists? p (explode s)

op map (f: Char -> Char) (s: String) : String =
  implode (map f (explode s))

op flatten (ss: List String) : String = implode (flatten (map explode ss))

% replace each character with a string and concatenate:

op translate (subst: Char -> String) (s: String) : String =
  flatten (map subst (explode s))

% strings can be linearly ordered and compared element-wise and regarding
% the empty string smaller than any non-empty string:

op compare (s1:String, s2:String) : Comparison =
  compare Char.compare (explode s1, explode s2)

% linear ordering relations:

op <  (s1:String, s2:String) infixl 20 : Bool = (compare(s1,s2) = Less)
proof Isa -> <_s end-proof   % avoid overloading

op <= (s1:String, s2:String) infixl 20 : Bool = (s1 < s2 || s1 = s2)
proof Isa -> <=_s end-proof

op >  (s1:String, s2:String) infixl 20 : Bool = (s2 <  s1)
proof Isa -> >_s end-proof

op >= (s1:String, s2:String) infixl 20 : Bool = (s2 <= s1)
proof Isa -> >=_s end-proof

% string consisting of just the newline character:

op newline : String = "\n"

% convert Booleans to strings:

op Bool.show (x:Bool) : String = if x then "true" else "false"

% convert naturals to strings:

op Nat.digitToString (d:Nat | d < 10) : String =
  case d of
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"

% --------------------------------------------------------------------------------
% We need to formulate a few insights in Isabelle to make the
% subsequent proofs go through
proof Isa -verbatim
lemma Nat__digitToString_singleton:
 "x<10 \<Longrightarrow> \<exists>(a::char). Nat__digitToString x = [a]"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString0 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''0'') = (x=0)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString1 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''1'') = (x=1)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString2 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''2'') = (x=2)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString3 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''3'') = (x=3)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString4 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''4'') = (x=4)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString5 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''5'') = (x=5)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString6 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''6'') = (x=6)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString7 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''7'') = (x=7)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString8 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''8'') = (x=8)"
  by (induct x rule: Nat__digitToString.induct, auto)
lemma Nat__digitToString9 [simp]:
 "x<10 \<Longrightarrow> (Nat__digitToString x = ''9'') = (x=9)"
  by (induct x rule: Nat__digitToString.induct, auto)

lemma Nat__digitToString_of0 [simp]: "Nat__digitToString 0 = ''0''" by auto
lemma Nat__digitToString_of1 [simp]: "Nat__digitToString 1 = ''1''" by auto
lemma Nat__digitToString_of2 [simp]: "Nat__digitToString 2 = ''2''" by auto
lemma Nat__digitToString_of3 [simp]: "Nat__digitToString 3 = ''3''" by auto
lemma Nat__digitToString_of4 [simp]: "Nat__digitToString 4 = ''4''" by auto
lemma Nat__digitToString_of5 [simp]: "Nat__digitToString 5 = ''5''" by auto
lemma Nat__digitToString_of6 [simp]: "Nat__digitToString 6 = ''6''" by auto
lemma Nat__digitToString_of7 [simp]: "Nat__digitToString 7 = ''7''" by auto
lemma Nat__digitToString_of8 [simp]: "Nat__digitToString 8 = ''8''" by auto
lemma Nat__digitToString_of9 [simp]: "Nat__digitToString 9 = ''9''" by auto

lemma Nat__digitToString_not_empty [simp]:
"x<10 \<Longrightarrow> (Nat__digitToString x = []) = False"
  by (cut_tac x=x in Nat__digitToString_singleton, auto)
lemma Nat__digitToString_not_sign [simp]:
"x<10 \<Longrightarrow> (Nat__digitToString x = ''-'') = False"
  by (induct x rule: Nat__digitToString.induct, auto)
end-proof
% --------------------------------------------------------------------------------

theorem digitToString_injective is
  fa(x:{d:Nat | d < 10}, y:{d:Nat | d < 10})
  (digitToString x = digitToString y) = (x = y)

theorem length_of_digitToString is fa (d:Nat)
  d < 10 => length (digitToString d) = 1

op Nat.natToString (x:Nat) : String =
  if x < 10 then digitToString x
  else natToString (x div 10) ^ digitToString (x mod 10)

% --------------------------------------------------------------------------------
proof Isa -verbatim

lemma Nat__natToString_small:
"\<lbrakk>x < 10\<rbrakk>
 \<Longrightarrow> Nat__natToString x = Nat__digitToString x"
  by simp

lemma Nat__natToString_large:
"\<lbrakk>10 \<le> x\<rbrakk> \<Longrightarrow>
 Nat__natToString x =
 Nat__natToString (x div 10) @ Nat__digitToString (x mod 10)"
  by simp

lemma Nat__natToString_not_empty [simp]: "(Nat__natToString x = []) = False"
  by simp

lemmas [simp del] = Nat__natToString.simps (* avoid loops in the simplifier *)

lemma Nat__natToString_no_sign [simp]:
"(Nat__natToString x = (CHR ''-'' # s)) = False"
  apply (cut_tac f="\<lambda>x. x div 10"
             and P="\<lambda>x. \<forall>s.
                       (Nat__natToString x = CHR ''-'' # s) = False"
             and a="x" in measure_induct, auto)
  apply (subgoal_tac "x<10 \<or> 10\<le>x", erule disjE)
  apply (auto simp add: Nat__natToString_small)
  apply (cut_tac x="x" in Nat__digitToString_singleton, simp, simp)
  apply (simp add: Nat__natToString_large)
  apply (drule_tac x="x div 10" in spec, drule mp, simp,
         simp add: append_eq_Cons_conv)
done

lemma Nat__natToString_no_sign2 [simp]:
"((CHR ''-'' # s) = Nat__natToString x) = False"
  by (simp add: not_sym)
end-proof
% --------------------------------------------------------------------------------

theorem natToString_injective is
  fa(x:Nat, y:Nat)
  (natToString x = natToString y) = (x = y)

op Nat.show : Nat -> String = natToString

% convert strings to naturals (if convertible):

op Nat.natConvertible (s:String) : Bool =
  ex(x:Nat) natToString x = s
#translate Haskell -> natConvertible #end

op Nat.stringToNat (s:String | natConvertible s) : Nat =
  the(x:Nat) natToString x = s

% convert integers to strings:

op Integer.intToString (x:Int) : String =
  if x >= 0 then        natToString   x
            else "-" ^ natToString (-x)
#translate Haskell -> intToString #end

op Integer.show : Int -> String = intToString

% convert strings to integers (if convertible):

op Integer.intConvertible (s:String) : Bool =
  ex(x:Int) intToString x = s
#translate Haskell -> intConvertible #end

op Integer.stringToInt (s:String | intConvertible s) : Int =
  the(x:Int) intToString x = s
#translate Haskell -> stringToInt #end

% convert characters to strings:

op Char.show (c:Char) : String = implode [c]

% convert comparisons to strings:

op Compare.show : Comparison -> String = fn
  | Greater -> "Greater"
  | Equal   -> "Equal"
  | Less    -> "Less"

% given conversion from type a to String, convert Option a to String:

op [a] Option.show (shw: a -> String) : Option a -> String = fn
  | None   -> "None"
  | Some x -> "(Some " ^ (shw x) ^ ")"

% convert list of strings to string, using given separator:

op List.show (sep:String) (l: List String) : String =
  case l of
     | []     -> ""
     | hd::[] -> hd
     | hd::tl -> hd ^ sep ^ (List.show sep tl)



%%% Isabelle proofs



proof Isa stringToNat_Obligation_the
  apply (simp add: Nat__natConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp)
  apply(clarify)
  apply(simp add: String__natToString_injective)
end-proof

proof Isa stringToInt_Obligation_the
  apply (simp add:Integer__intConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp)
  apply (simp add: Integer__intToString_def split: if_splits)
  apply (cut_tac s = "s" in Nat__stringToNat_Obligation_the)
  apply (simp add: Nat__natConvertible_def, rule_tac x="nat x" in exI, simp)
  apply (erule ex1E, frule_tac x="nat x" in spec, drule_tac x="nat xa" in spec,
         auto)
  apply (cut_tac s = "Nat__natToString (nat (- x))"
         in Nat__stringToNat_Obligation_the)
  apply (simp add: Nat__natConvertible_def, rule_tac x="nat (-x)" in exI, simp)
  apply (erule ex1E, frule_tac x="nat (-x)" in spec,
         drule_tac x="nat (-xa)" in spec)
  apply (drule mp, simp, drule mp, clarify,
         thin_tac "Nat__natToString xb = Nat__natToString (nat (- x))",
         thin_tac "Nat__natToString (nat (- xa)) =
                   Nat__natToString (nat (- x))",
         auto)
end-proof

proof Isa show_Obligation_exhaustive
  by (cases l, auto)
end-proof

% mapping to Isabelle:

proof Isa ThyMorphism
  type String.String -> string
  String.explode    -> id
  String.implode    -> id
  String.length     -> length
  String.^          -> @ Left 65
  String.map        -> map
  String.exists?    -> list_ex
  String.forall?    -> list_all
  String.@          -> ! Left 100
end-proof

#translate Haskell -header
{-# OPTIONS -fno-warn-duplicate-exports #-}
#end

#translate Haskell -morphism
  type String.String -> String
  String.explode    -> id
  String.implode    -> id
  String.length     -> length
  String.^          -> ++    Left  5
  String.map        -> map
  String.exists?    -> any
  String.forall?    -> all
  String.@          -> !!    Left   9
  String.<=         -> <=    Infix 4
  String.<          -> <     Infix 4
  String.>=         -> >=    Infix 4
  String.>          -> >     Infix 4
  String.flatten    -> concat
  String.compare    -> compare curried
  Nat.show          -> show
  Integer.show      -> show
  Nat.natToString   -> show
  Nat.digitToString   -> show
  Integer.intToString -> show
  Nat.stringToNat   -> stringToInt
  String.subFromTo  -> list__subFromTo
#end

% ------------------------------------------------------------------------------
proof Isa -verbatim

lemma String__compare_equal_aux:
  "\<forall>y. String__compare (x, y) = Equal \<longrightarrow> x = y"
 apply (simp add: String__compare_def)
 apply (induct_tac x)
 apply (rule allI, induct_tac y, simp_all)
 apply (rule allI, induct_tac y, simp_all)
 apply (case_tac "Char__compare (a, aa)", simp_all)
done

lemma String__compare_equal [simp]:
  "\<lbrakk>String__compare (x, y) = Equal\<rbrakk> \<Longrightarrow> x = y"
 by (auto simp add: String__compare_equal_aux)

lemma String__compare_eq_simp [simp]:
  "String__compare (x, x) = Equal"
 by (induct x, simp_all add: String__compare_def )

lemma String__compare_equal_simp:
  "(String__compare (x, y) = Equal) = (x = y)"
 by auto

lemma String__compare_antisym_aux:
 "\<forall>y. String__compare (x, y) = Less \<and> String__compare (y, x) = Less \<longrightarrow> x = y"
 apply (simp add: String__compare_def)
 apply (induct_tac x)
 apply (rule allI, induct_tac y, simp_all)
 apply (rule allI, induct_tac y, simp_all)
 apply (case_tac "Char__compare (a, aa)", simp_all add: Char__compare_equal_simp)
 apply (case_tac "Char__compare (aa, a)", simp_all add: Char__compare_equal_simp)
 apply (drule Char__compare_antisym, simp_all)
done

lemma String__compare_antisym:
 "\<lbrakk>String__compare (x, y) = Less; String__compare (y, x) = Less\<rbrakk> \<Longrightarrow> x = y"
 by (auto simp add: String__compare_antisym_aux)

lemma String__compare_linear_aux:
 "\<forall>y. String__compare (x, y)  \<noteq> Less \<and>  y \<noteq> x \<longrightarrow> String__compare (y, x) = Less"
 apply (simp add: String__compare_def)
 apply (induct_tac x)
 apply (rule allI, induct_tac y, simp_all)
 apply (rule allI, induct_tac y, simp_all)
 apply (case_tac "Char__compare (a, aa)",
        simp_all add: Char__compare_equal_simp Char__compare_greater2less)
done

lemma String__compare_linear:
 "\<lbrakk>String__compare (x, y) \<noteq> Less; y \<noteq> x\<rbrakk> \<Longrightarrow> String__compare (y, x) = Less"
 by (cut_tac x=x in String__compare_linear_aux, simp)

lemma String__compare_trans_aux:
 "\<forall>y z. String__compare (x, y) = Less \<and>  String__compare (y, z) = Less
  \<longrightarrow> String__compare (x, z) = Less"
 apply (simp add: String__compare_def del: all_simps)
 apply (induct_tac x)
 apply (rule allI, induct_tac y, simp_all del: all_simps)
 apply (rule allI, induct_tac z, simp_all del: all_simps)
 apply (rule allI, induct_tac y, simp_all del: all_simps)
 apply (rule allI, induct_tac z, simp_all del: all_simps)
 apply (case_tac "Char__compare (a, aa)",
        simp_all add: Char__compare_equal_simp del: all_simps)
 apply (case_tac "Char__compare (aa, ab)",
        simp_all add: Char__compare_equal_simp del: all_simps)
 apply (drule_tac x=lista in spec, rotate_tac -1,
        drule_tac x=listb in spec, rotate_tac -1, simp)
 apply (case_tac "Char__compare (aa, ab)",
        simp_all add: Char__compare_equal_simp del: all_simps)
 apply (frule Char__compare_trans, simp, clarsimp)
done

lemma String__compare_trans:
 "\<lbrakk>String__compare (x, y) = Less; String__compare (y, z) = Less\<rbrakk>
  \<Longrightarrow> String__compare (x, z) = Less"
 by (cut_tac x=x in String__compare_trans_aux, auto)

end-proof    % end verbatim block
% ------------------------------------------------------------------------------

proof Isa digitToString_injective [simp]
  apply (subgoal_tac "x=0 \<or> x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or>
                      x=5 \<or> x=6 \<or> x=7 \<or> x=8 \<or> x=9",
         auto simp del: One_nat_def)
  apply (drule sym, simp)+
end-proof

proof Isa natToString_injective
  apply(induct x arbitrary: y rule: Nat__natToString.induct)
  apply(case_tac "x < 10", simp)
  apply(case_tac "y < 10")
  apply(simp add: Nat__natToString_small)
  apply(cut_tac x=y in Nat__natToString_large, simp)
  apply(simp add: Nat__natToString_small)
  apply (metis Nat__digitToString_singleton Nat__natToString_Obligation_subtype Nat__natToString_not_empty append1_eq_conv eq_Nil_appendI)
  apply(auto)
  apply(case_tac "y < 10", (auto)[1])
  apply (metis Nat__digitToString_singleton Nat__natToString_Obligation_subtype Nat__natToString_not_empty append1_eq_conv eq_Nil_appendI Nat__natToString.simps)
  apply(auto simp add: Nat__natToString_large)
  apply(rule divmodten)
  apply(case_tac "y div 10 = x div 10")
  apply(clarify)
  apply(clarify)
  apply(simp add: Nat__natToString_large)
end-proof

proof Isa length_of_digitToString [simp]
  apply (subgoal_tac "d=0 \<or> d=1 \<or> d=2 \<or> d=3 \<or> d=4 \<or>
                      d=5 \<or> d=6 \<or> d=7 \<or> d=8 \<or> d=9",
         auto simp del: One_nat_def)
end-proof

proof Isa helperlemma
theorem divmodten:
"\<lbrakk>(x::nat) mod 10 = (y mod 10); (x div 10) = (y div 10)\<rbrakk> \<Longrightarrow> x = y"
   by (metis mod_by_0 mod_mult2_eq mult_zero_right)
end-proof

end-spec
