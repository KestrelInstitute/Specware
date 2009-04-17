String qualifying spec

import Character, List

(* A string is a finite sequence of characters (of type Char). Thus, we define
type String by isomorphism with lists of characters. *)

type String.String  % qualifier required for internal parsing reasons

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

op subFromTo (s:String, i:Nat, j:Nat | i <= j && j <= length s) : String =
  implode (subFromTo (explode s, i, j))

op ++ (s1:String, s2:String) infixl 25 : String =
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

op <= (s1:String, s2:String) infixl 20 : Bool = (s1 < s2 || s1 = s2)

op >  (s1:String, s2:String) infixl 20 : Bool = (s2 <  s1)

op >= (s1:String, s2:String) infixl 20 : Bool = (s2 <= s1)

% string consisting of just the newline character:

op newline : String = "\n"

% convert booleans to strings:

op Boolean.show (x:Bool) : String = if x then "true" else "false"

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

lemma Nat__digitToString_injective [simp]: 
"\<lbrakk>x<10; y<10; Nat__digitToString x = Nat__digitToString y\<rbrakk>
 \<Longrightarrow>  x = y"
  apply (subgoal_tac "x=0 \<or> x=1 \<or> x=2 \<or> x=3 \<or> x=4 \<or>
                      x=5 \<or> x=6 \<or> x=7 \<or> x=8 \<or> x=9",
         auto simp del: One_nat_def)
  apply (drule sym, simp)+
done
end-proof
% --------------------------------------------------------------------------------

op Nat.natToString (x:Nat) : String =
  if x < 10 then digitToString x
  else natToString (x div 10) ++ digitToString (x mod 10)
proof Isa natToString_Obligation_subtype
 apply (simp add: Nat__posNat_p_def )
end-proof
proof Isa natToString_Obligation_subtype0
 apply (simp add: Nat__posNat_p_def )
end-proof

% --------------------------------------------------------------------------------
proof Isa -verbatim

lemma Nat__natToString_small [simp]: 
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
  apply (subgoal_tac "x<10 \<or> 10\<le>x", erule disjE, auto)
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

op Nat.show : Nat -> String = natToString

% convert strings to naturals (if convertible):

op Nat.natConvertible (s:String) : Bool =
  ex(x:Nat) natToString x = s

op Nat.stringToNat (s:String | natConvertible s) : Nat =
  the(x:Nat) natToString x = s
proof Isa stringToNat_Obligation_the
  apply (simp add: Nat__natConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp) 
  apply (cut_tac xs=s and
                 P ="\<lambda>s. \<forall>z y.
                     (Nat__natToString z = s \<and> Nat__natToString y = s)
                     -->  (y = z)" 
         in rev_induct, auto,
         thin_tac "Nat__natToString xa = Nat__natToString x")
  apply (drule_tac x="z div 10" in spec, drule_tac x="y div 10" in spec)
  apply (cut_tac x=z in  Nat__natToString.simps, 
         cut_tac x=y in  Nat__natToString.simps, 
         simp split: split_if_asm, simp_all add: not_less)
  apply (cut_tac x="y mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="z" in Nat__digitToString_singleton, simp,
         erule exE, erule exE, simp)
  apply (cut_tac x="z mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="y" in Nat__digitToString_singleton, simp,
         erule exE, erule exE, simp)
  apply (cut_tac x="z mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         cut_tac x="y mod (10\<Colon>nat)" in Nat__digitToString_singleton, 
                                       simp add: mod_less_divisor,
         erule exE, erule exE, simp)
  apply (thin_tac "Nat__natToString z = xs @ [xb]", thin_tac "10 \<le> z",
         thin_tac "Nat__natToString y = xs @ [xb]", thin_tac "10 \<le> y",
         thin_tac "aa = xb",
         thin_tac "Nat__natToString (z div 10) = xs \<and> a = xb")
  apply (subgoal_tac "(y mod 10) = (z mod 10)", auto) 
  apply (rule_tac s="10 * (y div 10) + (y mod 10)" in ssubst)
  apply (rule_tac s="10 * (z div 10) + (z mod 10)" in ssubst)
  apply (simp, rule sym, rule mod_div_equality2, rule sym,
         rule mod_div_equality2)
  (*** there should be an easier way ***)
end-proof

% convert integers to strings:

op Integer.intToString (x:Integer) : String =
  if x >= 0 then        natToString   x
            else "-" ++ natToString (-x)

op Integer.show : Integer -> String = intToString

% convert strings to integers (if convertible):

op Integer.intConvertible (s:String) : Bool =
  ex(x:Integer) intToString x = s

op Integer.stringToInt (s:String | intConvertible s) : Integer =
  the(x:Integer) intToString x = s
proof Isa stringToInt_Obligation_the
  apply (simp add:Integer__intConvertible_def, erule exE)
  apply (rule_tac a=x in ex1I, simp)
  apply (simp add: Integer__intToString_def split: split_if_asm)
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
  | Some x -> "(Some " ++ (shw x) ++ ")"

% convert list of strings to string, using given separator:

op List.show (sep:String) (l: List String) : String =
  case l of
     | []     -> ""
     | hd::[] -> hd
     | hd::tl -> hd ++ sep ++ (List.show sep tl)

% deprecated:

op sub : {(s,n) : String * Nat | n < length s} -> Char = (@)

op substring : {(s,i,j) : String * Nat * Nat |
                i <= j && j <= length s} -> String = subFromTo

op concat : String * String -> String = (++)

op ^ infixl 25 : String * String -> String = (++)

op all : (Char -> Bool) -> String -> Bool = forall?

op exists : (Char -> Bool) -> String -> Bool = exists?

op concatList : List String -> String = flatten
proof Isa 
   apply (rule ext, simp add: String__flatten_def id_def)
end-proof

op toScreen (s:String) : () = ()

op writeLine (s:String) : () = ()

% Since lt and leq are not being mapped to predefined Isabelle ops
% it is better for the translation to specify them with arguments.

op lt (s1:String, s2:String) infixl 20 : Bool = (s1 <  s2)

op leq (s1:String, s2:String) infixl 20 : Bool = (s1 <=  s2)

op Boolean.toString : Bool -> String = Boolean.show

op Nat.toString : Nat -> String = Nat.show

op Integer.toString : Integer -> String = Integer.show

op Char.toString : Char -> String = Char.show

% mapping to Isabelle:

proof Isa ThyMorphism
  type String.String -> string
  String.explode    -> id
  String.implode    -> id
  String.length     -> length
  String.concat     -> @ Left 25
  String.++         -> @ Left 25
  String.^          -> @ Left 25
  String.map        -> map
  String.exists?    -> list_ex
  String.exists     -> list_ex
  String.forall?    -> list_all
  String.all        -> list_all
  String.@          -> ! Left 40
  String.sub        -> ! Left 40
  String.concatList -> concat
end-proof

endspec
