(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

String qualifying spec

import String

refine def Nat.natConvertible (s : String) : Bool =
 let cs = explode s in
 (exists? isNum cs) && (forall? isNum cs)

refine def Integer.intConvertible (s : String) : Bool =
 let cs = explode s in
 (exists? isNum cs)
 &&
 ((forall? isNum cs) || (head cs = #- && forall? isNum (tail cs)))

op explodedStringToNat (l : List Char | forall? isNum l) : Nat =
 foldl (fn (result, dig : (Char | isNum)) ->
          result * 10 + ord dig - 48)
       0
       l

refine def Integer.stringToInt (s : String | intConvertible s) : Int =
 let e_s = explode s in
 let firstchar :: r_s = e_s in
 if firstchar = #- then
   - (explodedStringToNat r_s)
 else
   explodedStringToNat e_s

refine def Nat.stringToNat (s : String | natConvertible s) : Nat =
 explodedStringToNat(explode s)

refine def explode (s : String) : List Char =
 tabulate (length s, fn i -> s@i)

def implode (char_list : List Char) : String =
 %% Hopefully code generators will provide a more efficient version
 foldl (fn (s, c) ->
          s ^ show c)
       ""
       char_list

proof isa Nat__natConvertible__1__obligation_refine_def
 (**  proof is extremely tedious  -- see attempt below

  apply (simp add: Nat__natConvertible_def Nat__natConvertible__1_def
                   list_ex_iff list_all_iff,
         rule iffI)
  apply (rule conjI)
  * 1. Existence **
  apply (clarify, case_tac "x<10",
         simp_all add: Nat__natToString_small Nat__natToString_large)
  apply (frule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp)+
  apply (simp)
  apply (frule Nat__natToString_Obligation_subtype,
         drule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp (no_asm_simp))+
  apply (simp (no_asm_simp))
  * 2. Proper bounds *
  apply (induct s rule: rev_induct, clarsimp, clarsimp)
  apply (case_tac "xa<10",
         simp_all add: Nat__natToString_small Nat__natToString_large)
  apply (frule_tac Nat__digitToString_singleton, clarsimp)
  apply (drule sym, drule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp)+
  apply (simp)
  apply (frule Nat__natToString_Obligation_subtype,
         frule_tac Nat__digitToString_singleton, clarsimp,
         rotate_tac -1, drule sym)
  apply (subgoal_tac "\<exists>x. Nat__natToString x = Nat__natToString (xa div 10)",
         simp, thin_tac _)
  apply (frule Nat__natToString_Obligation_subtype,
         drule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp only: Nat__digitToString.simps,
         thin_tac "?x mod 10 = ?y", simp)+
  apply (simp)
  apply (rule exI, simp)
  * 3 The other way around *
  apply (induct s rule: rev_induct, simp, clarsimp)
  apply (subgoal_tac "nat_of_char CHR ''0'' = 48 \<and>  nat_of_char CHR ''9'' = 57",
         simp, thin_tac "?A \<and> ?B")
  defer apply (simp)
  apply (subgoal_tac "nat_of_char x - 48 < 10", simp_all)
  apply (case_tac xs, clarsimp)
  apply (rule_tac x="nat_of_char x - 48" in exI,
         simp add: Nat__natToString_small)
  apply (rule_tac t="[x]" and s="[char_of_nat (nat_of_char x)]" in subst,
         simp add: char_of_nat_of_char)
  apply (drule Nat__digitToString_Obligation_exhaustive,
         simp only: le_imp_diff_is_add)
  apply (erule disjE,
         simp add: char_of_nat_def nibble_pair_of_nat_def nibble_of_nat_def)+
  apply (simp add: char_of_nat_def nibble_pair_of_nat_def nibble_of_nat_def)
  (* step *)
  apply (subgoal_tac "\<exists>x. x \<in> set xs")
  defer apply (rule_tac x=a in exI, simp)
  apply (clarsimp)
  apply (rule_tac x="xa * 10 + nat_of_char x - 48" in exI)
  apply (subst  Nat__natToString_large)
    (* oh well, what if xa=0? **)
 **********************************************************************)
sorry
end-proof

proof isa Integer__intConvertible__1__obligation_refine_def
 (**  proof is extremely tedious

  apply (simp add: Integer__intConvertible_def Integer__intToString_def
                   Integer__intConvertible__1_def)
  apply (cut_tac s=s in Nat__natConvertible__1__obligation_refine_def,
         simp add: Nat__natConvertible_def Nat__natConvertible__1_def)
 **********************************************************************)
sorry
end-proof

proof isa Integer__stringToInt__1_Obligation_subtype0
  by (simp add: Integer__intConvertible__1__obligation_refine_def
                Integer__intConvertible__1_def)
end-proof

proof isa Integer__stringToInt__1_Obligation_subtype
  by (clarsimp simp add: Integer__intConvertible__1__obligation_refine_def
                         Integer__intConvertible__1_def)
end-proof

proof isa Integer__stringToInt__1__obligation_refine_def
sorry
end-proof

proof isa Nat__stringToNat__1_Obligation_subtype
  by (clarsimp simp add: Nat__natConvertible__1__obligation_refine_def
                         Nat__natConvertible__1_def)
end-proof

proof isa Nat__stringToNat__1__obligation_refine_def
  apply (simp add: Nat__stringToNat_def,
         rule the1I2, erule Nat__stringToNat_Obligation_the)
  apply (thin_tac _, simp add: Nat__stringToNat__1_def)
  apply (subgoal_tac "\<forall>x. Nat__natToString x = s \<longrightarrow> x = String__explodedStringToNat s",
         simp, thin_tac _)
  apply (induct s  rule: rev_induct, auto)
  apply (drule sym, case_tac "xa < 10",
         simp_all add: Nat__natToString_small Nat__natToString_large)
  apply (thin_tac _, thin_tac _, drule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp add: String__explodedStringToNat_def)+
  apply (simp add: add: String__explodedStringToNat_def)
  apply (drule_tac x="xa div 10" in spec)
  apply (frule Nat__natToString_Obligation_subtype,
         frule_tac Nat__digitToString_singleton, clarsimp)
  apply (simp add: String__explodedStringToNat_def, thin_tac "_ = _")
  apply (rule_tac t = "(of_char a)::nat" and s = "xa mod 10 + 48" in subst)
  apply (drule sym, frule Nat__natToString_Obligation_subtype,
         drule Nat__digitToString_Obligation_exhaustive)
  apply (erule disjE, simp only: Nat__digitToString.simps,
         thin_tac "_ mod 10 = _", simp)+
  apply (simp)
  apply simp
end-proof

proof isa String__explode__1_Obligation_subtype
 (** TRANSLATION ISSUE: Obligation is false and should not have been generated
     in the first place.  According to the definition of tabulate, the "s@i"
     in 'tabulate (length s, fn i -> s@i)" will only be applied of i < length s

   sjw: This should be generated. The problem is that the type system cannot capture the
    above property. The solution is to use a version of tabulate with a dependent type:
    op [a] tabulate (l: Nat) (f: {i: Nat | i < l} -> a): List a
  **)
sorry
end-proof

proof isa String__explode__1__obligation_refine_def
  by (simp add: String__explode__1_def list_eq_iff_nth_eq,
      simp add: List__tabulate_alt )
end-proof

proof Isa String__implode_Obligation_subtype
  sorry
end-proof

proof isa String__implode__def
  by (induct char_list rule: rev_induct,
      auto simp add: Char__show_def)
end-proof

endspec
