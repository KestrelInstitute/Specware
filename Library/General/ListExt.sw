(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

List qualifying spec

(* This spec is an extension of the base spec for lists. *)

import Order, Map

% ------------------------------------------------------------------------------
% ---------- Part 1: Specifications --------------------------------------------
% ------------------------------------------------------------------------------

(* True iff list is ordered according to given relation. *)

op [a] sorted? (rel:EndoRelation a) (l:List a) : Bool =
  fa(i:Nat) i < length l - 1 => rel (l@i, l@(i+1))

(* Sort list according to given linear order. (Note that "sort" is currently
prohibited in Metaslang for backward compatibility.) *)

op [a] sortt (ord:LinearOrder a) (l:List a) : List a = the(l')
  l' permutationOf l && sorted? ord l'

(* Arrange elements of (finite) set according to given linear order. *)

op [a] sortset (ord:LinearOrder a) (s:FiniteSet a) : List a = the(l)
  noRepetitions? l && toSet l = s && sorted? ord l

(* Convert map to association list. A linear order on the map's domain must be
supplied. The list follows that order. *)

op [a,b] toAssocList (m:FiniteMap(a,b)) (ord:LinearOrder a) : List (a * b) =
  the (alist: List (a * b))
     let (xs, _) = unzip alist in
     noRepetitions? xs &&
     sorted? ord xs &&
     m = fromAssocList alist

(* Op @ is based on a left-to-right 0-based indexing of the elements of the
list. It is sometimes convenient to index the elements of a list starting from 1
and/or right-to-left. The following ops provide these capabilities, along with
the totalizations that are analogous to op @@.

Naming rationale:
- default is left-to-right 0-based
- 1 indicates 1-based
- R indicates right-to-left

*)

op [a]  @_1  (l: List a, i:PosNat | i <= length l) infixl 30 : a = l @ (i - 1)

op [a]  @_R  (l: List a, i:   Nat | i <  length l) infixl 30 : a = l @ (length l
                                                                       - 1 - i)

op [a]  @_R1 (l: List a, i:PosNat | i <= length l) infixl 30 : a = l @_R (i - 1)

op [a] @@_1  (l: List a, i:PosNat) infixl 30 : Option a = l @@ (i - 1)

op [a] @@_R  (l: List a, i:   Nat) infixl 30 : Option a = if i < length l
                                                          then l @@ (length l
                                                                     - 1 - i)
                                                          else None

op [a] @@_R1 (l: List a, i:PosNat) infixl 30 : Option a = l @@_R (i - 1)

% ------------------------------------------------------------------------------
% ---------- Part 2: Theorems about properties of operations -------------------
% ------------------------------------------------------------------------------

% ------------------------------------------------------------------------------
% ---------- Part 3: Main theorems ---------------------------------------------
% ------------------------------------------------------------------------------

theorem sorted_p_butlast is [a]
    fa  (rel:EndoRelation a, l:List a) 
       (l ~= empty) => 
       sorted? rel l => sorted? rel (butLast l)

(*****************************************************************
**** Later - translation is not how I need it 

theorem sorted_p_last_is_max is 
    fa  (l:List Nat) 
      sorted? (<) l => 
      (fa (i:Nat) i < length l - 1 => l@i < last l)

theorem sorted_p_max_is_last is 
    fa  (l:List Nat, m:Nat) 
      sorted? (<) l =>
      m in? l => 
      (fa (i:Nat) i < length l => l@i <= m) =>
      m = last l
******************************************************************************)

% ------------------------------------------------------------------------------
% ---------- Part 4: Theory Morphisms ------------------------------------------
% ------------------------------------------------------------------------------


% ------------------------------------------------------------------------------
% ---------- Part 5: The proofs ------------------------------------------------
% ------------------------------------------------------------------------------
% Note: for the time being we place Isabelle lemmas that are needed for a proof 
%       and cannot be expressed in SpecWare as "verbatim" lemmas into the
%       preceeding proofs 
% ------------------------------------------------------------------------------


proof Isa sortt_Obligation_the
 (*** in principle we can use "linorder.sort l" 
      but there are context and type conversion issues
  ***) 
 sorry
end-proof

proof Isa sortset_Obligation_the
 (*** in principle we can use "sorted_list_of_set s" 
      but there are context and type conversion issues
  ***)
 sorry
end-proof

proof Isa toAssocList_Obligation_the
 (*** later
      Note:  List__toAssocList__stp_def has a Rep_Map__FiniteMap missing
  ***) 
 sorry
end-proof



proof Isa sorted_p_butlast
 by (induct l rule: rev_induct, auto simp add: List__sorted_p_def ,
     drule_tac x=i in spec, auto simp add: nth_append)
end-proof

proof Isa sorted_p_last_is_max
 apply (induct l, auto simp add: List__sorted_p_def )
 apply (subgoal_tac "\<forall>i. int i < int (length l) - 1 \<longrightarrow> l ! i < l ! Suc i", simp)
 apply (case_tac "i=0", simp_all)
 apply (case_tac "length l > 1", simp_all)
 apply (rule_tac y="l!0" in less_trans)
 apply (thin_tac "_", drule_tac x=0 in spec, simp)
 apply (drule_tac x=0 in spec, simp)
 apply (drule_tac x=0 in spec, simp,
        rule_tac t="l" and s="[l!0]" in subst, simp_all, rule sym,
        simp add: length_1_nth_conv [symmetric] not_less 
                  length_greater_0_conv [symmetric] del: length_greater_0_conv )
 apply (rule_tac t=i and s="Suc (i - 1)" in subst, simp, simp only: nth_Cons_Suc)
 apply (clarify, drule_tac x="Suc ia" in spec, auto)
end-proof

proof Isa sorted_p_max_is_last
 apply (simp frule length_pos_if_in_set, simp)
 apply (drule_tac x="length l - 1" in spec, simp)
 apply (drule  List__sorted_p_last_is_max, simp add: last_conv_nth)
 apply (simp add: in_set_conv_nth, safe)
 apply (case_tac "i < length l - 1")
 apply (drule_tac x=i in spec, simp)
 apply (rule_tac t=i and s="length l - Suc 0" in subst, simp_all)
end-proof


proof Isa 
 (*** later ***) 
 sorry
end-proof

% ------------------------------------------------------------------------------
% ---------- Part 6: verbatim Isabelle lemmas             ----------------------
% ----------         that cannot be expressed in SpecWare ----------------------
% ------------------------------------------------------------------------------


%  ---------- most of the following can be converted into SpecWare Theorems 
% ----------- need to do this later

proof Isa -verbatim


(******* SORTED ********)

lemma nondec_as_sorted_p:
  "List__sorted_p {(x, y). x \<le> y} = nondec"
  apply (simp add: List__sorted_p_def  fun_eq_iff, rule allI)
  apply (induct_tac x, auto)
  apply (case_tac list, simp_all, rotate_tac 2, drule_tac x=0 in spec, simp)
  apply (case_tac list, simp_all, case_tac "i = 0", auto simp add: neq_iff)
  apply (drule_tac x="Suc i" in spec, simp)
  apply (case_tac list, simp_all)
done


lemma List__sorted_p_butlast2:
 "\<lbrakk>List__sorted_p {((x::nat), (y::nat)). x < y} l\<rbrakk> \<Longrightarrow> List__sorted_p {((x::nat), (y::nat)). x < y} (butlast l)"
 by (induct l rule: rev_induct, auto simp add: List__sorted_p_def ,
     drule_tac x=i in spec, auto simp add: nth_append)

lemma List__sorted_p_last_is_max:
 "\<lbrakk>List__sorted_p {((x::nat), (y::nat)). x < y} (l::nat list)\<rbrakk> \<Longrightarrow> \<forall>i<length l - 1. l!i < last l" 
 apply (induct l, auto simp add: List__sorted_p_def )
 apply (subgoal_tac "\<forall>i. int i < int (length l) - 1 \<longrightarrow> l ! i < l ! Suc i", simp)
 apply (case_tac "i=0", simp_all)
 apply (case_tac "length l > 1", simp_all)
 apply (rule_tac y="l!0" in less_trans)
 apply (thin_tac "_", drule_tac x=0 in spec, simp)
 apply (drule_tac x=0 in spec, simp)
 apply (drule_tac x=0 in spec, simp,
        rule_tac t="l" and s="[l!0]" in subst, simp_all, rule sym,
        simp add: length_1_nth_conv [symmetric] not_less 
                  length_greater_0_conv [symmetric] del: length_greater_0_conv )
 apply (clarify, drule_tac x="Suc ia" in spec, auto)
done

lemma List__sorted_p_max_is_last:
 "\<lbrakk>List__sorted_p {((x::nat), (y::nat)). x < y} (l::nat list); m mem l; \<forall>i<length l. l!i \<le> m\<rbrakk> \<Longrightarrow> m = last l"
 apply (frule length_pos_if_in_set, simp)
 apply (drule_tac x="length l - 1" in spec, simp)
 apply (drule  List__sorted_p_last_is_max, simp add: last_conv_nth)
 apply (simp add: in_set_conv_nth, safe)
 apply (case_tac "i < length l - 1")
 apply (drule_tac x=i in spec, simp)
 apply (rule_tac t=i and s="length l - Suc 0" in subst, simp_all)
done


(****** AssocLists *********)


lemma List__unzip_Assoc_empty [simp]:
  "\<lbrakk>Order__linearOrder_p ord\<rbrakk> \<Longrightarrow> 
    List__unzip (List__toAssocList (Abs_Map__FiniteMap Map.empty) ord)
    = ([],[])"
  apply (simp add: List__toAssocList_def)
  apply (rule the1I2, cut_tac List__toAssocList_Obligation_the, 
         simp_all, clarify)
  apply (cut_tac d__x=x in List__unzip_subtype_constr, simp)
  apply (rotate_tac -2, drule sym, rotate_tac -1,
         erule rev_mp, simp add: Map__fromAssocList_def,
         subst Abs_Map__FiniteMap_inject,
         simp_all add: member_def dom_if)
  apply (simp only: dom_eq_empty_conv [symmetric], 
         auto simp add: dom_if)
done

lemma List__unzip_Assoc_singleton [simp]:
  "\<lbrakk>Order__linearOrder_p ord\<rbrakk> \<Longrightarrow> 
    List__unzip (List__toAssocList 
           (Abs_Map__FiniteMap (Map__update Map.empty i val)) ord)
    = ([i],[val])"
  apply (simp add: List__toAssocList_def)
  apply (rule the1I2, cut_tac List__toAssocList_Obligation_the, 
         simp_all, clarify)
  apply (cut_tac d__x=x in List__unzip_subtype_constr, simp)
  apply (rotate_tac -2, 
         erule rev_mp, simp add: Map__fromAssocList_def,
         subst Abs_Map__FiniteMap_inject,
         simp_all add: member_def dom_if)
  apply (subgoal_tac "dom (Map__update Map.empty i val) = {i}", 
         clarify, simp add: dom_if, simp_all add: Map__update_def dom_if)
  apply (drule distinct_card, simp)
by (metis List__positionOf_singleton insert_absorb insert_not_empty length_0_conv length_Suc_conv
    list.set(1) nth_Cons_0 option.inject set_ConsD singletonI)
end-proof
% ------------------------------------------------------------------------------

endspec
