(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

(* This spec collects deprecated types and ops of the Specware base library. It
will be eventually eliminated. *)

op Function.wfo: [a] (a * a -> Bool) -> Bool

op Option.some : [a] a -> Option a = embed Some
op Option.none : [a]      Option a = embed None

(*** Integer ***)

type Integer.NonZeroInt = Int0

op Nat.natural? (i:Int) : Bool = i >= 0

op Integer.~ : Bijection (Int, Int) = -
proof Isa e_tld_subtype_constr
 apply(rule IntegerAux__e_dsh_subtype_constr)
end-proof

op Integer.rem infixl 26 : Int * Int0 -> Int = modT

theorem Integer.non_zero_divides_iff_zero_remainder is
  fa (x:Int0, y:Int) x divides y <=> y rem x = zero
proof Isa
  apply (simp add: divides_iff_modT_0)
end-proof

proof Isa Thy_Morphism
 type Integer.Int -> int
 Integer.~        -> -
 Integer.rem      -> modT Left 22
end-proof

(*** List ***)

op List.nil : [a] List a = empty

op List.cons : [a] a * List a -> List a = (|>)

op List.insert : [a] a * List a -> List a = (|>)

op List.null : [a] List a -> Bool = empty?

op List.hd : [a] List1 a -> a = head

proof Isa hd_subtype_constr 
  by (simp add: list_all_iff)
end-proof

op List.tl : [a] List1 a -> List a = tail

proof Isa tl_subtype_constr
  apply (auto simp add: list_all_iff, erule bspec)
  apply (rule_tac t="d__x" and s="hd d__x # tl d__x" in subst, simp)
  apply (simp del: hd_Cons_tl)
  
end-proof

op List.concat : [a] List a * List a -> List a = (++)

proof Isa concat_subtype_constr 
  by (auto simp add: list_all_iff)
end-proof

op List.nth : [a] {(l,i) : List a * Nat | i < length l} -> a = (@)

proof Isa nth_subtype_constr 
  by (simp add: list_all_length)
end-proof

op List.nthTail : [a] {(l,n) : List a * Nat | n <= length l} -> List a =
  removePrefix
proof Isa [simp] end-proof

proof Isa nthTail_subtype_constr 
  by (auto simp add: list_all_iff, drule bspec, erule in_set_dropD, simp)
end-proof

op List.member : [a] a * List a -> Bool = (in?)

op List.removeFirstElems : [a] {(l,n) : List a * Nat |
                           n <= length l} -> List a = removePrefix
proof Isa [simp] end-proof

proof Isa removeFirstElems_subtype_constr 
  by (auto simp add: list_all_iff, drule bspec, erule in_set_dropD, simp)
end-proof

op List.sublist : [a] {(l,i,j) : List a * Nat * Nat |
                  i <= j && j <= length l} -> List a = subFromTo
proof Isa [simp] end-proof
proof Isa sublist_subtype_constr 
   by (auto simp add: List__subFromTo_subtype_constr)
end-proof


op List.exists : [a] (a -> Bool) -> List a -> Bool = exists?

op List.all : [a] (a -> Bool) -> List a -> Bool = forall?

op [a] List.rev2 (l: List a, r: List a) : List a =
  case l of
  | [] -> r
  | hd::tl -> rev2 (tl, hd::r)

proof Isa rev2_subtype_constr 
  apply (subgoal_tac "\<forall>l\<in>list_all P__a. \<forall>r\<in> list_all P__a. 
                           list_all P__a (List__rev2 (l, r))",
         drule_tac x=l in bspec, simp add: mem_def,
         drule_tac x=r in bspec, simp add: mem_def, simp)
  apply (thin_tac "list_all P__a l", thin_tac "list_all P__a r",
         rule ballI, erule rev_mp)
  apply (induct_tac l, auto simp add: mem_def)
end-proof

op List.rev : [a] List a -> List a = reverse

op List.find : [a] (a -> Bool) -> List a -> Option a = findLeftmost
proof Isa [simp] end-proof

proof Isa find_subtype_constr
  by (simp add: List__findLeftmost_subtype_constr)
end-proof

op List.firstUpTo : [a] (a -> Bool) -> List a -> Option (a * List a) =
  findLeftmostAndPreceding
proof Isa [simp] end-proof

proof Isa firstUpTo_subtype_constr
  by (simp add: List__findLeftmostAndPreceding_subtype_constr)
end-proof

op List.splitList : [a] (a -> Bool) -> List a -> Option (List a * a * List a) =
  splitAtLeftmost
proof Isa [simp] end-proof

op List.locationOf : [a] List a * List a -> Option (Nat * List a) =
  leftmostPositionOfSublistAndFollowing
proof Isa [simp] end-proof
proof Isa splitList_subtype_constr
  by (simp only: List__splitList_def List__splitAtLeftmost_subtype_constr)
end-proof

proof Isa  locationOf_subtype_constr
  by (simp add: List__leftmostPositionOfSublistAndFollowing_subtype_constr)
end-proof


(*** String ***)


op String.sub : {(s,n) : String * Nat | n < length s} -> Char = (@)

op String.substring : {(s,i,j) : String * Nat * Nat |
                i <= j && j <= length s} -> String = subFromTo

op String.concat : String * String -> String = (++)

op String.++ infixl 25 : String * String -> String = (^)

op String.all : (Char -> Bool) -> String -> Bool = forall?

op String.exists : (Char -> Bool) -> String -> Bool = exists?

op String.concatList : List String -> String = flatten
proof Isa 
   apply (rule ext, simp add: String__flatten_def id_def)
end-proof

% Since lt and leq are not being mapped to predefined Isabelle ops
% it is better for the translation to specify them with arguments.

op String.lt (s1:String, s2:String) infixl 20 : Bool = (s1 <  s2)

op String.leq (s1:String, s2:String) infixl 20 : Bool = (s1 <=  s2)

op Bool.toString : Bool -> String = Bool.show

op Nat.toString : Nat -> String = Nat.show

op Integer.toString : Int -> String = Integer.show

op Char.toString : Char -> String = Char.show


endspec
