spec

(* This spec collects deprecated types and ops of the Specware base library. It
will be eventually eliminated. *)

import String

op Function.wfo: [a] (a * a -> Bool) -> Bool

op Option.some : [a] a -> Option a = embed Some
op Option.none : [a]      Option a = embed None

type Integer.NonZeroInteger = Int0

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
 type Integer.Integer -> int
 Integer.~            -> -
 Integer.rem          -> modT Left 22
end-proof

op List.nil : [a] List a = empty

op List.cons : [a] a * List a -> List a = (|>)

op List.insert : [a] a * List a -> List a = (|>)

op List.null : [a] List a -> Bool = empty?

op List.hd : [a] List1 a -> a = head

proof Isa List__hd_subtype_constr 
  by (simp add: list_all_iff)
end-proof

op List.tl : [a] List1 a -> List a = tail

proof Isa List__tl_subtype_constr
  apply (auto simp add: list_all_iff, erule bspec)
  apply (rule_tac t="d__x" and s="hd d__x # tl d__x" in subst, simp)
  apply (simp del: hd_Cons_tl)
  
end-proof

op List.concat : [a] List a * List a -> List a = (++)

proof Isa List__concat_subtype_constr 
  by (auto simp add: list_all_iff)
end-proof

op List.nth : [a] {(l,i) : List a * Nat | i < length l} -> a = (@)

proof Isa List__nth_subtype_constr 
  by (simp add: list_all_length)
end-proof

op List.nthTail : [a] {(l,n) : List a * Nat | n <= length l} -> List a =
  removePrefix
proof Isa [simp] end-proof

proof Isa List__nthTail_subtype_constr 
  by (auto simp add: list_all_iff, drule bspec, erule in_set_dropD, simp)
end-proof

op List.member : [a] a * List a -> Bool = (in?)

op List.removeFirstElems : [a] {(l,n) : List a * Nat |
                                 n <= length l} -> List a = removePrefix
proof Isa [simp] end-proof

proof Isa List__removeFirstElems_subtype_constr 
  by (auto simp add: list_all_iff, drule bspec, erule in_set_dropD, simp)
end-proof

op List.sublist : [a] {(l,i,j) : List a * Nat * Nat |
                       i <= j && j <= length l} -> List a = subFromTo
proof Isa [simp] end-proof
proof Isa List__sublist_subtype_constr 
   by (auto simp add: List__subFromTo_subtype_constr)
end-proof

op List.exists : [a] (a -> Bool) -> List a -> Bool = exists?

op List.all : [a] (a -> Bool) -> List a -> Bool = forall?

op [a] List.rev2 (l: List a, r: List a) : List a =
  case l of
  | [] -> r
  | hd::tl -> rev2 (tl, hd::r)

proof Isa List__rev2_subtype_constr 
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

proof Isa List__find_subtype_constr
  by (simp add: List__findLeftmost_subtype_constr)
end-proof

op List.firstUpTo : [a] (a -> Bool) -> List a -> Option (a * List a) =
  findLeftmostAndPreceding
proof Isa [simp] end-proof

proof Isa List__firstUpTo_subtype_constr
  by (simp add: List__findLeftmostAndPreceding_subtype_constr)
end-proof

op List.splitList : [a] (a -> Bool) -> List a -> Option (List a * a * List a) =
  splitAtLeftmost
proof Isa [simp] end-proof

op List.locationOf : [a] List a * List a -> Option (Nat * List a) =
  leftmostPositionOfSublistAndFollowing
proof Isa [simp] end-proof
proof Isa List__splitList_subtype_constr
  by (simp only: List__splitList_def List__splitAtLeftmost_subtype_constr)
end-proof

proof Isa List__locationOf_subtype_constr
  by (simp add: List__leftmostPositionOfSublistAndFollowing_subtype_constr)
end-proof

op [a] List.app (f: a -> ()) (l: List a) : () =
  case l of
     | []     -> ()
     | hd::tl -> (f hd; app f tl)

proof Isa Thy_Morphism
  List.nil -> []
  List.cons -> # Right 23
  List.insert -> # Right 23
  List.null -> null
  List.hd ->  hd  
  List.tl ->  tl
  List.concat ->  @ Left 25
  List.nth -> ! Left 35
  List.rev -> rev
  List.member ->  mem Left 22
  List.exists -> list_ex  
  List.all ->  list_all
end-proof

endspec
