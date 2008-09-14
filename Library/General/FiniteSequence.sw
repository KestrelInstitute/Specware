FSeq qualifying spec

 (* This spec is a temporary placeholder, which will be removed as soon as the
 JCRE specs are updated to no longer reference finite sequences but lists. *)

 type FSeqFunction a = ListFunction a

 type FSeq a = List a

 op seq : [a] Bijection (FSeqFunction a, FSeq a) = list

 op seq_1 : [a] Bijection (FSeq a, FSeqFunction a) = list_1

 op [a] inRange? (s: FSeq a, i:Nat) : Boolean = i < length s

 type NonEmptyFSeq a = List1 a

 op single? : [a] FSeq a -> Boolean = ofLength? 1

 type SingletonFSeq a = (FSeq a | single?)

 op first : [a] NonEmptyFSeq a -> a = head

 op ltail : [a] NonEmptyFSeq a -> FSeq a = butLast

 op rtail : [a] NonEmptyFSeq a -> FSeq a = tail

 type InjectiveFSeq a = InjList a

 op [a,b] matchingOptionSeqs? : List (Option a) * List (Option b) -> Boolean =
  matchingOptionLists?

endspec
