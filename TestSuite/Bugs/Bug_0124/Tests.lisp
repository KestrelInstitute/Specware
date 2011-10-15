(test-directories ".")


(test 

  ("Bug 0124 : Choose prints incorrectly"
   :show  "SetsAsLists"
   :output '((:optional ";;; Elaborating spec at $TESTDIR/SetsAsLists")
	     (:optional ";;; Elaborating spec at $TESTDIR/Lists")
	     (:optional "")
	     "spec  "
	     " import Lists"
	     (:optional "")
	     " op  no_repetitions : ListI -> Bool"
             (:alternatives
              (" def no_repetitions l = "
               "   (case l")
              (" def no_repetitions (l : ListI) : Bool"
               "    = case l"))
	     "      of nilI -> true"
             (:alternatives
              "       | consI (hd, tl) -> ~(member(hd, tl)) && no_repetitions tl)"
              "       | consI (hd, tl) -> (~(member(hd, tl)) && no_repetitions tl)"
              ("       | consI (hd : Integer, tl : ListI) -> "
               "         ~(member(hd, tl)) && no_repetitions tl)"))
	     (:optional "")
	     " type ListNR = (ListI | no_repetitions)"
	     (:optional "")
	     " op  permutation : ListNR * ListNR -> Bool"
	     (:optional "")
             (:alternatives
              (" def permutation (l1 : ListNR, l2 : ListNR) : Bool"
              "   = length l1 = length l2 ")
              (" def permutation (l1, l2) = "
               "   length l1 = length l2 "))
	     "   && (case l1"
	     "         of nilI -> true"
             (:alternatives
              "          | consI (hd, tl) -> permutation(tl, delete(l2, hd)))"
              ("         | consI (hd : Integer, tl : ListI) -> "
               "            permutation(tl, delete(l2, hd)))"))
	     (:optional "")
	     " type SetAsList = (ListNR / permutation)"
	     (:optional "")
	     " op  empty_set : SetAsList"
             (:alternatives
              " def empty_set = quotient[SetAsList] (nilI)"
              " def empty_set : SetAsList = quotient[SetAsList] (nilI)")
	     (:optional "")
	     " op  union : SetAsList * SetAsList -> SetAsList"
	     (:optional "")
             (:alternatives
              (" def union (s1, s2) = "
               "   choose[SetAsList] ")
              (" def union (s1 : SetAsList, s2 : SetAsList) : SetAsList"
               "   = choose[SetAsList]"))
             (:alternatives
              ("      (fn (l1 : ListNR) -> "
               "         choose[SetAsList] "
               "            (fn (l2 : ListNR) -> quotient[SetAsList]  (union_aux(l1, l2)))"
               "             s2)"
               "      s1")
              ("     ((fn l1 -> "
               "          choose[SetAsList] "
               "            ((fn l2 -> quotient[SetAsList] (union_aux(l1, l2)))) s2)) s1")
              ("     ((fn l1 : ListNR -> "
               "         choose[SetAsList] "
               "            ((fn l2 : ListNR -> quotient[SetAsList] (union_aux(l1, l2)))) s2))"
               "      s1"))
	     (:optional "")
	     " op  union_aux : ListNR * ListNR -> ListNR"
	     (:optional "")
	     (:alternatives
              (" def union_aux (l1, l2) = "
               "   (case l1")
              ("def union_aux (l1 : ListNR, l2 : ListNR) : ListNR"
               "  = case l1"))
	     "      of nilI -> l2"
             (:alternatives
              "       | consI (hd, tl) -> "
              "       | consI (hd : Integer, tl : ListI) -> ")
             "         if member(hd, l2)"
	     "          then union_aux(tl, l2) "
             (:alternatives
              "         else consI(hd, union_aux(tl, l2)))"
              "         else consI(hd, union_aux(tl, l2))")
	     (:optional "")
	     " op  insert : Integer * SetAsList -> SetAsList"
	     (:optional "")
             (:alternatives
              ("def insert (i : Integer, s : SetAsList) : SetAsList"
               "  = choose[SetAsList] "
               "     (fn (l : ListNR) -> "
               "         quotient[SetAsList]"
               "          (if member(i, l) then l else consI(i, l)))"
               "      s"))
	     (:optional "")
	     (:optional "")
	     "endspec"
	     (:optional "")
	     (:optional "")
	     ))
  )
