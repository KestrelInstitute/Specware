spec

  import Lists

  op no_repetitions : ListI -> Boolean
  def no_repetitions(l) = case l of
                             | nilI -> true
                             | consI(hd,tl) -> ~(member(hd,tl))
                                             & no_repetitions(tl)

  sort ListNR = (ListI | no_repetitions)

  op permutation : ListNR * ListNR -> Boolean
  def permutation(l1,l2) = length(l1) = length(l2) &
                           (case l1 of
                               | nilI -> true
                               | consI(hd,tl) -> permutation(tl,delete(l2,hd)))

  sort SetAsList = ListNR / permutation

  op empty_set : SetAsList
  def empty_set = quotient(permutation)(nilI)

  op union : SetAsList * SetAsList -> SetAsList
  def union(s1,s2) = % quotient(union_aux(choose(s1),choose(s2)))
                     choose
                       permutation
                       (fn l1 -> choose
                                   permutation
                                   (fn l2 -> quotient
                                               permutation
                                                 (union_aux(l1,l2)))
                                   s2)
                       s1

  op union_aux : ListNR * ListNR -> ListNR
  def union_aux(l1,l2) = case l1 of
                            | nilI -> l2
                            | consI(hd,tl) -> if member(hd,l2)
                                              then union_aux(tl,l2)
                                              else consI(hd,union_aux(tl,l2))

  op insert : Integer * SetAsList -> SetAsList
  def insert(i,s) = % if member(i,choose(s)) then s
                    % else quotient(consI(i,choose(s)))
                    choose
                      permutation
                      (fn l -> quotient
                                 permutation
                                 (if member(i,l) then l
                                  else consI(i,l)))
                      s

endspec
