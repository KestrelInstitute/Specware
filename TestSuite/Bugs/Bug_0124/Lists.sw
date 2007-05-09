spec

  sort ListI = | nilI
               | consI Integer * ListI
  % we add "I" (for "Integers") to distinguish from built-in lists

  op isempty : ListI -> Boolean
  def isempty(l) = (l = nilI)

  op length : ListI -> Integer
  def length(l) = case l of
                     | nilI -> 0
                     | consI(hd,tl) -> 1 + length(tl)

  op max : ListI -> Integer
  def max(l) = case l of
                  | nilI -> 0
                  | consI(hd,tl) -> let m = max(tl) in
                                    if (hd > m) then hd else m

  op concat : ListI * ListI -> ListI
  def concat(l1,l2) = case l1 of
                         | nilI -> l2
                         | consI(hd,tl) -> consI(hd,concat(tl,l2))

  op member : Integer * ListI -> Boolean
  def member(i,l) = case l of
                       | nilI -> false
                       | consI(hd,tl) -> if i = hd then true
                                         else member(i,tl)

  op delete : ListI * Integer -> ListI
  def delete(l,i) = case l of
                       | nilI -> nilI
                       | consI(hd,tl) -> if hd = i then delete(tl,i)
                                         else consI(hd,delete(tl,i))

  op prefix : {(l,n) : ListI * Integer | 0 <= n & n <= length(l)} -> ListI
  def prefix(l,n) = if (n = 0) then nilI
                    else case l of
                            | consI(hd,tl) -> consI(hd,prefix(tl,n-1))

  op sublist : {(l,pos1,pos2) : ListI * Integer * Integer |
                0 <= pos1 & pos1 < pos2 & pos2 <= length(l)} -> ListI
  def sublist(l,pos1,pos2) =
      if (pos1 = 0) then prefix(l,pos2)
      else case l of
              | consI(hd,tl) -> sublist(tl,pos1-1,pos2-1)

  op half1 : ListI -> ListI
  def half1(l) = sublist(l, 0, length(l) div 2)

  op half2 : ListI -> ListI
  def half2(l) = sublist(l, length(l) div 2, length(l))

  % one is not obliged to use pattern matching: destructors can be
  % defined and used with tests to define ops, e.g. concatenation

  op head : {l : ListI | ~(isempty(l))} -> Integer
  def head(l) = case l of
                   | consI(hd,tl) -> hd

  op tail : {l : ListI | ~(isempty(l))} -> ListI
  def tail(l) = case l of
                   | consI(hd,tl) -> tl

  op concat2 : ListI * ListI -> ListI
  def concat2(l1,l2) = if isempty(l1) then l2
                       else consI(head(l1),concat2(tail(l1),l2))

endspec
