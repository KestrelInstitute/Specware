spec

  import Lists

  op merge : ListI * ListI -> ListI
  def merge(l1,l2) = if isempty(l1) then l2
                     else if isempty(l2) then l1
                     else let hd1 = head(l1) in
                          let hd2 = head(l2) in
                          if (hd1 < hd2) then consI(hd1,merge(tail(l1),l2))
                          else consI(hd2,merge(l1,tail(l2)))

  op msort : ListI -> ListI
  def msort(l) = if (length(l) < 2) then l
                 else merge (msort(half1(l)), msort(half2(l)))

endspec
