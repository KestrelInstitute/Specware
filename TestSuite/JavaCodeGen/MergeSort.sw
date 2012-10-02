spec

  import Lists

  op merge : ListI * ListI -> ListI
  def merge(l1,l2) = if isempty(l1) then l2
                     else if isempty(l2) then l1
                     else let hd1 = head(l1) in
                          let hd2 = head(l2) in
                          if (hd1 < hd2) then consI(hd1,merge(tail(l1),l2))
                          else consI(hd2,merge(l1,tail(l2)))

  op mtype : ListI -> ListI
  def mtype(l) = if (length(l) < 2) then l
                 else merge (mtype(half1(l)), mtype(half2(l)))

endspec
