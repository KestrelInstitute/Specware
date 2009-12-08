spec
  import ../Monomorphic

  sort QuotientSet      = List EquivalenceClass % quotient as list          
  sort EquivalenceClass = List Element          % equivalence class as list 

  def class_member (x : Element,          y : EquivalenceClass) = x in? y
  def qset_member  (y : EquivalenceClass, z : QuotientSet)      = y in? z

endspec