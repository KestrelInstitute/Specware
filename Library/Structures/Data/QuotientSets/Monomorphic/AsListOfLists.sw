spec
  import ../Monomorphic

  sort QuotientSet      = List EquivalenceClass % quotient as list          
  sort EquivalenceClass = List Element          % equivalence class as list 

  def class_member (x : Element,          y : EquivalenceClass) = List.member(x,y)
  def qset_member  (y : EquivalenceClass, z : QuotientSet)      = List.member(y,z)

endspec