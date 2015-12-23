(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  import ../Monomorphic

  type QuotientSet      = List EquivalenceClass % quotient as list          
  type EquivalenceClass = List Element          % equivalence class as list 

  def class_member (x : Element,          y : EquivalenceClass) = x in? y
  def qset_member  (y : EquivalenceClass, z : QuotientSet)      = y in? z

endspec
