NatMap qualifying spec {
  import SplayMap

  sort NatMap.Map a = SplayMap.Map (Nat, a)

  op empty      : fa(a) NatMap.Map a
  op insert     : fa(a) NatMap.Map a * Nat * a -> NatMap.Map a
  op find       : fa(a) NatMap.Map a * Nat -> Option a 

  op map        : fa(a,b) (a -> b) -> NatMap.Map a -> NatMap.Map b
  op mapi       : fa(a,b) (Nat * a -> b)  -> NatMap.Map a -> NatMap.Map b
  op appi       : fa(a) (Nat * a -> ()) -> NatMap.Map a -> ()
  op foldri     : fa(a,b) (Nat * a * b -> b) -> b ->  NatMap.Map a -> b
  op listItems  : fa(a) NatMap.Map a -> List a
  op inDomain   : fa(a) NatMap.Map a * Nat -> Boolean 
  op numItems   : fa(a) NatMap.Map a -> Nat

  op compose    : NatMap.Map Nat * NatMap.Map Nat -> NatMap.Map Nat

  def empty      = SplayMap.empty Nat.compare
  def insert     = SplayMap.insert
  def find       = SplayMap.find
  def map        = SplayMap.map
  def mapi       = SplayMap.mapi
  def appi       = SplayMap.appi
  def foldri     = SplayMap.foldri
  def listItems  = SplayMap.listItems
  def inDomain   = SplayMap.inDomain
  def numItems   = SplayMap.numItems
  def compose    = SplayMap.compose
}
