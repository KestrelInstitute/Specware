NatMap qualifying spec {
  import SplayMap

  sort Map a = SplayMap.Map (Nat, a)

  op empty      : fa(a)   Map a
  op insert     : fa(a)   Map a * Nat * a -> Map a
  op find       : fa(a)   Map a * Nat -> Option a 

  op map        : fa(a,b) (a -> b) -> Map a -> Map(b)
  op mapi       : fa(a,b) (Nat * a -> b)  -> Map a -> Map b
  op appi       : fa(a)   (Nat * a -> ()) -> Map a -> ()
  op foldri     : fa(a,b) (Nat * a * b -> b) -> b ->  Map a -> b
  op listItems  : fa(a)   Map a -> List a
  op inDomain   : fa(a)   Map a * Nat -> Boolean 
  op numItems   : fa(a)   Map a -> Nat

  op compose    : Map Nat * Map Nat -> Map Nat

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
