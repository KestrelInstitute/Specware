IntegerSet qualifying spec {
  import SplaySet

  sort Set = SplaySet.Set Integer

  op empty         : Set
  op difference    : Set * Set -> Set
  op add           : Set * Integer -> Set
  op addList       : Set * List Integer -> Set
  op member        : Set * Integer -> Boolean
  op fromList      : List Integer -> Set
  op isEmpty       : Set -> Boolean
  op listItems     : Set -> List Integer
  op union         : Set * Set -> Set
  op delete        : Set * Integer -> Set
  op intersection  : Set * Set -> Set
  op numItems      : Set -> Nat
  op map           : (Integer -> Integer) -> Set -> Set
  op app           : (Integer -> ()) -> Set -> ()
  op foldr         : (Integer * Set -> Set) -> Set -> Set -> Set
  op foldl         : (Integer * Set -> Set) -> Set -> Set -> Set
  op filter        : (Integer -> Boolean) -> Set -> Set
  op exists        : (Integer -> Boolean) -> Set -> Boolean
  op find          : (Integer -> Boolean) -> Set -> Option Integer
  op equal         : Set * Set -> Boolean

  def empty          = SplaySet.empty Integer.compare
  def difference     = SplaySet.difference
  def add            = SplaySet.add
  def addList        = SplaySet.addList
  def fromList ls    = SplaySet.addList (empty, ls)
  def member         = SplaySet.member
  def isEmpty        = SplaySet.isEmpty
  def listItems      = SplaySet.listItems
  def union          = SplaySet.union
  def delete         = SplaySet.delete
  def intersection   = SplaySet.intersection
  def numItems       = SplaySet.numItems
  def map            = SplaySet.map
  def app            = SplaySet.app
  def foldr          = SplaySet.foldr
  def foldl          = SplaySet.foldl
  def filter         = SplaySet.filter
  def exists         = SplaySet.exists
  def find           = SplaySet.find
  def equal          = SplaySet.equal
}
