IntegerSet qualifying spec {
  import SplaySet

  sort IntegerSet.Set = SplaySet.Set Integer

  op empty         : IntegerSet.Set
  op difference    : IntegerSet.Set * IntegerSet.Set -> IntegerSet.Set
  op add           : IntegerSet.Set * Integer -> IntegerSet.Set
  op addList       : IntegerSet.Set * List Integer -> IntegerSet.Set
  op member        : IntegerSet.Set * Integer -> Boolean
  op fromList      : List Integer -> IntegerSet.Set
  op isEmpty       : IntegerSet.Set -> Boolean
  op listItems     : IntegerSet.Set -> List Integer
  op union         : IntegerSet.Set * IntegerSet.Set -> IntegerSet.Set
  op delete        : IntegerSet.Set * Integer -> IntegerSet.Set
  op intersection  : IntegerSet.Set * IntegerSet.Set -> IntegerSet.Set
  op numItems      : IntegerSet.Set -> Nat
  op map           : (Integer -> Integer) -> IntegerSet.Set -> IntegerSet.Set
  op app           : (Integer -> ()) -> IntegerSet.Set -> ()
  op foldr         : (Integer * IntegerSet.Set -> IntegerSet.Set) -> IntegerSet.Set -> IntegerSet.Set -> IntegerSet.Set
  op foldl         : (Integer * IntegerSet.Set -> IntegerSet.Set) -> IntegerSet.Set -> IntegerSet.Set -> IntegerSet.Set
  op filter        : (Integer -> Boolean) -> IntegerSet.Set -> IntegerSet.Set
  op exists        : (Integer -> Boolean) -> IntegerSet.Set -> Boolean
  op find          : (Integer -> Boolean) -> IntegerSet.Set -> Option Integer
  op equal         : IntegerSet.Set * IntegerSet.Set -> Boolean

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
