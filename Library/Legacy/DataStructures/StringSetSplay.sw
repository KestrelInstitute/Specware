StringSet qualifying spec { 
  import SplaySet   

  sort Set = SplaySet.Set String

  op empty         : Set
  op difference    : Set * Set -> Set
  op add           : Set * String -> Set
  op addList       : Set * List String -> Set
  op member        : Set * String -> Boolean
  op fromList      : List String -> Set
  op toList        : Set -> List String
  op isEmpty       : Set -> Boolean
  op listItems     : Set -> List String
  op union         : Set * Set -> Set
  op intersection  : Set * Set -> Set
  op map           : (String -> String) -> Set -> Set
  op app           : (String -> ()) -> Set -> ()

  def empty          = SplaySet.empty String.compare
  def difference     = SplaySet.difference
  def add            = SplaySet.add
  def addList        = SplaySet.addList
  def fromList ls    = SplaySet.addList (empty, ls)
  def toList         = SplaySet.listItems
  def member         = SplaySet.member
  def isEmpty        = SplaySet.isEmpty
  def listItems      = SplaySet.listItems
  def union          = SplaySet.union
  def intersection   = SplaySet.intersection
  def map            = SplaySet.map
  def app            = SplaySet.app
}

