(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

IntSet qualifying spec {
  import SplaySet

  type IntSet.Set = SplaySet.Set Int

  op empty         : IntSet.Set
  op difference    : IntSet.Set * IntSet.Set -> IntSet.Set
  op add           : IntSet.Set * Int -> IntSet.Set
  op addList       : IntSet.Set * List Int -> IntSet.Set
  op member        : IntSet.Set * Int -> Bool
  op fromList      : List Int -> IntSet.Set
  op isEmpty       : IntSet.Set -> Bool
  op listItems     : IntSet.Set -> List Int
  op union         : IntSet.Set * IntSet.Set -> IntSet.Set
  op delete        : IntSet.Set * Int -> IntSet.Set
  op intersection  : IntSet.Set * IntSet.Set -> IntSet.Set
  op numItems      : IntSet.Set -> Nat
  op map           : (Int -> Int) -> IntSet.Set -> IntSet.Set
  op app           : (Int -> ()) -> IntSet.Set -> ()
  op foldr         : (Int * IntSet.Set -> IntSet.Set) -> IntSet.Set -> IntSet.Set -> IntSet.Set
  op foldl         : (Int * IntSet.Set -> IntSet.Set) -> IntSet.Set -> IntSet.Set -> IntSet.Set
  op filter        : (Int -> Bool) -> IntSet.Set -> IntSet.Set
  op exists        : (Int -> Bool) -> IntSet.Set -> Bool
  op find          : (Int -> Bool) -> IntSet.Set -> Option Int
  op equal         : IntSet.Set * IntSet.Set -> Bool

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
