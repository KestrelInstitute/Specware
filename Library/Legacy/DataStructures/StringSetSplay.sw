(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

StringSet qualifying spec { 
  import SplaySet   

  type StringSet.Set = SplaySet.Set String

  op empty         : StringSet.Set
  op difference    : StringSet.Set * StringSet.Set -> StringSet.Set
  op add           : StringSet.Set * String -> StringSet.Set
  op addList       : StringSet.Set * List String -> StringSet.Set
  op member        : StringSet.Set * String -> Bool
  op fromList      : List String -> StringSet.Set
  op toList        : StringSet.Set -> List String
  op isEmpty       : StringSet.Set -> Bool
  op listItems     : StringSet.Set -> List String
  op union         : StringSet.Set * StringSet.Set -> StringSet.Set
  op intersection  : StringSet.Set * StringSet.Set -> StringSet.Set
  op map           : (String -> String) -> StringSet.Set -> StringSet.Set
  op app           : (String -> ()) -> StringSet.Set -> ()

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

