\section{Mono Sets as instances of Poly Lists}

This is a hopelessly naive implementation of monomorphic Sets as instances
of polymorphic Lists. Very naughty.

\begin{spec}
spec {
  import PolySet qualifying ../Polymorphic/AsLists
  import ../Monomorphic

  sort Set = PolySet.Set Elem

  def empty? = PolySet.empty?
  def empty = PolySet.empty
  def member? = PolySet.member?
  def delete = PolySet.delete
  def insert = PolySet.insert
  def fold = PolySet.fold
  def map = PolySet.map
  def singleton = PolySet.singleton
  def union = PolySet.union
  def toList = PolySet.toList
} 
