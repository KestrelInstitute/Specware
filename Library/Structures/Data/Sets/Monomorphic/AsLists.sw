(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

\section{Mono Sets as instances of Poly Lists}

This is a hopelessly naive implementation of monomorphic Sets as instances
of polymorphic Lists. Very naughty.

\begin{spec}
spec
  import PolySet qualifying ../Polymorphic/AsLists
  import ../Monomorphic

  type Set = PolySet.Set Elem

  def empty? = PolySet.empty?
  def empty = PolySet.empty
  def member? = PolySet.member?
  def subset? = PolySet.subset?
  def delete = PolySet.delete
  def insert = PolySet.insert
  def fold = PolySet.fold
  def map = PolySet.map
  def singleton = PolySet.singleton
  def union = PolySet.union
  def toList = PolySet.toList
  % def takeOne = PolySet.takeOne
endspec
