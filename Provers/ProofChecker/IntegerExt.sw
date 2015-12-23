(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* This spec is copied from Specware4/Library/Unvetted. It is copied, as
opposed to just referenced, for stability: specs under Unvetted may change at
any time (see README under that directory). Eventually, when this spec becomes
part of the standard library (i.e. it is moved from Unvetted to some other
directory), this copy can be replaced by a reference to the (stable) library
spec. *)



(*
2005:03:18
AC
Extension of the base spec Integer with exponentiation and ops for min/max of
sets as well as minimizers/maximizers of Int valued functions.

2005:05:06
AC
Adapted spec to 'the' being now built-in.

ISSUE:
The notion of min/max(imizers) should be factored in a more general spec for
orders.

*)


Integer qualifying spec


  import /Library/General/Set


  % integer is minimum in set:
  op isMinIn infixl 20 : Int * Set Int -> Bool
  def isMinIn (i,s) = i in? s && (fa(i1) i1 in? s => i <= i1)

  % set of integers has minimum:
  op hasMin? : Set Int -> Bool
  def hasMin? s = (ex(i) i isMinIn s)

  % min integer in set:
  op minIn : (Set Int | hasMin?) -> Int
  def minIn s = the(i) i isMinIn s


  % integer is maximum in set:
  op isMaxIn infixl 20 : Int * Set Int -> Bool
  def isMaxIn (i,s) = i in? s && (fa(i1) i1 in? s => i >= i1)

  % set of integers has maximum:
  op hasMax? : Set Int -> Bool
  def hasMax? s = (ex(i) i isMaxIn s)

  % max integer in set:
  op maxIn : (Set Int | hasMax?) -> Int
  def maxIn s = the(i) i isMaxIn s


  % value minimizes integer-valued function in set:
  op minimizes? : [a] a -> (a -> Int) -> Set a -> Bool
  def minimizes? x f s = (x in? s && (fa(x1) x1 in? s => f x <= f x1))

  % minimizers of function in set:
  op minimizers : [a] (a -> Int) -> Set a -> Set a
  def minimizers f s = (fn x -> minimizes? x f s)

  % value uniquely minimizes integer-valued function in set:
  op uniquelyMinimizes? : [a] a -> (a -> Int) -> Set a -> Bool
  def uniquelyMinimizes? x f s = x onlyMemberOf (minimizers f s)

  % integer-valued function has unique minimizer in set:
  op hasUniqueMinimizer? : [a] (a -> Int) -> Set a -> Bool
  def hasUniqueMinimizer? f s = single? (minimizers f s)

  % unique minimizer of integer-valued function in set:
  op minimizer : [a]
     {(f,s) : (a -> Int) * Set a | hasUniqueMinimizer? f s} -> a
  def minimizer(f,s) = theMember (minimizers f s)


  % value maximizes integer-valued function in set:
  op maximizes? : [a] a -> (a -> Int) -> Set a -> Bool
  def maximizes? x f s = (x in? s && (fa(x1) x1 in? s => f x >= f x1))

  % maximizers of function in set:
  op maximizers : [a] (a -> Int) -> Set a -> Set a
  def maximizers f s = (fn x -> maximizes? x f s)

  % value uniquely maximizes integer-valued function in set:
  op uniquelyMaximizes? : [a] a -> (a -> Int) -> Set a -> Bool
  def uniquelyMaximizes? x f s = x onlyMemberOf (maximizers f s)

  % integer-valued function has unique maximizer in set:
  op hasUniqueMaximizer? : [a] (a -> Int) -> Set a -> Bool
  def hasUniqueMaximizer? f s = single? (maximizers f s)

  % unique maximizer of integer-valued function in set:
  op maximizer : [a]
     {(f,s) : (a -> Int) * Set a | hasUniqueMaximizer? f s} -> a
  def maximizer(f,s) = theMember (maximizers f s)

endspec
