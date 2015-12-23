(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*

   Fixpoints of an Indexed Family of Monotone Endofunctions.

   This specification introduces notation for fixpoints of an indexed
   family of monotone endofunctions.  This generalizes the simple
   fixpoint iterator introduced in fixpoint.sw by introducing
   dependence of the montone function on other information that is
   bound at run-time.  It is not obvious how to unify these two
   theories, since a morphism can only do static/design-time binding,
   and cannot express runtime binding options except through extra
   input dependencies.

   Note that this spec is parametric on a partial order, which is
   sufficient to establish that ilfp/igfp is a function when the partial
   order is finite.  It should be extended to a cpo (or complete
   lattice) to handle assure existence and uniqueness for infinite
   orders (ala Tarski's Theorem).

   These iterators can be thought of as analogous to list_fold,
   bag_fold, and set_fold: they are higher-order functions that serve
   as specialized loop structures.  One key advantage is that they
   finesse the issue of nondeterministic choice of an element from a
   set.  Also, there are probably good fusion laws we can apply, and
   other kinds of laws.

*)

spec 
  import PartialOrder#MonotoneFn
  type I

  op ilfp : I -> A -> {f:I->A->A | fa(i:I) monotone (f i)} -> A 
  def ilfp i a f = the (b)( a<=b 
                         && (f i b)=b 
                         && (fa(c:A)(a<=c && (f i c)=c => b<=c)))

%  def ilfp i a f = the (b)( b = lfp a (f i) ) 

  op igfp :  I-> A -> {f:I->A->A | fa(i:I) monotone (f i)} -> A 

end
