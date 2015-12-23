(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
   This specification introduces notation for fixpoints of a (monotone) endofunction.

   Note that this spec is parametric on a partial order, which is
   sufficient to establish that lfp/gfp is a function when the partial
   order is finite.  It should be extended to a cpo (or complete
   lattice) to handle assure existence and uniqueness for infinite
   orders (ala Tarski's Theorem).  Also we need to add condition that
   F is increasing at the initial point (which requires a dependent
   type).

   These iterators can be thought of as analogous to list_fold,
   bag_fold, and set_fold: they are higher-order functions that serve
   as specialized loop structures.  One key advantage is that they
   finesse the issue of nondeterministic choice of an element from a
   set.  Also, there are probably good fusion laws we can apply, and
   other kinds of laws.

*)

spec 
  import PartialOrder#MonotoneFn

%  op lfp : A -> {f:A->A | monotone f} -> A 
%  op lfp : {(a,f):A * (A->A) | monotone f && a<=f(a)} -> A
%  op lfp : (A * (A->A) | fn(a,f) -> monotone f && a<=f(a)) -> A

  op clfp (a:A, F:A->A | monotone F && a<=F(a)): A =
     the (b)( a<=b 
               && F(b)=b 
               && (fa(c:A)(a<=c && F(c)=c => b<=c)))

(*  we need to introduce a new monotone function 


*)

end

