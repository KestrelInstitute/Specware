(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
	
     This specification introduces notation for fixpoints of a
     monotone endofunction on a partial order.

     Issues:
       - do we need a polymorphic version?
*)

spec 
	import PartialOrder#MonotoneFn
	op F: A -> A
	axiom F_is_monotone is 
           (monotone F)

(* fixpoints above/below a given element of A *)

	op lfp : fa(A) A* (A->A) -> A 
	op gfp : fa(A) A* (A->A) -> A 

%	axiom least_fixpoint_above_w is  
%	 lfp(w,f)=a => (w<=a && f(a,w)=a && fa(b)(w<=b && fp(b,w)=b => a <= b))

%        theorem Tarksi0 is  % first approx, needs other conditions
%          fa(f:A->A, w:A)( monotone f
%                           && increasing f w
%                           => (ex (a:A)(lfp(w,f)=a)) )

%	axiom greatest_fixpoint_below_w is
%	 gfp(w,f)=b => (b<=w && f(w,b)=b && fa(a)(a<=w && fp(w,a)=a => a <= b))

% The predicate isLeast? can be used to specify a least element of a set.
% Setting the predicate to be the fixpoint test f(x)=x or f(x) subset x,
% we can specify a problem for which fixpoint iteration is a solver.
% Restricting to finite sets, Tarski's theorem justifies existence
% and the Kleene Theorem guarantees finite convergence.

% decides if z is the least A element above w that satisfies predicate p
   def isLeast?(w:A)(p:A -> Bool)(z:A):Bool
      = w<=z && p(z) && (fa(y:A)(w<=y && p(y) => z<=y))

   op least(w:A)(p:A -> Bool):A 
   axiom spec_of_least is 
       fa(w:A,p:A ->Bool,z:A)
         (least w p = z => isLeast? w p z)

end
