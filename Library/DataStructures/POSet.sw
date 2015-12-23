(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
                    Specification of Partially Ordered Set (poset)

%%TODO This comments seems misplaced:
    empty_map and update could be constructors,
    but we want implementations that do destructive update
    to keep the size linear in the domain.
*)

%% Status: I made a few fixes to get this to proc again.  Not sure what it does or if it is correct or needed. -Eric, 10/11/12

spec
  import Sets
  type POSet(a)

  %u define the underlying set when you create the poset and can't change it
  op [a] newPOSet : Set a -> POSet(a)
  op [a] underlyingSet : POSet(a) -> Set(a)
  axiom newPOSet is [a]
        fa(s : Set a) underlyingSet(newPOSet(s)) = s
%
    op [a] prec? : POSet(a) -> a -> a -> Bool
    %omit reflexivity for now?
    axiom transitivity is
        fa(po,x,y,z) ((prec? po x y) && (prec? po y z) => (prec? po x z))
    axiom antisymmetry is
        fa(po,x,y) ((prec? po x y) && (prec? po y x) => x=y)
%
  op [a] immPrec? : POSet(a) -> a -> a -> Bool
  axiom immPrec? is [a]
    fa(po : POSet a, x:a, y:a, z:a) immPrec? po x y <=>
    prec? po x y && (fa(z) prec? po x z && prec? po z y => z = x || z = y)
  
  op [a] arcsOf : POSet(a) -> Set(a * a)
    axiom arcsOf is
        fa(po,x,y) immPrec? po x y <=> (x,y) in? arcsOf(po)
        
  op [a] addArc : {(po,x,y) : POSet(a) * a * a | x in? underlyingSet(po) && 
                                                 y in? underlyingSet(po) &&
                                                 ~(prec? po y x) } -> POSet(a)
  %op [a] addArc : POSet(a) -> a -> a -> POSet(a)
    axiom addArc is
    fa(po,x,y,w,z)
        (let new_po = addArc(po, w, z) in
        ((prec? po x y) => (prec? new_po x y)) && prec? new_po w z)
        %old ~ ((prec? new_po w z) && (prec? new_po w z)) &&
        %old w in? underlyingSet(new_po) && z in? underlyingSet(new_po))
%
(*  TBD
    op immPreds
    op immSuccs
    op preds
    op succs
*)

proof Isa addArc_Obligation_subtype
  sorry
end-proof

end-spec
