(* Copyright 2018 Kestrel Institute. See file LICENSE for license details *)

(*******************************************************************
			   Problem Theories (uncurried)
********************************************************************)


(* ------------------  Basic Problem Theory  ---------------------

    The intent is to capture the abstract structure of problems that
    can be solved by a function and for which the acceptability of an
    output only depends on the input.  This is a specialization of the
    notion of a system property, defined as a predicate that defines
    acceptable behaviors.  Here an acceptable behavior is just an I/O
    pair.  Generalizations can be defined to handle global properties
    (see below), properties, and hyper-properties.

*)

DRO = spec
 type D
 type R
 op O : D * R -> Bool
 end-spec

(* finding one feasible solution *)
DROfPartial = spec
 import DRO
 op f(x:D): {oz:Option R | case oz of
                            | Some z -> O(x, z)
                            | None   -> fa(y:R) ~(O(x,y))}
 end-spec

DROfTotal = spec
 import DRO
 op f (x:D):{z:R | O(x,z)}
 end-spec

(* finding all feasible solutions *)
DROf_All = spec
 import DRO
 import /Library/DataStructures/Sets
  op f_all: D -> Set(R)
  axiom correctness_of_f_all is
     fa(x:D, y:R) (y in? f_all(x) <=> O(x, y))
 end-spec


(* ----------------------  Pi1 Problem Theory -------------------

     This is a generalization of DRO theory in which the acceptability
     of an output for one input can depend on the outputs for other
     inputs.  Special cases include: (1) finding an optimal cost
     feasible solution, (2) expressing global constraints on the
     target function such as injectivity or bijectivity.  This spec
     can express global constraints that can be decomposed into
     constraints on pairs of I/O pairs.

*)

Pi1PT = spec
 type D
 type R
 op O2 : D * R * D * R -> Bool
 end-spec

(* finding one feasible solution for a Pi1 problem *)

Pi1PTf1 = spec
 import Pi1PT
 op f : D -> R
 axiom correctness_of_f is
   fa(x1:D,z1:R) fa(x2:D,z2:R) (z1=f(x1) =>  O2(x1, z1, x2,z2))
 end-spec

DROOpt = spec
 import DRO, translate ../Math/LinearOrder by {A +-> Nat}
 op cost : D * R -> Nat
 end-spec

(* finding one optimal solution *)

DROfOpt = spec
 import DROOpt
 op O2 : D * R * D * R -> Bool
 def O2(x1,z1,x2,z2) = (O(x1,z1) && O(x2,z2) && x1=x2
		        => cost(x1,z1) <= cost(x2,z2))
 op f : D -> R
 axiom correctness_of_f is
   fa(x1:D,z1:R) fa(x2:D,z2:R)
     z1=f(x1) => O2(x1, z1, x2, z2)
 end-spec

(* Optimization Problems are a refinement of Pi1 Problems *)

Pi1PTf1_to_DROfOpt = morphism  Pi1PTf1 -> DROfOpt
  { D +-> D,
    R +-> R,
    O2 +-> O2,
    f +-> f
  }

(* specifying an injective function *)

DROfInj = spec
 import DROOpt
 op O2 : D * R * D * R -> Bool
 def O2(x1,z1,x2,z2) = (O(x1,z1) && O(x2,z2) && x1~=x2 => z1~=z2)
 op f : D -> R
 axiom correctness_of_f is
   fa(x1:D,z1:R) fa(x2:D,z2:R)
     z1=f(x1) && z2=f(x2) => O2(x1, z1, x2, z2)
 end-spec
