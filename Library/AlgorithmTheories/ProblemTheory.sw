(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*******************************************************************
			   Problem Theories (uncurried)
********************************************************************)


(* ------------------  Basic Problem Theory  --------------------- *)

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
 % op f : D -> Option R
 % axiom correctness_of_f is 
 %   fa(x:D) case f(x) of
 %            | Some z -> O(x, z)
 %            | None   -> fa(y:R) ~(O(x,y))
 end-spec

DROfTotal = spec
 import DRO
 op f (x:D):{z:R | O(x,z)}
 % op f : D -> R
 % axiom correctness_of_f is 
 %  fa(x:D,z:R) (z=f(x) => O(x, z))
 end-spec

(* finding all feasible solutions *)

DROf_All = spec
 import DRO
 import /Library/DataStructures/Sets
  op f_all: D -> Set(R)
  axiom correctness_of_f_all is
     fa(x:D, y:R) (y in? f_all(x) <=> O(x, y))
 end-spec


(* ----------------------  Pi1 Problem Theory ------------------- *)

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

(* finding one optimal solution for a Pi1 problem *)

Pi1PTopt1 = spec
 import DRO
 op cost : D * R -> Nat
 op O2 : D * R * D * R -> Bool
 def O2(x1,z1,x2,z2) = (O(x1,z1) && O(x2,z2) && x1=x2
		        => cost(x1,z1) <= cost(x2,z2))
 op f : D -> R
 axiom correctness_of_f is 
   fa(x1:D,z1:R) fa(x2:D,z2:R)
     (z1=f(x1) 
      => O(x1,z1) 
         && ( x1=x2 && O(x2,z2) 
	    => cost(x1,z1) <= cost(x2,z2)))
 end-spec

(* Optimization Problems are a refinement of Pi1 Problems *)

Pi1PTf1_to_Pi1PTopt1 = morphism  Pi1PTf1 -> Pi1PTopt1
  { D +-> D,
    R +-> R,
    O2 +-> O2,
    f +-> f
  }


