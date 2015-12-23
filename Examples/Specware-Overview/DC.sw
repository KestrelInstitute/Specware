(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* 

  This is simple singleton-split D&C theory.
  Instances include Insertion Sort, Selection Sort, MaxSegSum

The specification starts by importing basic problem theory DRO,
which characterizes problems in terms of 
   D - input type, the given data
   R - output type, the results
   O - satisfaction predicate, which decides when an output z:R is acceptable
       with respect to input instance x:D.

Interpreting these symbols into a problem domain gives us enough
information to specify a problem-solver:

  op f(x:D):{z:R | O(x,z)}

although this function spec is not part of DRO itself.  DRO is so
simple as to seem vacuous, but it allows us to specify abstract
algorithms, such as divide-and-conquer, that solve a given problem
without concern for the details of a concrete problem.

Each divide-and-conquer theory corresponds to a particular signature
for the (co)algebras on its input and output types.  A
divide-and-conquer solver is essentially a homomorphism from the input
type to the output type.

DC_01 is based on the signature implicit in the type functor
    F(T) = 1 + E*T,
for auxilliary type E.

The input type is treated as coinductive (based on destructors);
The output type is treated as inductive (based on constructors).

DC_01 specifies the problem structure that is sufficient to justify a
divide-and-conquer solution to the given problem.  DC_01_scheme then
provides a schematic solver algorithm and specifications for
subalgorithms.  The hard work in applying D&C theory is constructing a
morphism from DC_01 to the problem domain.  In the references, we use
deductive calculation to perform key parts of the construction.  Once
a morphism from DC_01 has been built, the instantiation of the
algorithm scheme in DC_01_scheme is an automatic pushout/substitution
operation.

We construct a morphism (interpret) from DC_01 by either 

(1) selecting a library coalgebra (destructor set) for input type D
and then calculate a algebra (constructor set) for output type R,

or, conversely,

(2) selecting a library algebra (constructor set) for output type R
and then calculate a coalgebra (destructor set) for input type D.

*)

DC_01 = spec 
 import /Library/AlgorithmTheories/ProblemTheory#DRO 
 type E   % auxilliary type

 op I0: D -> Boolean  % precondition for destructor D0
 op O_D0: D -> Boolean
 op O_C0: R -> Boolean

 op I1: D -> Boolean  % precondition for destructor D1
 op O_D1: D * E * D -> Boolean
 op O_C1: R * E * R -> Boolean

% use a Nat-valued measure to assure well-founded recursion
 op measure: D -> Nat

 axiom Soundness0 is
   fa(x:D,z:R) I0(x) && O_D0(x) && O_C0(z) => O(x,z) 
 axiom Soundness1 is
   fa(x0:D,e:E,x1:D)
   fa(z0:R,z1:R) 
   I1(x0)
   && O_D1(x0,e,x1) 
   && O(x1, z1) 
   && O_C1(z0,e,z1)
   => O(x0,z0) 

 end-spec

DC_01_scheme = spec 
  import DC_01

% empty/constant case

  % op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split
  op D1(x0:D | I0 x0):
      {(e,x1):E*D | O_D1(x0,e,x1)
                  && measure x0 > measure x1}
  op C1(e:E,z1:R | ex(x1:D) O(x1,z1)): 
       {z0:R | O_C1(z0, e, z1)}


% D&C scheme
  op F: D->R
  def F(x:D) =
     if I0(x) then C0
     else let (e,x1) = D1(x) in
             C1(e, F x1)
 
  theorem correctness_of_F is fa(x:D) O(x, F x)
 
end-spec


(* ===================================================================

  This is simple binary-split D&C theory.
  Instances include MergeSort, QuickSort, MaxSegSum

DC_012 is based on the signature implicit in the type functor
    F(T) = 1 + E + T*T,
for auxilliary type E.

The input type is treated as coinductive (based on destructors);
The output type is treated as inductive (based on constructors).

DC_012 specifies the problem structure that is sufficient to justify a
divide-and-conquer solution to the given problem.  DC_012_scheme then
provides a schematic solver algorithm and specifications for
subalgorithms.  The hard work in applying D&C theory is constructing a
morphism from DC_012 to the problem domain.  In the references, we use
deductive calculation to perform key parts of the construction.  Once
a morphism from DC_012 has been built, the instantiation of the
algorithm scheme in DC_012_scheme is an automatic pushout/substitution
operation.

We construct a morphism (interpret) from DC_012 by either 

(1) selecting a library coalgebra (destructor set) for input type D
and then calculate a algebra (constructor set) for output type R,

or, conversely,

(2) selecting a library algebra (constructor set) for output type R
and then calculate a coalgebra (destructor set) for input type D.

*)

DC_012 = spec 
 import /Library/AlgorithmTheories/ProblemTheory#DRO
 type E

% decompose an input into the unit constant
 op I0: D -> Boolean     % precondition for destructor D0
 op O_D0: D -> Boolean
 op O_C0: R -> Boolean

% decompose an input into a single auxilliary element
 op I1: D -> Boolean     % precondition for destructor D1
 op O_D1: D * E -> Boolean
 op O_C1: R * E -> Boolean

% decompose an input into two subinputs
 op I2: D -> Boolean      % precondition for destructor D2
 op O_D2: D * D * D -> Boolean
 op O_C2: R * R * R -> Boolean

% use a Nat-valued measure to assure well-founded recursion
 op measure: D -> Nat

 axiom Soundness0 is
   fa(x:D,z:R) I0(x) && O_D0(x) && O_C0(z) => O(x,z) 
 axiom Soundness1 is
   fa(x:D,e:E,z:R) I1(x) && O_D1(x,e) && O_C1(z, e) => O(x,z) 
 axiom Soundness2 is
   fa(x0:D,x1:D,x2:D)
   fa(z0:R,z1:R,z2:R) 
   I2(x0)
   && O_D2(x0,x1,x2) 
   && O(x1, z1) && O(x2, z2) 
   && O_C2(z1, z2, z0)
   => O(x0,z0) 

 end-spec


DC_012_scheme = spec 
  import DC_012

% empty/constant case
% op D0(x0:D | I0 x0): ()
  op C0:{z:R | O_C0 z}

% singleton split
  op D1(x0:D | I1 x0):{e:E | O_D1(x0,e)}
  op C1(e:E): {z0:R | O_C1(z0, e)}

% binary split case, also need wfo
  op D2(x0:D | I2 x0):
       {(x1,x2):D*D | O_D2(x0,x1,x2)
                    && measure x0 > measure x1
                    && measure x0 > measure x2
       }
  op C2(z1:R,z2:R): {z0:R | O_C2(z0, z1,z2)}

% D&C scheme
  def F(x) =
     if I0(x) then C0
     else if I1(x) then C1(D1(x))
     else let x1x2 = D2(x) in
             C2(F(x1x2.1), F(x1x2.2))
 
  theorem correctness_of_F is fa(x:D) O(x, F(x))
 
end-spec

(*   References

Smith, D.R., The Design of Divide and Conquer Algorithms, Science of
Computer Programming 5,1(1985), 37-58.

Smith, D.R., Top-Down Synthesis of Divide-and-Conquer Algorithms,
Artificial Intelligence 27,1(1985), 43-96 (reprinted in {\em Readings
in Artificial Intelligence and Software Engineering}, Eds. C. Rich and
R. Waters, Morgan Kaufmann Pub. Co., Los Altos, CA, 1986, 35-61).

Smith, D.R., Applications of a Strategy for Designing
Divide-and-Conquer Algorithms, Science of Computer Programming 8,
3(1987), 213-229.

Smith, D.R., Constructing Specification Morphisms, Journal of Symbolic
Computation, Special Issue on Automatic Programming, Vol 16, No 5-6,
1993, 571-606.

Douglas R. Smith, Model Refinement: Calculating Refinements in
Algorithm and System Design, Technical Report, Kestrel Institute,
April 2009.

*)

