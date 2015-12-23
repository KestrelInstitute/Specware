(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* 
    Synthesis of Sorting Algorithms

The first step in algorithm synthesis is to specify the problem domain.
Here we specify the problem of sorting over a collection of Natural
numbers.

One immediate question is how to specify the input and output types of a
sorting algorithm.  In anticipation of using a divide-and-conquer (D&C)
strategy, we may want to specify the input type in terms of destructors
since we will need a way to, perhaps nondeterministically, decompose the
input into solvable subparts (the divide step of D&C).

The need for nondeterministic choice over collections such as sets and
bags is possible in a purely functional setting using a coalgebraic
technique that we developed.  Here we specify the input type as a Bag
of Nats, but we treat it as a coinductive type with a single observer
that provides the bag.  We will later implement the bag as a list, but
we have the freedom to specify a nondeterministic decomposition of a
bag into parts.  One can think of the coinductive type coBagNat as the
(currently unspecified) representation of a Bag of Nats, with an
observer bagof providing the actual bag.
  
*)

Sorting = spec
  import /Library/DataStructures/StructuredTypes  % Bags, Sets, Maps plus utilities

  type coBagNat                    % cotype to allow nondeterministic decomposition
  op bagof: coBagNat -> Bag Nat    % sole observer, which will be refined to List
  
  type ListNat = List Nat
	
  def ordered?(xs:List Nat):Bool = 
    case xs of
       | Nil -> true
       | Cons(x,ys) -> ordered?_aux(x,ys)

  def ordered?_aux(a:Nat, xs:List Nat):Bool = 
    case xs of
       | Nil -> true
       | Cons(x,ys) -> (a <= x) && ordered?_aux(x,ys)


(*  an alternate logical specification of ordered?
    ordered?(xs:List Nat) = 
      fa(i:Nat, j:Nat) (0<=i && i<length(xs) && 0<=j && j<length(xs)) 
                        => i<=j => nth(xs,i) <= nth(xs,j))
*)

  op sorted2?(xsi:coBagNat, xso:List Nat):Bool = (bagof xsi = L2B xso) && ordered?(xso)
  op sortBag(xs:coBagNat):{zs:List Nat | sorted2?(xs,zs)}

end-spec

(* The next step is to view sorting as a problem: Problem Theory DRO simply
provides type symbols for the input domain (D), the output domain (R), and
the problem satisfaction condition, which is a predicate O:D*R->Bool.  A
problem is defined by the set of input-output pairs that are acceptable:
O(x,z).   

To view a problem-domain specification, such as sorting above, as a problem,
we produce a morphism from problem theory to the domain.
*)

Sorting_as_Problem = morphism /Library/AlgorithmTheories/ProblemTheory#DRO -> Sorting
            { D +-> coBagNat
            , R +-> ListNat
            , O +-> sorted2?
            }

(* We next choose an algorithm theory to apply.  Most sorting
algorithm correspond to different instantiations of a
divide-and-conquer template or scheme.  Here we interpret the DC_012
scheme by choosing a simple decomposition of the input type Bag: a bag
is either (1) empty, (2) a singleton bag, or (3) destructs into a pair
consisting of disjoint, smaller subbags.  Given this choice we can
calculate the composition specifications.  For example, we calculate
as follows using the axiom Soundness2:

Assume:  
  0. bag_size (bagof x0) > 1                     % I2(x0)
  1. bagof x0 = bagof x1 \/ bagof x2             % O_D2(x0,e,x1)
  2. (bagof x1 = L2B z1) && ordered?(z1)         % sorted?(x1,z1)
  3. (bagof x2 = L2B z2) && ordered?(z2)         % sorted?(x2,z2)

Find a {z0,z1,z2}-sufficient condition of:
  (bagof x0 = L2B z0) && ordered?(z0)

=  { apply assumption 1 }

  (bagof x1 \/ bagof x2 = L2B z0) && ordered?(z0)

=  { apply assumption 2 twice }

  (L2B z1 \/ L2B z2 = L2B z0) && ordered?(z0)

which is a necessary and sufficient condition expressed over the
 variables {z0,e,z1}.  We take this (plus the assumption ordered?(z1)
 && ordered?(z2)) as O_C2:

  ordered?(z1) && ordered?(z2) => (L2B z1 \/ L2B z2 = L2B z0) && ordered?(z0)

which specifies the merge function.  See References for more detail
and other similar calculations.

*)

Sorting_as_DC = spec
  import Sorting

% destruct a bag which is empty
  op I0(x0:coBagNat):Boolean = (bagof x0 = empty_bag)
  op O_D0(x0:coBagNat):Boolean = I0 x0

% destruct a singleton bag
  op I1(x0:coBagNat):Boolean = (bag_size (bagof x0) = 1)
  op O_D1(x0:coBagNat,e:Nat):Boolean =
        ( bagof x0 = bag_insert(e, empty_bag) )

% destruct a nonempty, nonsingleton bag
  op I2(x0:coBagNat):Boolean = (bag_size (bagof x0) > 1)
  op O_D2(x0:coBagNat,x1:coBagNat,x2:coBagNat):Boolean =
        ( bagof x0 = bagof x1 \/ bagof x2 )

% calculated specifications for the composition functions
  op O_C0(z0:List Nat):Boolean = (z0 = Nil)
  op O_C1(z0:ListNat,e:Nat):Boolean = 
         (L2B z0 = bag_insert(e, empty_bag))
  op O_C2(z0:ListNat,z1:ListNat,z2:ListNat | ordered? z1 && ordered? z2):Boolean = 
        (ordered? z0  && L2B z0 = (L2B z1 \/ (L2B z2)))

  op measure(x:coBagNat):Nat = bag_size (bagof x)

end-spec


asMergeSort = morphism DC#DC_012 -> Sorting_as_DC
            { D +-> coBagNat
            , R +-> ListNat
            , O +-> sorted2?
            , E    +-> Nat
            , I0   +-> I0
            , O_D0 +-> O_D0
            , O_C0 +-> O_C0
            , I1   +-> I1
            , O_D1 +-> O_D1
            , O_C1 +-> O_C1
            , I2   +-> I2
            , O_D2 +-> O_D2
            , O_C2 +-> O_C2
            }

MergeSort = DC#DC_012_scheme[asMergeSort]



(* ----------------------- Observer Refinement ------------------------------------

Now we apply a refinement transformation that implements our observer bagof
in terms of lists.  

       refine bagof : coBagNat -> Bag Nat
       to     listof: coBagNat -> ListNat
       via    listof xs = L2B (bagof xs)

*)

MS_list_pre = spec
  import translate MergeSort by {F +-> mergeSort}
  op listof: coBagNat -> ListNat
  axiom bagof_as_listof is
     fa(xs:coBagNat) bagof xs = L2B (listof xs)
end-spec

MS_list = transform MS_list_pre by
            {trace on;
             implement(bagof, bagof_as_listof)
                      [rl _.L2B_Nil,
                       rl _.L2B_Nil1,
                       rl _.L2B_nonempty,
                       rl _.L2B_Cons,
                       rl _.L2B_length,
                       rl _.L2B_delete1,
                       rl _.L2B_member, 
                       lr _.L2B_head,
                       lr _.L2B_tail,
                       rl _.L2B_concat
                       ]
            }

(* ----------  simple optimizations ----------------------------------
We now apply some simple optimizations to get more localized code
by unfolding definitions.
*)

MS1_pre = spec
   import MS_list
   theorem singleton_to_destructor is [a]
     fa(x:List a, e:a) (x = e::Nil)  = (e = head x)
   theorem concat_to_destructor is [a]
     fa(x:List a, y1:List a, y2:List a) 
       (  y1 = prefix(x, (length (x)) div 2)
       && y2 = suffix(x, ((length (x)) div 2) + ((length (x)) mod 2))
       => (x = y1 ++ y2))
end-spec

MS1 = transform MS1_pre by
           {trace on
           ; at C0 {unfold O_C0}
           ; at C1 {unfold O_C1}
           ; at C2 {unfold O_C2}
           ; at D1 { unfold O_D1
                   ; unfold I1
                   ; lr singleton_to_destructor
                   }
           ; at D2 { unfold O_D2
                   ; move [a]    % all should work
                   ; unfold I2
                   ; move [post]
                   ; unfold measure    % simplify away the wfo
                   ; unfold measure
                   ; unfold measure
                   ; unfold measure
                   ; move [s "length"]    %, s "length", s "length", s "length"] 
                   ; simplify 
                   ; lr _.length_of_concat
                   ; lr _.simplify_gt2                   
                   ; move n
                   ; move n
                   ; simplify
                   ; lr _.length_of_concat
                   ; lr _.simplify_gt3
                   ; lr _.simplify_gt6 
                   ; move post
                   ; lr _.simplify_gt5
                   ; strengthen concat_to_destructor
                   ; move [s "length", s "length", s "length", s "length"]
                   ; simplify
                   ; lr _.length_of_suffix
                   ; move [s "length", s "length", s "length"]
                   ; simplify
                   ; lr _.length_of_prefix
                   ; move [post]
                   ; simplify [ lr _.simplify_gt4a
                              , lr _.simplify_gt4 ]
                   }
           }
               
(* -------------- Synthesize subalgorithms --------------------------------

Here we manually introduction code to implement the three composition
 operators whose specification we calculated above. The insert operator can
 itself be synthesized using the D&C strategy.
*)

MS2 = spec
  import MS1


  refine def C0: {z: ListNat | z = []} = Nil
  refine def C1 (e: Nat):
                {z0: ListNat | L2B z0 = bag_insert(e, empty_bag)} 
                = Cons(e,Nil)
  refine def C2 (z1: ListNat, z2: ListNat): 
                {z0: ListNat | ordered? z0 && L2B z0 = L2B z1 \/ L2B z2}
                = merge(z1,z2)

  op merge(z1:ListNat, z2:ListNat | ordered? z1 && ordered? z2): 
          {z0: ListNat | ordered? z0 
                       && L2B z0 = (L2B z1 \/ L2B z2)} =
           case z1 of
             | Nil         -> z2
             | Cons(e,z1') -> (case z2 of
                               | Nil   -> z1
                               | Cons(e',z2') -> (if e < e'
                                                  then e  :: merge(z1', z2)
                                                  else e' :: merge(z1, z2')))
end-spec

(* ------------------ Define the coinductive type ----------------

The finalizeCoType transformation generates a definition for a 
coinductive type, as a record structure.
*)

MS3 = transform MS2 by {finalizeCoType(coBagNat)}


(* -------------- Synthesize decomposition subalgorithms -----------------

These def introductions should be generated by finalizeCoType, but it needs
to be extended.
*)

MS4 = spec
  import MS3
  refine def D1 (x0: coBagNat | I1 x0): {e: Nat | e = head(listof x0)}
         = head(listof x0)
  refine def D2(x0: coBagNat | I2 x0): 
               {(x1, x2): (coBagNat * coBagNat)
                | listof x1 = prefix(listof x0, length(listof x0) div 2) 
               && listof x2 = suffix(listof x0, 1 + length(listof x0) div 2)}
            = % let m = (length x0.listof) div 2 in
                ( {listof = prefix(x0.listof, (length x0.listof) div 2)},
                  {listof = suffix(x0.listof, ((length x0.listof) div 2) 
                                              + ((length x0.listof) mod 2))}
                )
end-spec


(*  ------------ Eliminate the cotype ----------------------------

Next we unwrap the cotype to define Isort : List Nat -> List Nat.
The result will be:

 op Isort (xs: List(Nat)): List(Nat)
    = if xs = [] then Nil else insert(head xs, Isort(tail xs))

*)

MS5 = spec
   import MS4
   op Msort(xs:List Nat):List(Nat) = mergeSort({listof = xs})
end

MS6 = transform MS5 by
          {at Msort
             {unfold mergeSort;
              unfold C0;
              unfold C1;
              unfold C2;
              unfold I0; 
              unfold I1;
              unfold D1;
              unfold D2;
              unfold listof;
              unfold listof;
              unfold listof;
              lr _.length_of_singleton;
              SimpStandard;
              fold Msort;
              fold Msort;
              AbstractCommonExprs
              }}
            


(*   ------------------- Slicing ---------------------------------

As a final step, we slice away all support types and functions except 
those needed by the Isort algorithm.
*)

MSort = transform MS5 by {genLisp ([Msort], "msort", true)}

