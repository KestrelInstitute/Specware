(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

(* We next choose an algorithm theory to apply.  Most sorting algorithm
correspond to different instantiations of a divide-and-conquer template or
scheme.  Here we interpret the DC_01 scheme by choosing a simple
decomposition of the input type Bag: a bag is either empty or destructs
into a pair consisting of an arbitrary element and the rest of the bag.
Given this choice we can calculate the composition specifications.  For
example, we calculate as follows using the axiom Soundness1:

Assume:  
  0. ~(bagof x0 = empty_bag)                     % I1(x0)
  1. bagof x0 = bag_insert(e, bagof x1)          % O_D1(x0,e,x1)
  2. (bagof x1 = L2B z1) && ordered?(z1)         % sorted?(x1,z1)

Find a {z0,e,z1}-sufficient condition of:
  (bagof x0 = L2B z0) && ordered?(z0)

=  { apply assumption 1 }

  (bag_insert(e, bagof x1) = L2B z0) && ordered?(z0)

=  { apply assumption 2 }

  (bag_insert(e, L2B z1) = L2B z0) && ordered?(z0)

which is a necessary and sufficient condition expressed over the variables
 {z0,e,z1}.  We take this (plus the assumption ordered?(z1)) as O_C1:

  ordered?(z1) => (bag_insert(e, L2B z1) = L2B z0) && ordered?(z0)

which specifies the insert function.  See References for more detail and
other similar calculations.

*)

Sorting_as_DC = spec
  import Sorting

% destruct a bag which is empty
  op I0(x0:coBagNat):Boolean = (bagof x0 = empty_bag)
  op O_D0(x0:coBagNat):Boolean = I0 x0

% destruct a nonempty bag
  op I1(x0:coBagNat):Boolean = ~(bagof x0 = empty_bag)
  op O_D1(x0:coBagNat,e:Nat,x1:coBagNat):Boolean =
        ( bagof x0 = bag_insert(e, bagof x1) )

% calculated specifications for composition functions
  op O_C0(z0:List Nat):Boolean = (z0 = Nil)
  op O_C1(z0:ListNat,e:Nat,z1:ListNat | ordered? z1):Boolean = 
        (ordered? z0  && L2B z0 = bag_insert(e, L2B z1))

  op measure(x:coBagNat):Nat = bag_size (bagof x)
end-spec


asInsertionSort = morphism DC#DC_01 -> Sorting_as_DC
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
            }

InsertionSort = DC#DC_01_scheme[asInsertionSort]



(* ----------------------- Observer Refinement ------------------------------------

Now we apply a refinement transformation that implements our observer bagof
in terms of lists.  

       refine bagof : coBagNat -> Bag Nat
       to     listof: coBagNat -> ListNat
       via    listof xs = L2B (bagof xs)

*)

IS_list_pre = spec
  import translate InsertionSort by {F +-> insertSort}
  op listof: coBagNat -> ListNat
  axiom bagof_as_listof is
     fa(xs:coBagNat) bagof xs = L2B (listof xs)
end-spec

IS_list = transform IS_list_pre by
            {trace on;
             implement(bagof, bagof_as_listof)
                      [rl _.L2B_Nil,
                       rl _.L2B_nonempty,
                       rl _.L2B_Cons,
                       rl _.L2B_length,
                       rl _.L2B_delete1,
                       rl _.L2B_member, 
                       lr _.L2B_head,
                       lr _.L2B_tail,
                       rl _.L2B_concat
                       ]}

(* ----------  simple optimizations ----------------------------------
We now apply some simple optimizations to get more localized code
by unfolding definitions.
*)

IS1_pre = spec
   import IS_list
   theorem Cons_to_destructor is [a]
     fa(x:List a, e:a, y:List a) (x = e::y)  = (e = head x && y = tail x)
end-spec

IS1 = transform IS1_pre by
           {trace on
           ; at C0 {unfold O_C0}
           ; at C1 {unfold O_C1}
           ; at D1 { unfold O_D1
                   ; unfold I0
                   ; unfold measure
                   ; unfold measure
                   ; move [s "length"] 
                   ; simplify 
                   ; move [r "&&"] 
                   ; lr _.length_of_Cons
                   ; lr _.simplify_gt1
                   ; SimpStandard
                   ; lr Cons_to_destructor
                   }
           }
               
(* -------------- Synthesize subalgorithms --------------------------------

Here we manually introduction code to implement the two composition
 operators whose specification we calculated above. The insert operator can
 itself be synthesized using the D&C strategy.
*)

IS2 = spec
  import IS1

  op insert(e: Nat, z1: ListNat | ordered? z1): 
           {z0: ListNat | ordered? z0 
                        && L2B z0 = Bag.bag_insert(e, L2B z1)} =
           case z1 of
             | Nil         -> e :: Nil
             | Cons(e',z2) -> (if e < e'
                               then e  :: insert(e', z2)
                               else e' :: insert(e, z2))

  refine def C0: {z: ListNat | z = []} = Nil
  refine def C1 (e: Nat, z1: ListNat | ex(x1: coBagNat) sorted2?(x1, z1)): 
                {z0: ListNat | ordered? z0 && L2B z0 = Bag.bag_insert(e, L2B z1)} =
             insert(e,z1)
end-spec

(* ------------------ Define the coinductive type ----------------

The finalizeCoType transformation generates a definition for a 
coinductive type, as a record structure.
*)

IS3 = transform IS2 by {finalizeCoType(coBagNat)}


(*  ------------ eliminate the cotype ----------------------------

Next we unwrap the cotype to define Isort : List Nat -> List Nat.
The result will be:

 op Isort (xs: List(Nat)): List(Nat)
    = if xs = [] then Nil else insert(head xs, Isort(tail xs))

*)

IS4 = spec
   import IS3
   op Isort(xs:List Nat):List(Nat) = insertSort({listof = xs})
end

IS5 = transform IS4 by
          {at Isort
             {unfold insertSort;
              unfold C0;
              unfold C1;
              unfold I0; 
              unfold D1;
              unfold listof;
              unfold listof;
              SimpStandard;
              fold Isort
              }}
            


(*   ------------------- Slicing ---------------------------------

As a final step, we slice away all support types and functions except 
those needed by the Isort algorithm.

gen-lisp runs sliceSpecForLisp after doing such substitutions,
so we could omit this here.
*)


ISort = transform IS5 by {genLisp ([Isort],  "isort", true)}


