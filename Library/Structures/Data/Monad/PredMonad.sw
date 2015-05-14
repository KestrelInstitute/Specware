PredMonad qualifying spec
  import ../Monad
  import CPO % Defines relations in a way that works with most other libs...

  (* A predicate monad is a predicate over monadic computations. More
     specifically, 'PredM a' is a predicate over computations of type 'Monad a',
     where the operator |= below, pronounced "satisfies", defines the
     relationship between computations and predicates. *)
  type MPred a

  (* MPred is itself a monad *)
  op [a] return (x:a) : MPred a
  op [a,b] monadBind (P:MPred a, Q:a -> MPred b) : MPred b

  axiom left_unit  is [a,b]
    fa (Q: a -> MPred b, x) monadBind (return x, Q) = Q x
  axiom right_unit is [a]
    fa (P: MPred a) monadBind (P, return) = P
  axiom associativity is [a,b,c]
    fa (P, Q: a -> Monad b, R: b -> Monad c)
      monadBind (P, fn x -> monadBind (Q x, R)) = monadBind (monadBind (P, Q), R)


  (* The satisfaction relation *)
  op [a] |= (m: Monad a, P: MPred a) infixl 25 : Bool

  (* MPred forms a complete lattice, meaning that, for any (possibly infinite)
     set of predicates, we can take the least upper bound and the greatest lower
     bound of the set. The lattice ordering intuitively represents "less true
     than", i.e., subset of predicates.

     To represent lubs and glbs, we represent a set of predicates as a function
     whose domain can be an arbitrary type, where the set is the set of all
     return values of this function. (E.g., the empty set can be represented
     with an empty input type and the complete set can be represented with the
     id function over predicates.) Intuitively, the lub is a like an
     existential, since a computation satisfies the lub iff there exists some
     input to the set-function such that the computation satisfies the result of
     the set-function for that input. Similarly, the glb is a universal. This
     explains the naming of these ops. *)
  op [a] mpred_leq : PartialOrder (MPred a)
  op [a,b] mforall : (a -> MPred b) -> MPred b
  op [a,b] mexists : (a -> MPred b) -> MPred b

  axiom satisfaction_monotone is [a]
    fa (P1,P2,m:Monad a) mpred_leq (P1,P2) => m |= P1 => m |= P2
  axiom mforall_lower_bound is [a,b]
    fa (Q:a -> MPred b, x) mpred_leq (mforall Q, Q x)
  axiom mforall_greatest_lower_bound is [a,b]
    fa (P,Q:a -> MPred b)
      (fa (x) mpred_leq (P, Q x)) => mpred_leq (P, mforall Q)
  axiom mexists_upper_bound is [a,b]
    fa (Q:a -> MPred b, x) mpred_leq (Q x, mexists Q)
  axiom mexists_least_upper_bound is [a,b]
    fa (P,Q:a -> MPred b)
      (fa (x) mpred_leq (Q x, P)) => mpred_leq (mexists Q, P)


  (* FIXME: define the interaction between the monad ops and the logical ops *)

  (* The top and bottom elements correspond to "true" and "false", respectively *)
  op [a] mtrue : MPred a = mexists id
  op [a] mfalse : MPred a = mforall id

  (* FIXME: do these need to be axioms? *)
  theorem mtrue_is_true is [a]
    fa (m:Monad a) m |= mtrue
  theorem mfalse_is_false is [a]
    fa (m:Monad a) ~(m |= mfalse)

end-spec
