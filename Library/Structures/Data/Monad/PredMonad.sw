(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

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

  axiom satisfies_monotone is [a]
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

  (* We define 'and' and 'or' via forall and exists, using the two-element type
  Bool to form 2-element "function-sets". *)
  op [a] m_and (P1 : MPred a, P2 : MPred a) : MPred a =
    mforall (fn b -> if b then P1 else P2)
  op [a] m_or (P1 : MPred a, P2 : MPred a) : MPred a =
    mexists (fn b -> if b then P1 else P2)

  theorem satisfies_and is [a]
    fa (P1,P2,m:Monad a)
      m |= m_and (P1,P2) <=> (m |= P1 && m |= P2)
  theorem satisfies_or is [a]
    fa (P1,P2,m:Monad a)
      m |= m_or (P1,P2) <=> (m |= P1 || m |= P2)


  (* The top and bottom elements correspond to "true" and "false", respectively *)
  op [a] mtrue : MPred a = mexists id
  op [a] mfalse : MPred a = mforall id

  (* The fact that true always holds and false never does is equivalent to the
  existence, for each m, of predicates that m does and does not satisfy,
  respectively. We state the latter properties as axioms, and the former follow
  from them. *)
  axiom mpred_separation is [a]
    fa (m:Monad a) ex (P1,P2) m |= P1 && ~(m |= P2)

  theorem mtrue_is_true is [a]
    fa (m:Monad a) m |= mtrue
  theorem mfalse_is_false is [a]
    fa (m:Monad a) ~(m |= mfalse)


  (* Implication makes a predicate monad into a complete Heyting algebra, which
  means there is an operation mimplies with a Galois connection with mforall.
  Note that this is weaker than making MPred a Boolean algebra, which would be
  inherently non-constructive. *)
  op [a] mimplies (P1 : MPred a, P2 : MPred a) : MPred a

  axiom mimplies_galois is [a]
    fa (P1,P2,P3:MPred a)
      mpred_leq (m_and (P1,P2), P3) <=> mpred_leq (P1, (mimplies (P2, P3)))

  (* mimplies implies implication (say that 5 times fast!), but it need not be
  equivalent to it; i.e., the predicate monad need not be as strong as the
  meta-logic in which it is formalized *)

  theorem satisfies_mimplies is [a]
    fa (P1,P2,m:Monad a)
      m |= mimplies(P1,P2) => (m |= P1 => m |= P2)


  (* Negation is just implication of false *)
  op [a] mnot (P : MPred a) : MPred a = mimplies (P, mfalse)
  theorem satisfies_mnot is [a]
    fa (m,P:MPred a) m |= P <=> ~(m |= mnot P)


  (* The return and bind of MPred recognize the return and bind of Monad *)
  axiom satisfies_return is [a]
    fa (m,x:a) m |= return x <=> m = return x
  axiom satisfies_bind is [a,b]
    fa (m,P,Q:a -> MPred b)
      (ex (m',f) m' |= P && (fa (x) f x |= Q x)) =>
      m |= monadBind (P,Q) <=>
      (ex (m',f) m' |= P && (fa (x) f x |= Q x) && m = monadBind (m',f))


  (* FIXME: need to commute return and bind with logical operators! Also need to
  lift propositions into MPred, and maybe even equality with an m *)

  (* Lift propositions to predicates (in a very non-constructive way!) *)
  op [a] liftProp (prop : Bool) : MPred a =
    if prop then mtrue else mfalse

  (* NOTE: This is how one would liftProp constructively... *)
  (*
  op [a] liftProp (prop : Prop) : MPred a =
    mexists (fn (p : prop) -> mtrue)
  *)


end-spec
