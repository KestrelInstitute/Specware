FSet qualifying spec

  (* Here we refine proto-sets to be finite sets and we add a few ops that are
  specific to finite sets and do not apply to infinite sets.

  The spec imported by the following `import' is constructed from spec
  `ProtoSets' as follows: (1) rename type `PSet' to `FSet'; (2) substitute
  spec `ProtoSetsParameter' with spec `ProtoSetsInstantiationFinite'; and (3)
  rename qualifier `PSet' to `FSet'. *)

  import translate (translate ProtoSets by {PSet +-> FSet})
                   [morphism ProtoSetsParameter ->
                             ProtoSetsInstantiationFinite
                             {protoSetPredicate? +-> protoSetPredicate?}]
                   by {PSet._ +-> FSet._}

  op size : [a] FSet a -> Nat
  def [a] size =
    the (fn (size : FSet a -> Nat) ->
      (size empty = 0) &&
      (fa(s,x) size (s with x) = 1 + size (s wout x)))

  (* In order to fold over a set, we need the folding function to be
  insensitive to order (a kind of commutativity property). It is not necessary
  that it is also insensitive to repetitions (a kind of idempotence), because
  we can remove elements from the set as we fold. It is also not
  necessary that the function is commutative on its whole domain: it is
  sufficient that it is commutative on the elements of the set that we are
  folding over. Thus, below is the weakest requirement for folding. *)

  op foldable? : [a,b] FSet a * b * (b * a -> b) -> Boolean
  def [a,b] foldable?(s,c,f) =
    (fa (x:a, y:a, z:b) x in? s && y in? s => f(f(z,x),y) = f(f(z,y),x))

  op fold : [a,b] ((FSet a * b * (b * a -> b)) | foldable?) -> b
  def [a,b] fold =
    the (fn (fold : ((FSet a * b * (b * a -> b)) | foldable?) -> b) ->
      (fa(c,f) fold (empty, c, f) = c) &&
      (fa(s,x,c,f) foldable? (s with x, c, f) =>
                   fold (s with x, c, f) = f (fold (s wout x, c, f), x)))

endspec
