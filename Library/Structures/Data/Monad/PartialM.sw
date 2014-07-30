(* The partiality monad: for computations with full recursion *)

PartialM = Monad qualifying spec

  % A computation of type a in PartialM is, intuitively, an object of
  % type a that is defined by a fixed-point. All we can ask of such a
  % computation is whether it is defined after the nth step of
  % iterating the fixed-point. Once it has become defined, however,
  % iterating the fixed-point any more times keeps the same value.
  type Monad a = { f : Nat -> Option a
                    | fa (n1,n2) n1 <= n2 => f n2 = f n1 || f n1 = None }

  op [a] return (x:a) : Monad a = fn _ -> Some x

  op [a,b] monadBind: (m: Monad a, f:a -> Monad b) : Monad b =
    fn n -> case m n of
              | Some x -> f x n
              | None -> None

  op [a,b] MonadTrans.monadSeq (m1:MonadTrans.Monad a, m2:MonadTrans.Monad b) : MonadTrans.Monad b =
    MonadTrans.monadBind (m1, fn _ -> m2)


  % Monad axioms

  theorem left_unit  is [a,b]
    fa (f: a -> Monad b, x: a) monadBind (return x, f) = f x

  theorem right_unit is [a]
    fa (m: Monad a) monadBind (m, return) = m

  theorem associativity is [a,b,c]
    fa (m: Monad a, f: a -> Monad b, h: b -> Monad c)
      monadBind (m, fn x -> monadBind (f x, h)) = monadBind (monadBind (m, f), h)

  theorem non_binding_sequence is [a]
    fa (f :Monad a, g: Monad a)
    monadSeq (f, g) = monadBind (f, fn _ -> g)


  % Proofs

  proof Isa non_binding_sequence
    by (simp add: Monad__monadSeq_def)
  end-proof


end-spec
