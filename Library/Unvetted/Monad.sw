(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
2005:03:16
LM
This is meant as a possible replacement for the spec at
  Library/Structures/Data/Monad.sw
Its natural place is at
  Library/CategoryTheory/Monad

This spec introduces ops monadBind, monadSeq and return,
the first two of which are employed by the translation
of Metaslang monadic-expressions like {x <- y; y <- z; p x}
Note that monadSeq is defined here; the user of this spec
needs to supply definitions for Monad, monadBind and return.
Additionally, this spec introduces AND defines Kleisli type
Arrow and op o ("Kleisli composition"), and Monad ops map
-- the "action on arrows" of the functor Monad -- and flatten
(generalization of List.flatten and Set.\\//)

Note that the "inner spec" is just the most basic way of
saying: some category whose objects are types.  It could be
extracted as a spec in its own right and then be imported.

Caveat Emptor: the spec has not been "tested" -- whatever that
means...

2005:03:18
LM
Added clarifying comments about the role of the conjectures

*)

Monad qualifying spec

  type Monad a

  import translate Kleisli qualifying spec

    type Arrow(a,b)

    op id : [a] Arrow(a,a)

    op o infixl 24 : [a,b,c] Arrow(b,c) * Arrow(a,b) -> Arrow(a,c)

    % The following conjectures should morally be axioms.
    % The point is that this spec is meant to be imported
    % (indirectly) in specs defining specific monads by
    % supplying definitions for Monad, monadBind and return,
    % thereby fixing Arrow, id and o.  These conjectures
    % are imported then as well and turn into the proof
    % obligations on the actual definitions supplied.

    conjecture idNeutral is
      [a,b] fa(f : Arrow(a,b)) id o f = f && f o id = f

    conjecture oAssoc is
      [a,b,c,d] fa(f : Arrow(a,b), g : Arrow(b,c), h : Arrow(c,d))
        (h o g) o f = h o (g o f)

  endspec by {Kleisli.id +-> return}

  type Kleisli.Arrow(a,b) = a -> Monad b

  op  monadBind : [a,b] Monad a * Arrow(a,b) -> Monad b

  op  monadSeq : [a,b] Monad a * Monad b -> Monad b
  def monadSeq(f, g) = monadBind(f, (fn _ -> g))

  def Kleisli.o(g,f) x = monadBind(f x, g)

  op  map : [a,b] (a -> b) -> (Monad a -> Monad b)
  def map f x = monadBind(x, return o f)

  op  flatten : [a] Monad(Monad a) -> Monad a
  def flatten xx = monadBind(xx, id)

endspec
