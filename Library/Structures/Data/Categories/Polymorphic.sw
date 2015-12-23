(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

\section{Polymorphic Categories}

The spec below defines a type for representing categories.  See also the
spec WithMaps for a different, and in some ways better, representation.

The type is polymorphic in the sense that the same type can be used at
runtime to represent different categories. For instance, categories of
finite sets, Specs, graphs etc.

In most cases, the polymorphism appearing here is not needed and one
is better to use a monomorphic type. Also, often, one does not need a
type for category at all but rather just a spec.  Note that the spec
below is roughly what you get from a naive internalization of the spec
Structures/Math/Categories/Cat. There is another such internalization
without the polymorphism.

This type of internalization yields definitions closest to Burstall
and Rydeheard's presentation and what David Espinosa did.

Unlike the CatsWithMaps, we do not internalize the sets of objects
and arrows.

This still needs some thought. How do we say that ident only applies to
what is in the set `objects'. Do we need dependent types? I don't think it is
going to help. Perhaps we need an axiom to say that for a category C,
O is a member? of (objects C) iff O member? (domain (ident C)).

Some other issues. Should we distinguish total and partial maps? Should
the domain and codomain of a map be part of the map? Perhaps if the maps 
are total.

Should compose be partial? yes but it messes up any operations that use
compose since they must inspect the result that comes back to
see if is is valid. The other option is to define a subtype of A * A
of those maps that are composable and then define compose over that subset
... but then compose isn't curried any more. And I don't think it is realistic
to check for conformance at compile time. And it doesn't work anyway since it
would require a dependent type.

The other option is to make everything monadic .. then there can be
a monad for partial maps and all the ugly stuff gets hidden.

Should compose take the two arrows as a product or should it be curried? I
prefer curried.

The following defines both only an abstract type for categories.
A concrete product type is defined in Polymorphic/AsRecord.spec. The
separation is needed to enable the type Cat to be refined. In particular,
the type for cocomplete category comes with the same operators plus one
for computing colimits.

This way we can define operations on categories also applicable to
cocomplete categories.

But this doesn't work .. operations like slice can be defined only
abstractly. We are still obliged to define the slice for both
categories and cocomplete categories. In this case the extra
level of abstraction helps none.

\begin{spec}
Cat qualifying spec {
  import /Library/PrettyPrinter/WadlerLindig

  type Cat (O,A)

  op ident       : fa (O,A) Cat (O,A) -> O -> A
  op dom         : fa (O,A) Cat (O,A) -> A -> O
  op cod         : fa (O,A) Cat (O,A) -> A -> O
 %op composable? : fa (O,A) Cat (O,A) -> A -> A -> Bool
  op compose     : fa (O,A) Cat (O,A) -> A -> A -> A
  op ppObj       : fa (O,A) Cat (O,A) -> O -> WLPretty
  op ppArr       : fa (O,A) Cat (O,A) -> A -> WLPretty
}
\end{spec}

We have omitted the operator composable?. It seems of little use,
even with subtypeing, without dependent types.

Should we have pretty printing operations here? 
