This spec is not used at present.

It differs from the base polymorphic spec in that the association of
objects to arrows in the dom, cod and ident operations is via maps rather
then function spaces.  Arguably this spec is more abstract and the base
polymorphic version should be presented as a refinement of this.

The spec below defines a sort for representing categories.  The sort is
polymorphic in the sense that the same sort can be used at runtime to
represent different categories. For instance, categories of finite sets,
Specs, graphs etc.

In most cases, the polymorphism appearing here is not needed and one
is better to use a monomorphic sort. Also, often, one does not need a
sort for category at all but rather just a spec.  Note that the spec
below is roughly what you get from a naive internalization of the spec
Structures/Math/Categories/Cat. There is another such internalization
without the polymorphism.

This sort of internalization is yields definitions closest to Burstall
and Rydeheard's presentation.

The spec is intended to handle two distinct cases: when the sets of
objects and arrows are finite or generated from a finite set (as in the
category generated from a graph) and when the sets are possibly infinite
(as in the category Spec). In the first, we might expect 'Set a' to refine
to lists or trees. In the second we might expect 'Set a' to refine to
'a -> Boolean'.  For the category Spec, for example, this might end up
as just 'fn x -> True'. It would appear that this scheme also allows us
to define subcategories easily.

This first spec is not used (note the verbatim environment). This is
an abstract spec of which the second should be a refinment

\begin{spec}
spec {
  import /Library/Structures/Data/Sets/Polymorphic
  import /Library/Structures/Data/Maps/Polymorphic

  sort Cat (O,A) 

  op objects : fa (O,A) Cat (O,A) -> Set O
  op arrows : fa (O,A) Cat (O,A) -> Set A
  op ident : fa (O,A) Cat (O,A) -> Map (O,A)
  op dom : fa (O,A) Cat (O,A) -> Map (A,O)
  op cod : fa (O,A) Cat (O,A) -> Map (A,O)
  op composable? : fa (O,A) Cat (O,A) -> Set (A * A)
  op compose : fa (O,A) Cat (O,A) -> A -> A -> A
}
\end{spec}

This still needs some thought. How do we say that ident only applies to
what is in the set `objects'. Do we need dependent types? I don't think it is
going to help. Perhaps we need an axiom to say that for a category C,
O is a member? of (objects C) iff O member? (domain (ident C)).

One problem with it is that one may want to refine the different
occurrences of 'Set a' in different ways.

Some other issues. Should we distinguish total and partial maps? Should
the domain and codomain of a map be part of the map? Perhaps if the maps 
are total.

Should compose be partial?

Should compose take the two arrows as a product or should it be curried? I
prefer curried.

I have used A * A but to internalize things correctly, we should have
an 'internal' product type, Prod (a,b) which might refine to a * b but
might not.
