\section{Functors with free domain and polymorphic target category}

This is a spec for polymorphic functors where the domain is the free
category generated from a category presentation (ie sketch). This spec is
meant mainly for defining diagrams and systems. A key distinction between
this spec and the more general polymorphic functor spec is that the effect
of the functor is determined by what the maps do on the vertices
and edges of the graph underlying the sketch.

Note the following. In
\specref{Library/Structures/Data/Categories/Functors/Polymorphic},
the type Functor is defined over 4 type variables. The first two are
the types of the objects and arrows in the domain category. The other
two for the codomain category. In contrast, here there are only type
variables characterizing the objects and arrows in the codomain.

An alternative to including the generator is simply to define the
functor from the free category. The problem is that by doing so, we
lose the ability to enumerate (fold) over the vertices and edges
in the generating graph, since as a rule, whereas the number of edges
in the generating graph may be finite, there may not be a finite number
of paths in the free category.

Note that import Maps are qualified with "PolyMap". This is to distinguish
it from the monomorphic maps used elsewhere. See the file NameSpaces
for more on this.

The names of some of these operators clash with Cats and Graphs.

\begin{spec}
spec {
  import Shape qualifying Sketch
  import Cat qualifying /Library/Structures/Data/Categories/Polymorphic
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

  type Functor (O,A)

% the record refinement should appear elsewhere.
  type Functor (O,A) = {
    dom : Sketch,
    cod : Cat (O,A),
    vertexMap : PolyMap.Map (V.Elem,O),
    edgeMap :  PolyMap.Map (E.Elem,A)
  }

  op dom : fa (O,A) Functor (O,A) -> Sketch
  def dom func = func.dom

  op cod : fa (O,A) Functor (O,A) -> Cat (O,A)
  def cod func = func.cod

  op vertexMap : fa (O,A) Functor (O,A) -> PolyMap.Map (V.Elem,O)
  def vertexMap func = func.vertexMap

  op edgeMap : fa (O,A) Functor (O,A) -> PolyMap.Map (E.Elem,A)
  def edgeMap func = func.edgeMap

  op emptyFunctor : fa (O,A) Cat (O,A) -> Functor (O,A)
  def emptyFunctor cat = {
    dom = emptySketch,
    cod = cat,
    vertexMap = PolyMap.emptyMap,
    edgeMap = PolyMap.emptyMap
  }
    
\end{spec}

When pretty printing a functor, we don't print the domain or codomain. 
Printing the domain (generator) is not unreasonable.

\begin{spec}
  op ppFunctor : fa (O,A) Functor (O,A) -> Pretty
  def ppFunctor functor = 
    ppConcat [
      ppString "Vertex Map =",
      ppNewline,
      ppString "  ",
      ppIndent (PolyMap.ppMap V.ppElem (ppObj (cod functor)) (vertexMap functor)),
      ppNewline,
      ppString "Edge Map =",
      ppNewline,
      ppString "  ",
      ppIndent (PolyMap.ppMap E.ppElem (ppArr (cod functor)) (edgeMap functor))
   ]
}
\end{spec}

The above should import and refine the general polymorphic Functors spec
and the explicit records should be removed from both.

Perhaps we should define the free category construction. Can we also
describe what happens on graph homomorphisms? Ie can we define a functor?
Perhaps not since this requires the category of categories. Needs thought.
