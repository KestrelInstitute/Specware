\section{Functors with free domain and polymorphic target category}

This is a copy of
/Library/Structures/Data/Categories/Functor/FreeDomain/Monomorphic.sw
It is here because of lack of sufficient support for requalifying names.

The point is that we need a copy of sketches where the sets for edges
and vertices are distinct from those used for diagrams. Hence we need
to import a local copy of sketches which, in turn, imports Set twice
but qualified differently from those used in diagrams.

\begin{spec}
spec {
  import Shape qualifying ../Sketch
  import Category qualifying /Library/Structures/Math/Cat  % need to avoid clash of op dom
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic 

  sort Functor

% the record refinement should appear elsewhere.
  sort Functor = {
    dom : Sketch,
    vertexMap : PolyMap.Map (V.Elem,Object),
    edgeMap :  PolyMap.Map (E.Elem,Arrow)
  }

  op dom : Functor -> Sketch
  def dom func = func.dom

  op vertexMap : Functor -> PolyMap.Map (V.Elem,Object)
  def vertexMap func = func.vertexMap

  op edgeMap : Functor -> PolyMap.Map (E.Elem,Arrow)
  def edgeMap func = func.edgeMap

  op emptyFunctor : Functor
  def emptyFunctor = {
    dom = emptySketch,
    vertexMap = PolyMap.emptyMap,
    edgeMap = PolyMap.emptyMap
  }
\end{spec}

When pretty printing a functor, we don't print the domain or codomain. 
Printing the domain (generator) is not unreasonable.

\begin{spec}
  op ppFunctor : Functor -> Pretty
  def ppFunctor functor = 
    ppConcat [
      ppString "Vertex Map =",
      ppNewline,
      ppString "  ",
      ppIndent (PolyMap.ppMap V.ppElem ppObject (vertexMap functor)),
      ppNewline,
      ppString "Edge Map =",
      ppNewline,
      ppString "  ",
      ppIndent (PolyMap.ppMap E.ppElem ppArrow (edgeMap functor))
   ]
}
\end{spec}

Perhaps we should define the free category construction. Can we also
describe what happens on graph homomorphisms? Ie can we define a functor?
Perhaps not since this requires the category of categories. Needs thought.
