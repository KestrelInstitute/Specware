\section{Systems in a Polymorphic Category}

A category of systems has a fixed universe of shapes (ie sketches) but
is parameterized on the target category.  Systems in this case refers
to twisted systems. They differ from diagrams in that the domain of the
functor is "twisted".

Systems are very similar to diagrams and in fact can be viewed as a class
of diagrams. Alternatively, systems and diagrams both arise by application
of the Grothendieck construction to a strict indexed category. The two
arise from slightly different indexed cats. 

Like a diagram, a system is a shape and a functor. The difference is that
whereas with diagrams the domain of the functor is the shape, in twisted
systems, the domain of the functor is the "twist" of the shape. The twist
operation has the effect of replacing every edge in the graph with an cospan.

More generally twisted systems can be constructed with shapes other than
sketches. A particularly attractive option is that the shapes should be
a higher-dimensional automaton in the sense of van Glabeek, Goubault and
others. Such automota are expressed in terms of complexes from algebraic
topology and determine sketches by a construction similar to that for
a fundamental groupoid.

Note that the functors appearing here are those whose domain is freely
generated from the shape.

Formally, a system is a pair consisting of a shape and a functor from
the twist of the shape into the target category.

There are two copies of Set in sketches. One for the vertices and one for
the edges.

What do we really want. Right now the sorts for the sketches of the functor
and the shape are all identified. Why?

Perhaps sketches should have imported sets twice but explicitly named them
apart than than qualifying. 

For the time being, the sort for the domain of the functor and for the
sketch are the same. This is reflected in the fact that we don't import
a copy of Sketch directly but through the import of Functor. It is also
reflected in the type for the elements of the set. The sort
mut be able to encode the types of the

\begin{spec}
spec {
  import Functor qualifying ../Functors/FreeDomain/Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  sort System (O,A)
  op shape : fa (O,A) System (O,A) -> Sketch
  op functor : fa (O,A) System (O,A) -> Functor (O,A)
\end{spec}

The operations for adding vertices and edges yield a system that is not
well-formed. In particular, the new vertex or edge is unlabeled. It might
be better to make the addition of an edge or vertex and the labeling an
atomic operation. Perhaps later.

Also we assume that when an edge gets labeled, labeling of the start and
end vertices are consistent with the domain and codomain of the morphism.

Since system are parameterized on the target category, when we construct
an empty system we must give fix the target category.

\begin{spec}
  op emptySystem : fa (O,A) Cat (O,A) -> System (O,A)
  op addVertex : fa (O,A) System (O,A) -> Vertex.Elem -> System (O,A)
  op addEdge : fa (O,A) System (O,A)
    -> Edge.Elem -> Vertex.Elem -> Vertex.Elem -> System (O,A)

  op vertexInSystem? : fa (O,A) System (O,A) -> Vertex.Elem -> Boolean
  op edgeInSystem? : fa (O,A) System (O,A) -> Edge.Elem -> Boolean

  op labelVertex : fa (O,A) System (O,A) -> Vertex.Elem -> O -> System (O,A)
  op labelEdge : fa (O,A) System (O,A) -> Edge.Elem -> O -> A -> A -> System (O,A)
\end{spec}

The following fold a function over the vertices and edges of a system and
retrieve the labels on the vertices and edges.

Should the function being folded be given the system as well? Probably not.
If necessary, the function being folded can be curried where its first
argument is the system. For example, the function f:

\begin{verbatim}
  sort S
  op f : fa (O,A) System (O,A) -> x -> Edge.Vertex -> x
  op unit : S
\end{verbatim}

can be folded over a system sys with:

\begin{verbatim}
  foldOverEdges (f sys) unit sys
\end{verbatim}

\begin{spec}
  op edgeLabel : fa (O,A) System (O,A) -> Edge.Elem -> (A * O * A)
  op vertexLabel : fa (O,A) System (O,A) -> Vertex.Elem -> O

  op foldOverEdges : fa (x,O,A) (x -> Edge.Elem -> x) -> x -> System (O,A) -> x
  op foldOverVertices : fa (x,O,A) (x -> Vertex.Elem -> x) -> x -> System (O,A) -> x
\end{spec}

While they are distinguished in the signatures above, the sorts of edges
and vertices of the sketch must be the same. The sets must also be
the same sort. Then the domain of the functor is a sketch where the
vertices and edges are the coproduct of the sort for the vertices
end edges.

The coproduct sort is far more restructive than it needs to be.

\begin{spec}
  sort Elem
  op ppElem : Elem -> Pretty

  sort TaggedElem =
     | Just Elem
     | Tag (Nat * TaggedElem)

  op ppTaggedElem : TaggedElem -> Pretty
  def ppTaggedElem x =
    case x of
        Just x -> ppElem x
      | Tag (n,x) ->
         ppConcat [
           ppString "(",
           ppString (Nat.toString n),
           ppString ",",
           ppTaggedElem x,
           ppString ")"
         ]
\end{spec}

Right now the domain of the functor and the shape are defined over
a single spec for Sketches. This is not right. The sets should be
different ..  and there should be no concrete representation for the
domain of the functor.

Identifying the sorts for the edges and vertices is done by equations.
It would be better if they were identified by a colimit so that there
is only one sort.

\begin{spec}
  sort Vertex.Set = Edge.Set  % Without this things don't typecheck??

  sort Vertex.Elem = TaggedElem
  sort Edge.Elem = TaggedElem

  % op Vertex.ppElem : Vertex.Elem -> Pretty
  % op Edge.ppElem : Edge.Elem -> Pretty

  def Vertex.ppElem = ppTaggedElem 
  def Edge.ppElem = ppTaggedElem
\end{spec}

Next we define the coproduct operation. This is not used at runtime.

\begin{spec}
  op coprod : Vertex.Set -> Vertex.Set -> Vertex.Set
  def coprod s1 s2 =
    let s1p = Vertex.map (fn (x : TaggedElem) -> Tag (0,x)) s1 in
    let s2p = Vertex.map (fn x -> Tag (1,x)) s2 in
    Vertex.union s1p s2p
\end{spec}

Next we fix the sorts for the maps between graphs. Again these are
the coproducts given above.  This should get fixed by the above in
someway. This should be redundant.

\begin{spec}
  sort Dom = TaggedElem
  sort Cod = TaggedElem

  op ppDom : Dom -> Pretty
  op ppCod : Cod -> Pretty

  def ppDom = Edge.ppElem
  def ppCod = Vertex.ppElem
\end{spec}

Next we define the twist operation on (non-reflexive) graphs. Reflexive
graphs are similar. In fact, as systems are typically built incrementally,
this function is not likely to be used.

This is not used at runtime. It would be far better to have a 
axiomatic characterization of this.

This is where there is a small problem. Below, we define the
twist. The assumption made below is that the we use the same sorts for
both sketches. The underlying sets may have different representations.
This is wrong. Also, there shouldn't be a call to makeSketch.  It should
be done incrementally with addVertex and addEdge.

\begin{spec}
  op twist : Sketch -> Sketch
  def twist sketch =
    let vs = coprod (vertices sketch) (edges sketch) in
    let es = coprod (edges sketch) (edges sketch) in
    let def upd_src map e = Sketch.update map e
      (case e of
        | (Tag (0,e)) -> Tag (0, eval (src sketch) e)
        | (Tag (1,e)) -> Tag (0, eval (target sketch) e)
        | _ -> fail "badly formed graph") in
    let def upd_target map e = Sketch.update map e
      (case e of
        | (Tag (0,e)) -> Tag (1,e)
        | (Tag (1,e)) -> Tag (1,e)
        | _ -> fail "badly formed graph") in
    let src = Edge.fold upd_src emptyMap es in
    let target = Edge.fold upd_target emptyMap es in
    makeSketch vs es src target % No Equations yet!!
\end{spec}

A functor has a domain and this must be the same as the twist of the shape
of the system. In a concrete representation, the apparent redundancy
can be eliminated.

\begin{spec}
  axiom system_domain is fa (sys) (shape sys) = twist (dom (functor sys))
\end{spec}

\begin{spec}
  op ppSystem : fa (O,A) System (O,A) -> Pretty
  def ppSystem sys =
    ppConcat [
      ppString "Shape=",
      ppNewline,
      ppString "  ",
      ppIndent (ppSketch (shape sys)),
      ppNewline,
      ppString "  ",
      ppString "Functor=",
      ppIndent (ppFunctor (functor sys))
    ]
\end{spec}

A functor has a domain and this must be the same as the twist of the shape
of the system. In a concrete representation, the apparent redundancy
can be eliminated.

\begin{spec}
}
\end{spec}
