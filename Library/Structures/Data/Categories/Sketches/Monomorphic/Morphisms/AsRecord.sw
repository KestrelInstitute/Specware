This is not used at present.

This defines a sort for morphisms between sketches. There are many choices
for such morphisms. One would be that a sketch morphism is simply a
morphism on the underlying graph that preserves the equations (if any). A more
general notion would be a morphism maps edges in the source to paths in the
target such that equations are preserved.

The sort defined below is not complete. It should be subsorted so
to ensure that the domain and image of the maps agrees with the
dom and cod fields.

Note that we import two copies of endo-maps.  This is a situation where
having different sorts for the sets of vertices and the sets of edges
makes things more complicated than we might like.

The spec VertexMaps defines a sort VertexMap.Elem and endo maps on that set.
Similarly, EdgeMaps defines a sort EdgeMap.Elem and endo maps on it.

The names of the sorts VertexMap.Elem and EdgeMap.Elem correspond to the
sorts for the elements of the edge and vertex sets respectively. These
are defined in Graphs.

There might be a better way to ensure the endo maps and sets are defined 
over the same elements rather that by renaming them to coincide.

We import two copies of endo-maps, one for vertices and one for edges.

\begin{spec}
let Sketches =
  /Library/Structures/Data/Categories/Sketches/Monomorphic in
let VertexMaps =
  VertexMap qualifying /Library/Structures/Data/Maps/Monomorphic/Endo in
let EdgeMaps =
  EdgeMap qualifying /Library/Structures/Data/Maps/Monomorphic/Endo in
spec
  import /Library/PrettyPrinter/WadlerLindig
  import Sketches
  import VertexMaps
  import EdgeMaps
\end{spec}

Now refine the sorts for the domain and codomain of monomorphic maps.

\begin{spec}
  sort Morphism = {
      dom : Sketch,
      cod : Sketch,
      vertexMap : VertexMap.Map,
      edgeMap : EdgeMap.Map
    }

  op compose : Morphism -> Morphism -> Morphism

  def compose
   {dom = dom1, cod = cod1, vertexMap = vertexMap1, edgeMap = edgeMap1}
   {dom = dom2, cod = cod2, vertexMap = vertexMap2, edgeMap = edgeMap2} =
     {dom = dom1,
      cod = cod2,
      vertexMap = VertexMap.compose vertexMap1 vertexMap2,
      edgeMap = EdgeMap.compose edgeMap1 edgeMap2}
\end{spec}

Should compose be partial? Yes but this makes everything ugly downstream.

The sort defines domain and codomain operations. These may be redundant as
the information is carried in sort Cat. Think about it.

Must the sorts for the vertices and edges in the domain and codomain be
the same? They aren't in the case of functors.

\begin{spec}
  op ppSketchMorphism : Morphism -> Pretty
  def ppSketchMorphism sm =
    ppBlockAll [
      ppString "Vertex map=",
      ppIndent 2 (VertexMap.ppMap sm.vertexMap),
      ppString "Edge map=",
      ppIndent 2 (EdgeMap.ppMap sm.edgeMap)
    ]
end
\end{spec}
