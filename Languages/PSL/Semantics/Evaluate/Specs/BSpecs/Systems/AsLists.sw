\section{Naive refinement of systems}

Local copy to handle eq test on sets of vertices and edges.
This could be cleaned up alot.

\begin{spec}
System qualifying spec
  import /Library/Structures/Data/Categories/Systems
  import Shape qualifying ../Sketches/AsLists
  import Cat qualifying /Library/Structures/Math/Cat
  import EdgeMap qualifying
    (translate (translate ../Maps/AsAssocLists
       by {KeyValue._ +-> EdgeCat._, Dom._ +-> TW_Edge._, Cod._ +-> Cat._})
       by {TW_Edge.Dom +-> TW.Edge, Cat.Cod +-> Cat.Arrow})

  % op TW_Edge.eq? : TW.Edge * TW.Edge -> Boolean
  def TW_Edge.eq? (e1,e2) =
    case (e1,e2) of
      | (Forw e1,Forw e2) -> Edge.eq? (e1,e2)
      | (Back e1,Back e2) -> Edge.eq? (e1,e2)
      | _ -> false


  import VertexMap qualifying
    (translate (translate ../Maps/AsAssocLists
       by {KeyValue._ +-> VertexCat._, Dom._ +-> TW_Vertex._, Cod._ +-> Cat._})
       by {TW_Vertex.Dom +-> TW.Vertex, Cat.Cod +-> Cat.Object})

  % op TW_Vertex.eq? : TW.Vertex * TW.Vertex -> Boolean
  def TW_Vertex.eq? (v1,v2) =
    case (v1,v2) of
      | (Vertex v1,Vertex v2) -> Vertex.eq? (v1,v2)
      | (Edge e1,Edge e2) -> Edge.eq? (e1,e2)
      | _ -> false
endspec
\end{spec}
