\section{Naive refinement of systems}

\begin{spec}
System qualifying spec
  import ../Systems
  import Shape qualifying /Library/Structures/Data/Categories/Sketches/AsLists
  import Cat qualifying /Library/Structures/Math/Cat
  import EdgeMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite/AsAssocLists
       by {KeyValue._ +-> EdgeCat._, Dom._ +-> TW_Edge._, Cod._ +-> Cat._})
       by {TW_Edge.Dom +-> TW.Edge, Cat.Cod +-> Cat.Arrow})

  import VertexMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite/AsAssocLists
       by {KeyValue._ +-> VertexCat._, Dom._ +-> TW_Vertex._, Cod._ +-> Cat._})
       by {TW_Vertex.Dom +-> TW.Vertex, Cat.Cod +-> Cat.Object})
endspec
\end{spec}
