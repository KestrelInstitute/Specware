\section{Naive refinement of systems}

\begin{spec}
System qualifying spec
  import ../Systems
  import Shape qualifying /Library/Structures/Data/Categories/Sketches/AsLists
  import Cat qualifying /Library/Structures/Math/Cat

  import EdgeMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite/AsAssocLists
       by {KeyValue._ +-> EdgeCat._, Dom._ +-> TW_Edge._, Cod._ +-> CatArrow._})
       by {TW_Edge.Dom +-> TW.Edge, CatArrow.Cod +-> Cat.Arrow})

  import VertexMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite/AsAssocLists
       by {KeyValue._ +-> VertexCat._, Dom._ +-> TW_Vertex._, Cod._ +-> CatObject._})
       by {TW_Vertex.Dom +-> TW.Vertex, CatObject.Cod +-> Cat.Object})
endspec
\end{spec}
