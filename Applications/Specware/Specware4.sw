\section{Specware 4 Toplevel Specification}

This constructs Specware and refines various abstract sorts.

\begin{spec}
spec {
  import /Languages/SpecCalculus/Semantics/Specware
  import /Languages/SpecCalculus/Semantics/Evaluate/NoOther

  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
  import Cat qualifying
    /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  import Functor qualifying
    /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic/AsRecord
  import Cat qualifying
    /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
  import Sketch qualifying
    /Library/Structures/Data/Categories/Sketches/Monomorphic/AsRecord

  % The renaming below should match that in /Library/Structures/Data/Graphs.sw
  import translate (Vertex qualifying /Library/Structures/Data/Sets/Monomorphic/AsLists) by {
      Elem.Elem +-> Vertex.Elem,
      Elem.pp +-> Vertex.ppElem,
      Vertex.pp +-> Vertex.ppSet
    }
  import translate (Edge qualifying /Library/Structures/Data/Sets/Monomorphic/AsLists) by {
      Elem.Elem +-> Edge.Elem,
      Elem.pp +-> Edge.ppElem,
      Edge.pp +-> Edge.ppSet
    }

  import Sketch qualifying 
    /Library/Structures/Data/Maps/Monomorphic/AsLists
  import NatTrans qualifying
    /Library/Structures/Data/Categories/NatTrans/FreeFunctorDomain/Polymorphic/AsRecord
} 
\end{spec}
