\section{PSL Toplevel Specification}

This constructs PSL and refines various abstract sorts.

\begin{spec}
let PSL = spec {
  import /Languages/SpecCalculus/Semantics/Specware
  import /Languages/PSL/Semantics/Evaluate/Other

  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic/AsLists
  import Cat qualifying
    /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  import Functor qualifying
    /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic/AsRecord
  import Cat qualifying
    /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
  import Sketch qualifying
    /Library/Structures/Data/Categories/Sketches/Monomorphic/AsRecord
  import Vertex qualifying
    /Library/Structures/Data/Sets/Monomorphic/AsLists
  import Edge qualifying
    /Library/Structures/Data/Sets/Monomorphic/AsLists
  import Sketch qualifying 
    /Library/Structures/Data/Maps/Monomorphic/AsLists
  import NatTrans qualifying
    /Library/Structures/Data/Categories/NatTrans/FreeFunctorDomain/Polymorphic/AsRecord

  % This doesn't work because the sketches refer explicitly to
  % Vertex.Elem and Edge.Elem so the translation yields operators
  % with the incorrect sort. so insertEdge refers to Vertex.Elem rather than V.Elem
  % import Shape qualifying
  %   translate /Library/Structures/Data/Categories/Sketches/Monomorphic/AsRecord
  import Shape qualifying
    /Library/Structures/Data/Maps/Monomorphic/AsLists
  import E qualifying
    /Library/Structures/Data/Sets/Monomorphic/AsLists
  % import V qualifying
   %  /Library/Structures/Data/Sets/Monomorphic/AsLists
  % why doesn't the above work
  def V.singleton = E.singleton
  def V.empty = E.empty
  def V.insert = E.insert
  def V.fold = E.fold
  def V.map = E.map
  def V.union = E.union
  def V.member? = E.member?

  % sort Systems.Elem = ATerm Position
% These shouldn't be here.
  def Systems.ppElem term = SpecCalc.ppATerm term
  def Shape.ppDom = ppTaggedElem
  def Shape.ppCod = ppTaggedElem
\end{spec}

Now we repeat some of the definitions appearing in
\verb+Library/DataStructures/Categories/Twist/Polymorphic/Systems.spec+.
It follows that we should only have had to import one copy of monomorphic
sets but then the names wouldn't have gone through elsewhere.

  sort Dom = TaggedElem
  sort Cod = TaggedElem

\begin{spec}
} in
  generate lisp PSL
\end{spec}
