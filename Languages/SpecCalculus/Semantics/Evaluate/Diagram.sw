(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Evalution of a diagram term in the Spec Calculus *)

SpecCalc qualifying spec
  import Signature
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Library/Legacy/DataStructures/ListUtilities     % for listUnion
  import UnitId/Utilities                                    % for uidToString, if used...

  import                    /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  import Functor qualifying /Library/Structures/Data/Categories/Functors/FreeDomain/Polymorphic/AsRecord
  import Cat     qualifying /Library/Structures/Data/Categories/Diagrams/Polymorphic/AsRecord
  import Sketch  qualifying /Library/Structures/Data/Categories/Sketches/Monomorphic/AsRecord

  import NatTrans qualifying /Library/Structures/Data/Categories/NatTrans/FreeFunctorDomain/Polymorphic/AsRecord

\end{spec}

When constructing the semantic representation of a diagram, what are
the coherence conditions that come up? Commutativity of sketches.
Lots of proof obligations. Needs thought.

\begin{spec}
  def evaluateDiag elems pos = {
    unitId <- getCurrentUID;
    print (";;; Elaborating diagram-term at " ^ (uidToString unitId)^"\n");
    (dgm : SpecDiagram, timeStamp, depUIDs) <-
         foldM evaluateDiagElem ((emptyDiagram (specCat ())),0,[]) elems;
    return (Diag dgm,timeStamp,depUIDs)
    }
\end{spec}

%%   type DiagElem a = (DiagElem_ a) * a
%%   type DiagElem_ a =
%%     | Node NodeId * (Term a)
%%     | Edge EdgeId * NodeId * NodeId * (Term a)
%%   type NodeId = Name
%%   type EdgeId = Name

This fixes the types for representing the vertices and edges in the
shape of diagrams. We use ppString, but really should be ppNodeId.

\begin{spec}
  type Vertex.Elem = NodeId
  type Edge.Elem = EdgeId
  def Vertex.ppElem = ppString
  def Edge.ppElem = ppString

  op vertexName : Vertex.Elem -> String
  def vertexName v = v  % used by colimit
\end{spec}

The conditions for a diagram expression to be valid include:
\begin{itemize}
\item A node must be labeled by a spec. Later this will
  be relaxed.
\item A edge must be labeled by a spec morphism
\item If a node is to be added and already appears, then the
  new and old labels must be equal.
\item If an edge is to be added and it already appears, then
  dom and cod nodes must be consistent in the sense above, and
  likewise for the edge.
\end{itemize}

\begin{spec}
  op evaluateDiagElem : (SpecDiagram * TimeStamp * UnitId_Dependency) -> DiagElem -> Env (SpecDiagram * TimeStamp * UnitId_Dependency)
  def evaluateDiagElem (dgm : SpecDiagram,timeStamp,depUIDs) elem =
    case (valueOf elem) of
      | Node (nodeId,term) -> {
           (termValue,termTime,termDeps) <- evaluateTermInfo term;
           case termValue of
             | Spec spc -> {
                    newDgm <- addLabelledVertex dgm nodeId spc (positionOf term);
                    return (newDgm, max (timeStamp,termTime), listUnion (depUIDs, termDeps))
                  }
             | _ -> raise (TypeCheck (positionOf term, "diagram node not labeled with a specification"))
          }
      | Edge (edgeId,domNode,codNode,term) -> {
           (termValue,termTime,termDeps) <- evaluateTermInfo term;
           case termValue of
             | Morph morph ->
                if edgeInDiagram? dgm edgeId then
                  if (domNode = Sketch.eval (src (shape dgm)) edgeId)
                   && (codNode = Sketch.eval (target (shape dgm)) edgeId) then
                    if (morph = edgeLabel dgm edgeId) then
                      return (dgm, max (timeStamp, termTime), listUnion (depUIDs, termDeps))
                    else
                      raise (DiagError (positionOf term,
                                        "edge "
                                       ^ edgeId
                                       ^ " inconsistently labeled in diagram"))
                  else
                    raise (DiagError (positionOf term,
                                        "edge "
                                       ^ edgeId
                                       ^ " has inconsisent source and/or target"))
                else {
                    dgm1 <- addLabelledVertex dgm domNode (dom morph) (positionOf term);
                    dgm2 <- addLabelledVertex dgm1 codNode (cod morph) (positionOf term);
                    let dgm3 = labelEdge (addEdge dgm2 edgeId domNode codNode) edgeId morph in
                      return (dgm3, max (timeStamp,termTime), listUnion (depUIDs, termDeps))
                  }
             | _ -> raise (TypeCheck (positionOf term, "diagram edge not labeled by a morphism"))
           }
\end{spec}

edge is in diagram then the dom and cod must be the same as what we have
and the edge must be labeled with the same morphism 
if edge is not in the diagram then addLa

\begin{spec}
  op addLabelledVertex :
       SpecDiagram 
    -> Vertex.Elem
    -> Spec
    -> Position
    -> Env SpecDiagram
  def addLabelledVertex dgm nodeId spc position =
    if vertexInDiagram? dgm nodeId then
      if (spc = vertexLabel dgm nodeId) then
        return dgm
      else
        raise (DiagError (position,
                            "node "
                           ^ nodeId
                           ^ " inconsistently labeled in diagram"))
    else
      return (labelVertex (addVertex dgm nodeId) nodeId spc)
endspec
\end{spec}
