\subsection{Evalution of a diagram term in the Spec Calculus}

Much extended from r1.3 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalDiagram.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Library/Legacy/DataStructures/ListUtilities     % for listUnion
\end{spec}

When constructing the semantic representation of a diagram, what are
the coherence conditions that come up? Commutativity of sketches.
Lots of proof obligations. Needs thought.

\begin{spec}
  def SpecCalc.evaluateDiag elems = {
      (dgm,timeStamp,depURIs) <-
         foldM evaluateDiagElem ((emptyDiagram (specCat ())),0,[]) elems;
      return (Diag dgm,timeStamp,depURIs)
    }
\end{spec}

%%   sort DiagElem a = (DiagElem_ a) * a
%%   sort DiagElem_ a =
%%     | Node NodeId * (Term a)
%%     | Edge EdgeId * NodeId * NodeId * (Term a)
%%   sort NodeId = Name
%%   sort EdgeId = Name

This fixes the types for representing the vertices and edges in the
shape of diagrams. We use ppString, but really should be ppNodeId.

\begin{spec}
  sort Vertex.Elem = NodeId
  sort Edge.Elem = EdgeId
  def Vertex.ppElem = ppString
  def Edge.ppElem = ppString
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
  op evaluateDiagElem :
       (Diagram (Spec,Morphism) * TimeStamp * URI_Dependency)
    -> DiagElem Position
    -> Env (Diagram (Spec,Morphism) * TimeStamp * URI_Dependency)

  def evaluateDiagElem (dgm,timeStamp,depURIs) elem =
    case (valueOf elem) of
      | Node (nodeId,term) -> {
           (termValue,termTime,termDeps) <- evaluateTermInfo term;
           case coerceToSpec termValue of
             | Spec spc -> {
                    newDgm <- addLabelledVertex dgm nodeId spc (positionOf term);
                    return (newDgm, max (timeStamp,termTime), listUnion (depURIs, termDeps))
                  }
             | _ -> raise (TypeCheck (positionOf term, "diagram node not labeled with a specification"))
          }
      | Edge (edgeId,domNode,codNode,term) -> {
           (termValue,termTime,termDeps) <- evaluateTermInfo term;
           case termValue of
             | Morph morph ->
                if edgeInDiagram? dgm edgeId then
                  if (domNode = Sketch.eval (src (shape dgm)) edgeId)
                   & (codNode = Sketch.eval (target (shape dgm)) edgeId) then
                    if (morph = edgeLabel dgm edgeId) then
                      return (dgm, max (timeStamp, termTime), listUnion (depURIs, termDeps))
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
                      return (dgm3, max (timeStamp,termTime), listUnion (depURIs, termDeps))
                  }
             | _ -> raise (TypeCheck (positionOf term, "diagram edge not labeled by a morphism"))
           }
\end{spec}

edge is in diagram then the dom and cod must be the same as what we have
and the edge must be labeled with the same morphism 
if edge is not in the diagram then addLa

\begin{spec}
  op addLabelledVertex :
       Diagram (Spec,Morphism) 
    -> Vertex.Elem
    -> Spec
    -> Position
    -> Env (Diagram (Spec,Morphism))
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
}
\end{spec}
