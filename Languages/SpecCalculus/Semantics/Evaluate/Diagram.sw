\subsection{Evalution of a diagram term in the Spec Calculus}

Much extended from r1.3 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalDiagram.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Languages/MetaSlang/Specs/Categories/AsRecord
\end{spec}

When constructing the semantic representation of a diagram, what are
the coherence conditions that come up? Commutativity of sketches.
Lots of proof obligations. Needs thought.

\begin{spec}
  def SpecCalc.evaluateDiag elems = {
      dgm <- foldM evaluateDiagElem (emptyDiagram specCat) elems;
      return (Diag dgm,0,[])
    }
\end{spec}

%%   sort DiagElem a = (DiagElem_ a) * a
%%   sort DiagElem_ a =
%%     | Node NodeId * (Term a)
%%     | Edge EdgeId * NodeId * NodeId * (Term a)
%%   sort NodeId = Name
%%   sort EdgeId = Name

\begin{spec}
  sort Vertex.Elem = NodeId
  sort Edge.Elem = EdgeId
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

Unfortunately the SpecCalc and SpecCat qualifiers are needed here otherwise
the typechecker complains. I don't understand it.

\begin{spec}
  op evaluateDiagElem :
       Diagram (Spec,Morphism)
    -> DiagElem Position
    -> Env (Diagram (Spec,Morphism))

  def evaluateDiagElem dgm elem =
    case (valueOf elem) of
      | Node (nodeId,term) -> {
           value <- evaluateTerm term;
           case value of
             | Spec spc -> addLabelledVertex dgm nodeId spc (positionOf term)
             | _ -> raise (TypeCheck (positionOf term, "diagram node not labeled with a specification"))
          }
      | Edge (edgeId,domNode,codNode,term) -> {
           value <- evaluateTerm term;
           case value of
             | Morph morph ->
                if edgeInDiagram? dgm edgeId then
                  if (domNode = eval (src (shape dgm)) edgeId)
                   & (codNode = eval (target (shape dgm)) edgeId) then
                    if (morph = edgeLabel dgm edgeId) then
                      return dgm
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
                    dgm <- addLabelledVertex dgm domNode (dom morph) (positionOf term);
                    dgm <- addLabelledVertex dgm codNode (cod morph) (positionOf term);
                    return (labelEdge (addEdge dgm edgeId domNode codNode) edgeId morph)
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
