\subsection{Evalution of a diagram term in the Spec Calculus}

Synchronized with r1.3 SW4/Languages/SpecCalculus/Semantics/Evaluate/EvalDiagram.sl

\begin{spec}
SpecCalc qualifying spec {
  import Signature
  import /Languages/MetaSlang/Specs/Categories/AsRecord
  import /Library/Structures/Data/Categories/Diagrams/Polymorphic
\end{spec}

When constructing the semantic representation of a diagram, what are
the coherence conditions that come up? Commutativity of sketches.
Lots of proof obligations. Needs thought.

\begin{spec}
  def SpecCalc.evaluateDiag elems = {
      dgm <- foldM evaluateDiagElem emptyDiagram elems;
      return (Diag dgm,0,[])
    }
\end{spec}

%%   sort DiagElem a = (DiagElem_ a) * a
%%   sort DiagElem_ a =
%%     | Node NodeId * (Term a)
%%     | Edge EdgeId * NodeId * NodeId * (Term a)
%%   sort NodeId = Name
%%   sort EdgeId = Name

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
       SpecCalc.Diagram (Spec,SpecCat.Morphism)
    -> DiagElem Position
    -> Env (SpecCalc.Diagram (Spec,SpecCat.Morphism))

  def evaluateDiagElem dgm elem =
    case (valueOf elem) of
      | Node (nodeId,term) -> return emptyDiagram
%%%          {
%%%            value <- evaluateTerm term;
%%%            case value of
%%%              | Spec spc -> return emptyDiagram
%%%              | _ -> raise (TypeCheck (positionOf term, "diagram node not labeled with a spec"))
%%%            % if member (vertices (shape dgm)) elem then
%%%          }
      | Edge (edgeId,domNode,codNode,term) -> return emptyDiagram
}
\end{spec}
