\section{BSpec simplification}

This is a trivial \BSpec\ simplifier. It eliminates (where possible)
the transitions which are no-ops. Classifying these transitions is
more difficult than one might expect. An indentity transition can be
encoded in a variety of ways. For instance, the fact that a variable
doesn't change may expressed as an axiom: $x' = x$. Alternatively, it
can be expressed by having a single operator $x$ the apex and then the
$x$'s that appear in at the source and target both map to the same $x$
at the apex.  One can have combinations of the two as well.

The latter representation is preferred as it means that only 
variables that change need to be mentioned at the axiom at the apex.

Ideally we would like a minimal representation where for each transition,
if an identifier is unchanged then it is omitted from the axiom at the
apex. This is not easy to ensure. If, for example, we have
\verb&x' = x + y&, and \verb+y+ is instantiated with $0$, then we need
to detect that the axiom has become the identity. This is likely to
be undecidable.

Call a transition whose axiom is \verb+true+ and where both the forward
and backward morphisms are identity signature morphisms, a \verb+nil+
transition.

We will eliminate \verb+nil+ transitions. For each vertex $a$,
the \emph{succesor set} is the set of pairs $(e,b)$ where $e$
is an edge connecting $a$ to $b$. A program is considered to 
be \emph{well-formed}, if when the successor set contains a
\verb+nil+ transition, then it is the only transition in the
successor set.  

The problem with the scheme is eliminating an edge into the top of a loop.
When is such an elimination well formed.

\begin{verbatim}
  if 
    z > 1 ->
      y := y + 1;
      do 
        z > 0 -> z := f (y,z)
    z <= 1 ->
      command
\end{verbatim}

Now specialize with some value of y. The command incrementing \verb+y+
becomes \verb+nil+. In this case we are ok since there remains a single
branch into the top of the loop.

\begin{verbatim}
  if 
    y <= 0 ->
      y := abs (y);
      do 
        z > 0 -> z := f (y,z)
    y > 0 ->
      command
\end{verbatim}

A program is \emph{locally} deterministic if the guards on the transitions
leaving a state are exclusive.

\begin{lemma}
Collapsing \verb+nil+ transitions never introduces a a new transition
exiting a loop.
\end{lemma}

\begin{proof}
Suppose we have a
branch point with two outgoing transitions $e$ and $f$ labelled with
specs $E$ and $F$ respectively. Now suppose that extending $f$ we find
a vertex $c$ which is in a loop and $c$ is not along a path extending
$e$. Further suppose that all the specs along the path to $c$ reduce to
\verb+true+. Then $F$ reduces to \verb+true$ and hence, since the guards
are exclusive, $E$ must reduce to \verb+false+ and can be discarded.
\end{proof}

This is closely related to the issue of $\tau$
transitions in Milner's CCS. 

For programs that are not locally deterministic, there might still be a
way to collapse transitions. It may be necessary to conjoin
the negation of guard onto the guards leaving the now common vertex.
But this is unlikely to work. Consider two loops with the same
guard in a context that gets collapsed and the starting vertices
of the two loops gets identified.

To be a nil transition, does it follow that to src and target specs
have the same signature?

begin{spec}
  op simplifyOscar : Oscar -> Oscar
  def simplifyOscar {procedures,main} = {
      procedures = mapMap_p simplifyProcedure procedures,
      main = main
  }
end{spec}

There is a hack here as we represent external procedures using systems
with no edges.

begin{spec}
  op simplifyProcedure : Procedure_ms -> Procedure_ms
  def simplifyProcedure proc = {
      parameters = proc.parameters,
      return = proc.return,
      static = proc.static,
      axmSpec = proc.axmSpec,
      dynamic = proc.dynamic,
      code =
        if empty?_e proc.code.system.shape.edges then
          proc.code
        else
          removeNilTransitions proc.code
  }

\begin{spec}
Simplify qualifying spec
  import /Languages/PSL/Semantics/Evaluate/Specs/Oscar
  import /Languages/PSL/Semantics/Evaluate/Specs/Subst
  import /Languages/PSL/Semantics/Evaluate/Specs/Compiler

  (* We prematurely refine transition specs here. *)
  import /Languages/PSL/Semantics/Evaluate/Specs/TransSpec/Legacy

  op PE.connect : BSpec -> Vrtx.Vertex -> Vrtx.Vertex -> Edg.Edge -> TransSpec -> Env BSpec

  op removeNilTransitions : BSpec -> Env BSpec
  def removeNilTransitions oldBSpec = {
      newBSpec <- return (BSpec.make (initial oldBSpec) (modeSpec oldBSpec (initial oldBSpec)));
      succCoalg <- return (succCoalgebra oldBSpec);
      predCoalg <- return (predCoalgebra oldBSpec);
      removeNilsFrom oldBSpec succCoalg predCoalg (initial oldBSpec) (succCoalg (initial oldBSpec)) newBSpec
    }
\end{spec}

The strategy is to construct a new bspec from the old bspec but
only create those vertices and edges that are reachable and where
the nil transitions are eliminated.

We are give a collection of \verb+edges+ leaving \verb+src+. If there
is exactly one edge and it is a nil transition and does not
lead to the final state then we eliminate the edge. 

If there are more than one transition leaving the src, then we check
to see that none of them are nil transitions. This would represent
an undesirable degree of non-determinism.

\begin{spec}
  op removeNilsFrom :
       BSpec
    -> Coalgebra
    -> Coalgebra
    -> Vrtx.Vertex
    -> EdgSet.Set
    -> BSpec
    -> Env BSpec

  def removeNilsFrom oldBSpec succCoalg predCoalg src edges newBSpec = 
    case (takeOne edges) of
      | None -> return newBSpec
      | One (edge,rest) -> 
          if (empty? rest) then {
            transSpec <- return (edgeLabel (system oldBSpec) edge);
            target <- return (GraphMap.eval (target (shape (system oldBSpec)), edge));
            if (isNilTransition? transSpec)
                            & ~(member? (final oldBSpec,target))
                            & (indegreeOne predCoalg target) then
              removeNilsFrom oldBSpec succCoalg predCoalg src (succCoalg target) newBSpec
            else
              extendBSpec oldBSpec succCoalg predCoalg src newBSpec edge
          } else {
             nilLeavingState? <- existsInSet (fn edge -> isNilTransition? (edgeLabel (system oldBSpec) edge)) edges;
             when nilLeavingState?
                (raise (SpecError (noPos, "Nil transition leaving branching node")));
             EdgSetEnv.foldl (extendBSpec oldBSpec succCoalg predCoalg src) newBSpec edges
          }
\end{spec}

This copies an edge from the old bspec to then new and then recursively
explores the transitions leaving the target state.

\begin{spec}
  op extendBSpec :
       BSpec
    -> Coalgebra
    -> Coalgebra
    -> Vrtx.Vertex
    -> BSpec
    -> Edg.Edge 
    -> Env BSpec

  def extendBSpec oldBSpec succCoalg predCoalg src newBSpec edge = {
      transSpec <- return (edgeLabel (system oldBSpec) edge); 
      target <- return (GraphMap.eval (target (shape (system oldBSpec)), edge));
      if VrtxSet.member? (vertices (shape (system newBSpec)), target) then
        connect newBSpec src target edge transSpec
      else {
        targetSpec <- return (modeSpec oldBSpec target);
        newBSpec <-
          if VrtxSet.member? (final oldBSpec, target) then
            return (addFinalMode newBSpec target targetSpec)
          else
            return (addMode newBSpec target targetSpec);
        newBSpec <- connect newBSpec src target edge transSpec;
        removeNilsFrom oldBSpec succCoalg predCoalg target (succCoalg target) newBSpec
      }
    }

  op indegreeOne : Coalgebra -> Vrtx.Vertex -> Boolean
  def indegreeOne predCoalg vertex =
    case takeOne (predCoalg vertex) of
      | None -> fail "removeNilTransitions: vertex with no predecessors?"
      | One (edge,rest) ->
          if empty? rest then
            true
          else
            false
\end{spec}
endspec

how do we ensure we don't explore the same vertex more than once.
We are accumulating a new bspec .. need to check that the vertex
is not already there before adding and exploring from it.

Which begs the question, do we need the pending list in the PE?

To do the partial evaluation of procedures .. add the procs
to the context and then build a new list of procs in the PE.
To see if we need to pe a procedure, then check to see which
map it is in.

\begin{spec}
  op existsInSet : (Edg.Edge -> Boolean) -> EdgSet.Set -> Env Boolean
  def existsInSet f s =
    case (takeOne s) of
      | None -> return false
      | One (x,s) ->
         if (f x) then
           return true
         else
           existsInSet f s

  op isNilTransition? : TransSpec -> Boolean
  def isNilTransition? transSpec =
    let ms = modeSpec transSpec in
    let def trueAxiom? claim =
        if member? (invariants ms, refOf claim) then
          case (claimType claim,term claim) of
            | (Axiom, Fun (Bool true,_,_)) -> true
            | _ -> false
        else
          true
    in
      empty? (changedVars (backMorph transSpec))
      & (all trueAxiom? (specOf (modeSpec transSpec)).properties)
endspec
\end{spec}

