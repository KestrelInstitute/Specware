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

\begin{spec}
Simplify qualifying spec
  import /Languages/PSL/Semantics/Evaluate/Specs/Oscar
  import /Languages/PSL/Semantics/Evaluate/Specs/Subst
  import /Languages/PSL/Semantics/Evaluate/Specs/Compiler

  (* We prematurely refine transition specs here. *)
  import /Languages/PSL/Semantics/Evaluate/Specs/TransSpec/Legacy

  op PE.connect : BSpec -> Mode -> Mode -> Transition -> TransSpec -> Env BSpec

  op removeNilTransitions : BSpec -> Env BSpec
  def removeNilTransitions oldBSpec = {
      (newBSpec,newInitial) <- return (BSpec.initFromOld oldBSpec);
      removeNilsFrom oldBSpec (initial oldBSpec) (outTrans oldBSpec (initial oldBSpec)) newBSpec
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
    -> Mode
    -> List Transition
    -> BSpec
    -> Env BSpec

  def removeNilsFrom oldBSpec src transitions newBSpec = 
    case transitions of
      | [] -> return newBSpec
      | [transition] -> 
            if (isNilTransition? transition)
                            & ~(Mode.member? (final oldBSpec) (Transition.target transition))
                            & (lengthOne (inTrans oldBSpec (Transition.target transition))) then
              removeNilsFrom oldBSpec src (outTrans oldBSpec (Transition.target transition)) newBSpec
            else
              extendBSpec oldBSpec src newBSpec transition
      | _ -> {
             nilLeavingState? <- existsInSet isNilTransition? transitions;
             when nilLeavingState?
                (raise (SpecError (noPos, "Nil transition leaving branching node")));
             foldM (extendBSpec oldBSpec src) newBSpec transitions
          }
\end{spec}

This copies an edge from the old bspec to then new and then recursively
explores the transitions leaving the target state.

\begin{spec}
  op extendBSpec :
       BSpec
    -> Mode
    -> BSpec
    -> Transition
    -> Env BSpec

  def extendBSpec oldBSpec src newBSpec transition =
      if Mode.member? (modes newBSpec) (Transition.target transition) then
        return (newTrans newBSpec src (Transition.target transition) (transSpec transition)).1
      else {
        newBSpec <-
          if Mode.member? (final oldBSpec) (Transition.target transition) then
            return (addFinalMode newBSpec (Transition.target transition))
          else
            return (addMode newBSpec (Transition.target transition));
        newBSpec <- return (newTrans newBSpec src (Transition.target transition) (transSpec transition)).1;
        removeNilsFrom oldBSpec (Transition.target transition) (outTrans oldBSpec (Transition.target transition)) newBSpec
      }

  op lengthOne : List Transition -> Boolean
  def lengthOne l =
    case l of 
      | [_] -> true
      | _ -> false
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
  op existsInSet : (Transition -> Boolean) -> List Transition -> Env Boolean
  def existsInSet f l =
    case l of
      | [] -> return false
      | (x::l) ->
         if (f x) then
           return true
         else
           existsInSet f l

  % This should be a fold
  op isNilTransition? : Transition -> Boolean
  def isNilTransition? transition =
    let ms = Transition.modeSpec transition in
    let def trueAxiom? claim =
        if member? (invariants ms, refOf claim) then
          case (claimType claim,term claim) of
            | (Axiom, Fun (Bool true,_,_)) -> true
            | _ -> false
        else
          true
    in
      empty? (changedVars (backMorph (transSpec transition)))
      & (all trueAxiom? (specOf (modeSpec (transSpec transition))).properties)
endspec
\end{spec}

