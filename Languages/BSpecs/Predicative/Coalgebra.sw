\section{Recasting BSpecs as simple Coalgebras}

These are functions for converting a predicative \BSpec\ into one of two
coalgebras.  For some applications, these simplify the task of navigating
around a \BSpec\ program.

\begin{spec}
spec {
  import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic
  import Multipointed
  import PolySet qualifying /Library/Structures/Data/Sets/Polymorphic
\end{spec}

It is convenient, when traversing an algorithm representing a diagram,
to first convert it into a coalgebra. The coalgebra can represented
either as a function or as a map. The latter has the advantage that it
can be updated. We define sorts for each of the two representations
of coalgebras.

\begin{spec}
  sort Coalgebra = V.Elem -> PolySet.Set (V.Elem * V.Elem)
  sort CoalgebraMap = PolyMap.Map (V.Elem, PolySet.Set (V.Elem * V.Elem))
\end{spec}

A better scheme might be to start with just the Map version and then
refine maps to functions. Needs thought. Also, there is no need to 
return the target state. It is enough to return the set of edges.

Given an algorithm, the following yields what we might call the
\emph{successor coalgebra} corresponding to the underlying graph. That
is, it returns a function which when given a state, returns a finite set
of pairs.  A pair is an edge and a state such that if the function maps
$v \mapsto (f,v')$ then $f$ is an edge from $v$ to $v'$ in the underlying
graph in the algorithm. The state $v'$ is a \emph{successor} of $v$. Put
another way, given a state, the function returns the transitions leaving
that state.

\begin{spec}
  op succCoalgebraMap : BSpec -> CoalgebraMap
  def succCoalgebraMap prg =
    let shape = shape (system prg) in
\end{spec}

We begin by constructing a map that takes every vertex to an emptySet.

\begin{spec}
    let initMap = V.fold (fn map -> fn vertex -> PolyMap.update map vertex PolySet.empty)
                         PolyMap.emptyMap (vertices shape) in
\end{spec}

Next we fold over the edges in the graph. Given an edge $e$ with source
$v$, we update the map at $v$ by adding $(e, \mathit{target} e)$ to the
set. This could be made much much more efficient.

\begin{spec}
    let def upd_map map edge =
      let vertex = eval (src shape) edge in
      let set = PolyMap.eval map vertex in
        PolyMap.update map vertex (PolySet.insert set (edge, eval (target shape) edge))
    in
      E.fold upd_map initMap (edges shape)
\end{spec}

Then we hide the map inside a function. It might be better to return the
map rather than the function. Needs thought.

\begin{spec}
  op succCoalgebra : BSpec -> Coalgebra
  def succCoalgebra prg = fn vertex -> PolyMap.eval (succCoalgebraMap prg) vertex
\end{spec}

The following is in a sense dual to the above. Given an algorithm it
returns the \emph{predecessor coalgebra}. This is a function (or map) with
the property that, given a state, it returns the transitions ending at
that state.

\begin{spec}
  op predCoalgebra : BSpec -> Coalgebra
  def predCoalgebra prg = fn vertex -> PolyMap.eval (predCoalgebraMap prg) vertex

  op predCoalgebraMap : BSpec -> CoalgebraMap
  def predCoalgebraMap prg =
    let shape = shape (system prg) in
    let initMap = V.fold (fn map -> fn vertex -> PolyMap.update map vertex PolySet.empty)
                         PolyMap.emptyMap (vertices shape) in
    let def upd_map map edge =
      let vertex = eval (target shape) edge in
      let set = PolyMap.eval map vertex in
        PolyMap.update map vertex (PolySet.insert set (edge, eval (src shape) edge))
    in
      E.fold upd_map initMap (edges shape)
}
\end{spec}
