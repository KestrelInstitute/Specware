\section{Naive Predicative BSpecs}

BSpecs in an abstract category. A BSpec is a system interpreted as a
flow graph and having a designated start state.

The term ``multipointed'' refers to the possibility that there may be
many end states as well.

The term ``predicative'' refers to the fact that the forward
and backward morphisms are an epimorphic pair in the labelling
category. This is not exploited at present.

Seems odd that we need to qualify things with \Qualifier{Vertex}
and \Qualifier{Edge}.

\begin{spec}
BSpec qualifying spec {
  import /Library/Structures/Data/Categories/Systems

  sort BSpec = {
    initial : Vertex.Vertex,
    final : VertexSet.Set,
    system : System
  }

  op initial : BSpec -> Vertex.Vertex
  def initial bSpec = bSpec.initial

  op final : BSpec -> VertexSet.Set
  def final bSpec = bSpec.final

  op system : BSpec -> System
  def system bSpec = bSpec.system

  op make : Vertex.Vertex -> Object -> BSpec
  def make first spc = {
    initial = first,
    final = empty,
    system = labelVertex (addVertex empty first) first spc 
  }

  op addMode : BSpec -> Vertex.Vertex -> Object -> BSpec
  def addMode bSpec vertex spc =
    bSpec withSystem (labelVertex (addVertex (system bSpec) vertex) vertex spc)

  op addFinalMode : BSpec -> Vertex.Vertex -> Object -> BSpec
  def addFinalMode bSpec vertex spc =
    (bSpec withSystem (labelVertex (addVertex (system bSpec) vertex) vertex spc))
           withFinal (insert (final bSpec, vertex))

  op map : BSpec -> (Object -> Object) -> (Arrow -> Arrow) -> BSpec
  def map bSpec objMap arrMap = bSpec withSystem (map (system bSpec) objMap arrMap)

  op addTrans :
       BSpec 
    -> Vertex.Vertex
    -> Vertex.Vertex
    -> Edge.Edge
    -> Object
    -> Arrow
    -> Arrow
    -> BSpec
  def addTrans bSpec src target edge spc morph1 morph2 =
    bSpec withSystem (labelEdge (addEdge (system bSpec) edge src target) edge spc morph1 morph2)

  op withSystem infixl 17 : (BSpec * System) -> BSpec
  def withSystem (bSpec,system) = {
    initial = initial bSpec,
    final = final bSpec,
    system = system
  }

  op withFinal infixl 17 : (BSpec * VertexSet.Set) -> BSpec
  def withFinal (bSpec,modes) = {
    initial = initial bSpec,
    final = modes,
    system = system bSpec
  }
\end{spec}

The first function retrieves the spec associated with a transition.
Because of the twist, the desired spec is in the image of the vertex
map rather than the edge map.

\begin{spec}
  op transitionSpec : BSpec -> Edge.Edge -> Object
  def transitionSpec bSpec edge = eval (vertexMap (system bSpec), Edge edge)
\end{spec}

The next function retrieves the spec associated with a state or mode.

\begin{spec}
  op modeSpec : BSpec -> Vertex.Vertex -> Object
  def modeSpec bSpec vertex = eval (vertexMap (system bSpec), Vertex vertex)
\end{spec}

Naive pretty printing of \BSpecs

\begin{spec}
  op pp : BSpec -> Doc
  def pp bSpec =
    ppConcat [
      pp "{initial = ",
      pp (initial bSpec),
      pp ", final = ",
      pp (final bSpec),
      pp ", system = ",
      ppNewline,
      pp "  ",
      ppIndent (pp (system bSpec)),
      pp "}"
    ]
}
\end{spec}
