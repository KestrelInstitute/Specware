\section{Naive Predicative BSpecs}

This is the same as ../Multipointed except that the target
category is monomorphic. See the comments in the above.

\begin{spec}
BSpec qualifying spec {
  import /Library/Structures/Data/Categories/Systems/Monomorphic

  sort BSpec = {
    initial : V.Elem,
    final : V.Set,
    system : System
  }

  op initial : BSpec -> V.Elem
  def initial bSpec = bSpec.initial

  op final : BSpec -> V.Set
  def final bSpec = bSpec.final

  op system : BSpec -> System
  def system bSpec = bSpec.system

  op make : V.Elem -> Object -> BSpec
  def make first spc = {
    initial = first,
    final = V.empty,
    system = labelVertex (addVertex emptySystem first) first spc 
  }

  op addMode : BSpec -> V.Elem -> Object -> BSpec
  def addMode bSpec vertex spc =
    bSpec withSystem (labelVertex (addVertex (system bSpec) vertex) vertex spc)

  op mapBSpec : BSpec -> (Object -> Object) -> (Arrow -> Arrow) -> BSpec
  def mapBSpec bSpec objMap arrMap =
    bSpec withSystem (mapSystem (system bSpec) objMap arrMap)

  op addTrans :
       BSpec 
    -> V.Elem
    -> V.Elem
    -> E.Elem
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

  op withFinal infixl 17 : (BSpec * V.Set) -> BSpec
  def withFinal (bSpec,modes) = {
    initial = initial bSpec,
    final = modes,
    system = system bSpec
  }
\end{spec}

The first function retrieves the spec associated with a transition. Bear in
mind that the transition (edge) is "tagged" so if $f$ is an edge, you
pass (Just $f$) as the name of the transition.

Because of the twist, the desired spec is in the image of the vertex map
rather than the edge map. 

\begin{spec}
  op transitionSpec : BSpec -> E.Elem -> Object
  def transitionSpec bSpec edge = 
      PolyMap.eval (vertexMap (functor (system bSpec))) (Tag (1,edge))
\end{spec}

The next function retrieves the spec associated with a state or mode.

\begin{spec}
  op modeSpec : BSpec -> V.Elem -> Object
  def modeSpec bSpec vertex =
    PolyMap.eval (vertexMap (functor (system bSpec))) (Tag (0,vertex))
\end{spec}

Given a transition, this returns the static operators for the transition. The
static operators are those not forming part of the machine state.

The latter has not been implemented yet.

Naive pretty printing of \BSpecs

\begin{spec}
  op pp : BSpec -> WadlerLindig.Pretty
  def pp {initial,final,system} =
    ppConcat [
      ppString "{",
      ppString "initial = ",
      V.ppElem initial,
      ppString ", final = ",
      V.pp final,
      ppNewline,
      ppString "system = ",
      ppNewline,
      ppString "  ",
      ppIndent (ppSystem system),
      ppNewline,
      ppString "}"
    ]
}
\end{spec}
