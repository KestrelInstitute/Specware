\section{Naive Predicative BSpecs}

This defines trivial \BSpecs\ labelled in the category of specs.

This needs refactoring!!. The explicit products should be removed.

Systems are now multi-pointed rather than bi-pointed. This means they
may have many exit points. This file will be abstracted and renamed.

These functions are for examining and constructing \emph{multipointed
predicative} \BSpecs.  Recall that a \BSpec\ is a twisted system labeled
in the category \cat{Spec}. These are essentially diagrams interpreted
as state machines, transition systems, Kripke frames or other such
behavioural models of computation.

In \BSpecs, each transition is labelled with an opspan. There is a spec
and a pair of spec morphisms (or interpretations) to it from the start
and end specs of the transition. More precisely, an edge $a \To[e] b$
in a graph is labelled

\[
S \To[f] X \From[g] T
\]

where $S$, $T$ and $X$ are specs. The spec $X$ is the \emph{apex}.

Predicative \BSpecs\ are those with the property that the opspan of
morphisms, $f$ and $g$, labeling a transition are jointly epimorphic
on signatures. This implies that both $f$ and $g$ above are spec morphisms
(rather than interpretations) but neither identifies two symbols. Note
however that $f$ and $g$ may each take symbol to the same target.
So in $f$, $x \mapsto x$ and $g$ may $y \mapsto x$. This relaxes an
earlier constraint that $f$ and $g$ must have disjoint images.

The spec at the apex contains axioms. These axioms define a relation
between the new and old values of the dynamic variables (operators).
This means that the effect of the transition is captured in the axiom
alone.

Multipointed means that each system has \emph{points}: these are
desginated vertices representing the initial (start) and possible many
final (end) states.

The requirement that $f$ and $g$ be jointly epimorphic extends to the
components of the natural transformations between \BSpecs. Without
this constraint on the components, the category of \BSpecs\ would not
be complete.

This structure is likely to change. The proper way to do pointed systems
is to construct slices in the category of shapes. This is likely to
happen later.

This needs some work. For starters, it is not enough to label modes
and transitions in the category \cat{Spec}. We need to distinguish between
the sorts and ops that are part of the state and those that are ``static''
(in the ASM sense). This suggests labeling the states and transitions
in slice categories. Are all such spec sliced over the same spec?
Presumably sorts like \verb{Nat} should be pervasive. But there should also
be the possibility to define sorts whose interpretation is fixed
but scoped nevertheless.

Importing the category of specs includes also the sorts for the abstract
syntax of MetaSlang and spec morphisms.

\begin{spec}
spec {
  import Systems qualifying /Library/Structures/Data/Categories/Systems/Polymorphic
  import /Languages/MetaSlang/Specs/Categories/AsRecord

  sort BSpec = {
    initial : V.Elem,
    final : V.Set,
    system : System (Spec, Morphism)
  }

  op initial : BSpec -> V.Elem
  def initial bSpec = bSpec.initial

  op final : BSpec -> V.Set
  def final bSpec = bSpec.final

  op system : BSpec -> System (Spec, Morphism)
  def system bSpec = bSpec.system

  op newSystem : V.Elem -> Spec -> BSpec
  def newSystem first spc = {
    initial = first,
    final = V.empty,
    system = labelVertex (addVertex (emptySystem (specCat ())) first) first spc 
  }

  op addMode : BSpec -> V.Elem -> Spec -> BSpec
  def addMode bSpec vertex spc = {
    initial = bSpec.initial,
    final = bSpec.final,
    system = labelVertex (addVertex (system bSpec) vertex) vertex spc
  }
    
  op addTrans :
       BSpec 
    -> V.Elem
    -> V.Elem
    -> E.Elem
    -> Spec
    -> Morphism
    -> Morphism
    -> BSpec
  def addTrans bSpec src target edge spc morph1 morph2 = {
    initial = initial bSpec,
    final = final bSpec,
    system = labelEdge (addEdge (system bSpec) edge src target) edge spc morph1 morph2
  }

  op setFinalModes : BSpec -> V.Set -> BSpec
  def setFinalModes bSpec modes = {
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
  op transitionSpec : BSpec -> E.Elem -> Spec
  def transitionSpec bspec edge = 
      PolyMap.eval (vertexMap (functor (system bspec))) (Tag (1,edge))
\end{spec}

The next function retrieves the spec associated with a state or mode.

\begin{spec}
  op modeSpec : BSpec -> V.Elem -> Spec
  def modeSpec bspec vertex =
    PolyMap.eval (vertexMap (functor (system bspec))) (Tag (0,vertex))
\end{spec}

Given a transition, this returns the static operators for the transition. The
static operators are those not forming part of the machine state.

The latter has not been implemented yet.

\subsection*{Operators for constructing BSpecs}

There are many ways to encode this relation at the apex of the opspan.

In one, the two legs of the opspans are imports and all the operators
appear twice.  The names of the operators in the second copy are "primed"
by suffixing them with "'".  This agrees with many many other formal
methods including Z, SAL, TLA etc.  Note that this means that, since "'"
is not a valid character in a MetaSlang identifier, if we write the specs
out, they cannot be read in again without substituting something for the
"'" or until the parser is changed.  Hopefully the parser will change.

To make this more precise, if $S$ is a spec, let $S'$ be the spec obtained by
priming the operators. Now given a spec $S$ and a list of axioms $A$,
this constructs the opspan:

\[
S \To[f] (S + S') \wedge A \From[g] S
\]

It returns the spec at the apex, $(S + S') \wedge A$, and the morphisms $f$
and $g$. In Z terminology, the apex of the opspan is a refinement of
$\Delta S$.

The following does most of the work of constucting an (op)span relating
the specs at two states. The spec at the start and end of a transition
are assumed to be same for now but this will change. In other words,
the class of opspans is far richer than can be constructed from this
function but this function suffices for now.

This function is given a spec and a list of axioms.  It constructs the
spec for the transition and the morphisms from the start and end specs
into the new spec. The axioms are added to the new spec. At present the
Axioms have no type variables.

When constructing the new spec, we ignore the sorts for now. We assume
for now that the program does not define any new sorts.

\begin{spec}
%  sort Axiom = String * Term
%   op makeSpan : Spec -> List Axiom -> (Spec * Morphism * Morphism)
%   def makeSpan spc axioms = 
%     let newSpc = {
%        name = spc.name ^ " + " ^ spc.name ^ "'",  % prettyPrinting only
%        sorts = spc.sorts,
%        ops = foldMap_p
%           (fn map ->
%              fn opr ->
%                fn opInfo -> update_p map (opr ^ "'") opInfo)
%              spc.ops spc.ops,
%        properties = List.map (fn (name,term) -> (Axiom, name, [], term)) axioms,
%        imports = []
%     } in
%     let sm1 : Morphism = {
%       dom = spc,
%       cod = newSpc,
%       sortMap = emptyMap_p,   % wrong but not used
%       opMap = foldMap_p
%           (fn map ->
%              fn opr ->
%                fn _ -> update_p map opr opr) emptyMap_p spc.ops % ident
%     } in
%     let sm2 : Morphism = {
%       dom = spc,
%       cod = newSpc,
%       sortMap = emptyMap_p,   % wrong but not used
%       opMap = foldMap_p 
%           (fn map ->
%              fn opr ->
%                fn _ -> update_p map opr (opr ^ "'")) emptyMap_p spc.ops
%     } in
%       (newSpc, sm1, sm2)
\end{spec}

Naive pretty printing of \BSpecs

\begin{spec}
  op ppBSpecLess : BSpec -> Spec -> Pretty
  def ppBSpecLess {initial,final,system} spc =
    ppConcat [
      ppString "{",
      ppString "initial = ",
      V.ppElem initial,
      ppString ", final = ",
      V.ppSet final,
      ppNewline,
      ppString "system = ",
      ppNewline,
      ppString "  ",
      ppIndent (ppSystem (mapSystem system (fn o -> subtractSpec o spc) (fn a -> a))),
      ppNewline,
      ppString "}"
    ]

  op ppBSpec : BSpec -> Pretty
  def ppBSpec {initial,final,system} =
    ppConcat [
      ppString "{",
      ppString "initial = ",
      V.ppElem initial,
      ppString ", final = ",
      V.ppSet final,
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

ppBSpecLessShort bSpec spc
  vertices = {
    let edges = edges (shape (system bSpec))
    let srcMap = src (shape (system bSpec))
    let taretMap = target (shape (system bSpec))

    print e : (eval srcMap e) -> (eval targetMap e)
  map (fn e -> Tag (1,n)) 
   eval  e
