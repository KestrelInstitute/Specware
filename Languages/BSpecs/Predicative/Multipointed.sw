\section{Naive Predicative BSpecs}

This defines trivial \BSpecs\ labelled in the category of specs 

This file is misnamed. These systems are now multi-pointed rather than
bi-pointed. This means they may have many exit points. This file will
be abstracted and renamed.

These functions are for examining and constructing \emph{bipointed
predicative} \BSpecs.  Recall that a \BSpec\ is a twisted system labeled
in the category \cat{Spec}. These are essentially diagrams interpreted
as state machines, transition systems, Kripke frames or other such
behavioural models of computation.

In \BSpecs, each transition is labelled with an opspan. There is a spec
and a pair of spec morphisms (or interpretations) to it
from the start and end specs of the transition. More precisely, an
edge $a \To[e] b$ in a graph is labelled

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

Bipointed means that each diagram has two \emph{points} representing
initial (start) and final (end) states.

The requirement that $f$ and $g$ be injective extends to the components
of the natural transformations between \BSpecs. Without this constraint
on the components, the category of \BSpecs\ would not be complete.

This structure is likely to change. The proper way to do bipointed systems
is to construct slices in the category of shapes. This is likely to happen
later.

If you import this you also import: ast spec cat, of ast, ast_util and
so on. Applying a prefix to this spec also yields a prefix of all the
ast stuff. Check the export chain.

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
  import /Library/Structures/Data/Categories/Systems/Polymorphic
  import /Languages/MetaSlang/Specs/Categories/Specs

  sort BSpec = {
    initial : Vertex.Elem,
    final : Vertex.Set,
    system : System (Spec, Morphism)
  }

  op initial : BSpec -> Vertex.Elem
  op final : BSpec -> Vertex.Set
  op system : BSpec -> System (Spec, Morphism)
\end{spec}

The first function retrieves the spec associated with a transition. Bear in
mind that the transition (edge) is "tagged" so if $f$ is an edge, you
pass (Just $f$) as the name of the transition.

Because of the twist, the desired spec is in the image of the vertex map
rather than the edge map. 

\begin{spec}
  op transitionSpec : BSpec -> Edge.Elem -> Spec
  def transitionSpec bspec edge = 
      PolyMap.eval (vertexMap (functor (system bspec))) (Tag (1,edge))
\end{spec}

The next function retrieves the spec associated with a state or mode.

\begin{spec}
  op modeSpec : BSpec -> Vertex.Elem -> Spec
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
  op ppBSpec : BSpec -> Pretty
  def ppBSpec {initial,final,system} =
    ppConcat [
      ppString "{",
      ppString "initial = ",
      Vertex.ppElem initial,
      ppString ", final = ",
      Vertex.ppSet final,
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
