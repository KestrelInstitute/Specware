

===================
|Specware| Concepts
===================

Overview
########

|Specware| is designed with the idea that large and complex problems
can be specified by combining small and simple specifications, and
that problem specifications can be refined into a working system by
the controlled stepwise introduction of implementation design
decisions, in such a way that the refined specifications and
ultimately the working code is a provably correct refinement of the
original problem specification.

|Specware| allows you to express requirements as formal specifications
without regard to the ultimate implementation or target language.
Specifications can describe the desired functionality of a program
independently of such implementation concerns as architecture,
algorithms, data structures, and efficiency. This makes it possible to
focus on the correctness, which is crucial to the reliability of large
software systems.

Often, there are many possible solutions to a single problem, all
valid, with different advantages and drawbacks. It is sometimes very
difficult to make a decision given all the different trade-offs. Using
|Specware|, the analysis of the problem can be kept separate from the
implementation process, and implementation choices can be introduced
piecemeal, making it easier to backtrack or explore alternatives.

|Specware| allows you to articulate software requirements, make
implementation choices, and generate provably correct code in a
formally verifiable manner. The progression of specifications forms a
record of the system design and development that is invaluable for
system maintenance. You can later adapt the specifications to new or
changed requirements or make different implementation decisions at any
level of the development while reusing what has not changed, and
generate provably correct new code by the same process.

  

.. COMMENT:  overview 

|Specware| Development Process
##############################

Building Specifications
=======================

The first step in building an application in |Specware| is to describe
the problem domain in abstract form. You use the |Metaslang| language
to build specifications (specs) that describe the abstract concepts of
the problem domain. Specs contain types, which denote collections of
values, operations, which denote functions on values, and axioms,
which describe the required properties of the operations in logical
formulas.

To design specifications, you may combine top-down and bottom-up
approaches. To begin, you break down the problem domain into small,
manageable parts that you can understand more easily in complete
detail. You create specifications for each part. This conceptual
decomposition process allows you to isolate and describe each detail
of functionality.

You then extend and compose the smaller specifications to form a
larger, more complex specification.

You create morphisms to describe how specifications are related. A
morphism is a formal mapping between two specifications that describes
exactly how one is translated or extended into the other. Morphisms
can describe "part-of" as well as "is-a" relationships.

You can extend a specification by importing it and adding new
concepts. When you extend a specification, you can also translate the
names of the concepts to a different terminology.

As you extend the specification, you provide more and more information
about the structure and details of the types and operations, by
including axioms and theorems to describe them.

You compose simple specifications to form more complex specifications
using substitutions (e.g., to instantiate parameterized
specifications) and colimit. Colimit
"glues"  specs together along shared
concepts. Morphisms describe exactly how concepts are shared.

 

.. COMMENT:  building 

Refining Specifications
=======================

When you have described the abstract concepts in your problem domain,
you begin the refinement process. Refinement maps a problem
specification set into a solution specification set. Refinements
replace functionality constraints with algorithms and abstract types
with implementation data structures. You refine a specification by
mapping it into the implementation domain. You describe how the
concepts of the problem domain are implemented in terms of
computational concepts. Computational concepts, such as numbers (e.g.,
integers) and collections (e.g., lists) are already specified in the
|Specware| library. In the process of refinement, you build a bridge
from your abstract specifications to these concrete, implementation-
specific specifications.

Morphisms are also used to describe how each specification is to be
mapped into a desired target specification. The source spec is a more
abstract description of concepts, while the target spec describes
those concepts more concretely. Often, the target spec is obtained by
extending some other spec that contains concepts in term of which the
concepts of the source spec are expressed. For example, if you have an
abstract spec for a house, you can refine it by importing a spec for
materials (wood, etc.) and expressing how the house is built in terms
of those materials.

A morphism maps each type or operation of the source spec to a type or
operation of the target spec. In certain cases, it may be useful to
map a type or operation to a new type or operation that is not present
in the target spec but that is defined in terms of those in the target
spec. Interpretations are used for this purpose.

An interpretation contains three specs: a source spec (the domain), a
target spec (the codomain), and a mediator. The mediator spec extends
the target, so there is an inclusion morphism from the target to the
mediator. A morphism from the source spec to the mediator expresses
how the source spec maps to the extension of the target spec.

A morphisms can be viewed as a particular kind of interpretation where
the mediator coincides with the target. Indeed, the refinement
relation between a more abstract spec and a more concrete one can be
expressed by a morphism but also by an interpretation.

  

.. COMMENT:  refining 

Extending Refinements
=====================

You build up a refinement in the same way you build up a
specification, in an iterative, stepwise progression. You build basic
morphisms (or interpretations) from more abstract specs to more
concrete specs, then compose the morphisms to extend the refinement.
There are two ways to compose morphisms.

Sequential composition (\ ``A=>B + B=>C = A=>C``\ ) deepens a
refinement. For example, if you are specifying a house, you might use
sequential composition of morphisms to create an increasingly detailed
description of a single room.

Parallel composition (\ ``A=>A' + B=>B' = (A,B) => (A',B')``\ )
widens, or increases the complexity of a refinement. For example, in
the specification of a house, when you have several morphisms that
refine different rooms, you could combine them in parallel to create a
description of a multi-room house. You could do this before or after
providing the additional detail for each one. You use the colimit
method for this kind of composition, as you do to compose
specifications.

|Specware| contains a library of specs that fully describe various
mathematical and computational concepts that you need to produce an
implementation of an abstract specification. The goal of refinement is
to refine your abstract specs in terms of these library specs. This
process guarantees that |Specware| can generate code to implement your
specifications in its target language, Lisp.

  

.. COMMENT:  extending 

Generating Code
===============

Once the abstract spec is refined to a "constructive" spec, |Specware|
can generate code in the target language.  The generated code contains
a function for each of the operations you have described in the
abstract specification.  After you examine and test it, you can embed
it in an application that uses the functions.

  

.. COMMENT:  generating 

  

.. COMMENT:  process 

Specification Components
########################

A specification (spec) consists of some types, some operations (ops),
and some axioms about the types and ops.

Types, Operations, Axioms
=========================

A type is a syntactic entity that denotes a set of values. In its
simplest form, a type is a symbol. For example, a spec can contain a
type ``Nat`` that denotes the set of natural numbers, i.e., 0, 1, 2,
...



Type symbols can be combined by means of some pre-defined constructs
to build more complex types. One such construct is
"\ ``->``\ ": if ``A`` and
``B`` are types, ``A -> B`` is also a
type.  The set denoted by ``A -> B`` is the set of
all total functions from the set denoted by ``A`` to
the set denoted by ``B``\ .

An op is a syntactic symbol accompanied by a type. An op denotes an
element of the set denoted by its type. For example, a spec can
contain an op ``zero`` of type ``Nat``\ , which denotes the natural
number 0. It can also contain an op ``succ`` of type ``Nat -> Nat``\ ,
which denotes the function that returns the successor of any given
natural number.

From the type ``Nat`` and the ops ``zero`` and ``succ`` alone, it does
not follow that they denote the natural numbers, 0, and successor
function. They could denote the set of the days of the week,
Wednesday, and the identity function, respectively. The intended
meaning can be enforced by means of axioms.

An axiom is a term of type ``Bool``\ . ``Bool`` is a type
automatically present (built-in) in every spec, which denotes the set
of boolean truth values (
"true"  and
"false"). Terms are built from typed variables (i.e.,
symbols accompanied by types), ops, and some pre-defined
constructs. These include universal and existential quantifiers
("for all"  and "exists"), logical
connectives ("and", "or",
"implies", "iff", "not"), and
equality.

Here is an example of an axiom to constrain successor to never return
0:

.. code-block:: specware

   fa(x) ~(succ x = zero)
   

In the axiom,
"\ ``=``\ "  denotes equality,
"\ ``~``\ "  boolean negation, and
"\ ``fa``\ "  universal quantification. Note that this
axiom rules out the possibility that ``succ`` is the
identity function.  Additional axioms can be added to constrain the
spec to capture exactly the natural numbers (essentially, the rest of
Peano's axioms).

Models
======

In the above description, the notion of a type or op
"denoting"  a set or a function corresponds to the notion
of model of a spec. A model of a spec is an assignment of a set to
each type and of an element to each op from the set assigned to the
type of the op, such that all the axioms of the spec are
satisfied.

In the example spec sketched above, a model consists of a set *N*
assigned to ``Nat``\ , an element *z* in *N* assigned to ``zero``\ ,
and a function *s* from *N* to *N* (i.e., an element *s* of the set
denoted by ``Nat -> Nat``) assigned to ``succ``\ . In the absence of
axioms, the model where *N* consists of the days of the week, *z*
Wednesday, and *s* identity, is a valid model. But with the axiom
shown above, since *s(z) = z*, this cannot be a model. With the rest
of Peano's axioms, *N*, *z*, and *s* are constrained to be isomorphic
to natural numbers, 0, and successor. (No matter how many axioms are
added to the spec, it is not possible to pin down *N* to be exactly
the set of natural numbers. Things can be pinned down only up to
isomorphism. But this is fine because isomorphic sets are totally
equivalent.)

A spec may have no models. This happens when the spec contains
incompatible axioms. This situation is often subtle and difficult to
detect, and it is always a symptom of human errors in the
specification process. Whether a spec has models or not is an
undecidable problem. However, by following certain practices and
disciplines in the development of specs, this situation can be
avoided.

Polymorphism
============

Types can be polymorphic. In its simplest form, a polymorphic type is
a symbol plus one or more
"parameter types". While a monomorphic
(i.e., non-polymorphic) type denotes a set, a polymorphic type denotes a
function that returns a set given sets for all its parameters. For example, a
spec can contain a type ``List a``\ , where ``a`` is the type parameter, which
denotes the set of (finite) lists over ``a``\ : more precisely, it denotes a
function that, given a set *S* for ``a``\ , returns the set of all lists of
elements of *S*. If *S* is the set of natural numbers, it returns the set of
all lists of natural numbers; if *S* is the set of the days of the week, it
returns the set of all lists of days of the week.

A polymorphic type can be instantiated by replacing its parameters
with other types. The latter can be polymorphic or monomorphic: if at
least one is polymorphic, the instantiated type is polymorphic;
otherwise, it is monomorphic. For example, ``List a`` can be
instantiated to the monomorphic ``List Nat`` or to the polymorphic
``List(List a)``\ .

Correspondingly, ops can be polymorphic. An op is polymorphic when its
type is a polymorphic type. While a monomorphic op denotes an element
of the set denoted by the type of the op, a polymorphic op denotes a
function that, given a set for each parameter type of the polymorphic
type of the op, returns an element of the set obtained by applying to
such parameter sets the function denoted by the type of the op. For
example, a spec can contain an op ``nil`` of type ``List a``\ , that
denotes the empty list, for each set assigned to parameter ``a``\ .

Morphisms
=========

A morphism is a mapping from a source spec to a target spec. More
precisely, it consists of two functions: one maps each type symbol of
the source to a type symbol of the target, and the other maps each op
symbol of the source to an op symbol of the target. The mapping must
be type-consistent: if ``f`` of type ``T`` in the source spec is
mapped to ``g`` of type ``U`` in the target spec, then ``T`` must be
mapped to ``U``\ . This mapping of types and ops can be lifted to
terms, and thus to the axioms of the source spec. A morphism must be
such that each axiom of the source spec maps to a theorem in the
target spec: in other words, the translation of the axiom (according
to the mapping expressed by the morphism) must be provable from the
axioms in the target spec.

So, a morphism expresses that all the properties (i.e., the axioms) of
the source spec are satisfied by the target spec. This is why
refinement is expressed by means of morphisms: the source spec
contains more abstract concepts; the target spec contains more
concrete concepts, but all the properties of the abstract concepts
must be satisfied by the concrete ones.

At the level of models, a morphism ``m`` induces a function that maps
models of the target spec to models of the source spec (the function
goes in the opposite direction of the morphism). The function operates
as follows: given a model of the target spec, the corresponding model
of the source spec is constructed as follows. The set assigned to a
type ``T`` of the source spec is the set assigned to ``m(T)`` by the
model of the target spec (or, if ``T`` is polymorphic, replace
"set"  with "set-valued function over
sets"); the element assigned to an op ``f`` of type ``T`` of
the source spec is the element (of the set assigned to ``T``\ ) assigned
to ``m(f)`` by the model of the target spec (or, if ``f`` has a
polymorphic type, replace "element"  with
"element-valued function over sets").

In other words, the morphism induces a reduction of the models of the
target spec to models of the source spec. A model of the target spec
can be reduced to a model of the source spec. This shows how a
morphism can express an
"is-a"  relationship.

For example, if a spec imports another spec, possibly adding types,
ops, and axioms, there is an inclusion morphism from the imported spec
to the importing spec. Since all the types, ops, and axioms are mapped
to themselves, the fact that axioms are mapped to theorems is
immediate.

As another, less trivial example, consider a spec for natural numbers
that also includes an op ``plus`` and an op ``times``\ , both of type
``Nat * Nat -> Nat``\ . (The construct
"\ ``*``\ "
builds the cartesian product of two types: in a model, ``A * B``
denotes the cartesian product of the set denoted by ``A`` and the set
denoted by ``B``\ .) The spec also contains axioms that define ``plus``
and ``times`` to be addition and multiplication. Now, consider another
spec consisting of a type ``X``\ , an op ``f`` of type ``X * X -> X``\ ,
and an axiom stating that ``f`` is commutative:

.. code-block:: specware

   fa(x,y) f(x,y) = f(y,x)
   

There is a morphism from the latter spec to the former that maps ``X``
to ``Nat`` and ``f`` to ``plus``\ : since addition is commutative, the
commutativity axiom can be proved as a theorem in the spec for natural
numbers. Note that there is also another morphism that maps ``X`` to
``Nat`` and ``f`` to ``times``\ .

Diagrams and Colimits
=====================

A diagram is a graph whose nodes are labeled by specs and whose edges
are labeled by morphisms. The morphism labeling an edge must be such
that its source is the spec labeling the source node of the edge, and
its target is the spec labeling the target node of the edge.

The colimit operation produces a spec from a diagram. The resulting
spec is the gluing of the specs of the diagram, with the sharing
expressed by the morphisms of the diagram.

In order to understand how the colimit operation works, consider first
the simple case of a diagram without edges (and morphisms). This is
called a discrete diagram. The colimit operation produces a spec whose
types, ops, and axioms are the disjoint union of the types, ops, and
axioms of the specs in the diagram. In other words, the specs are all
glued together without any sharing.

Now, consider a diagram with some edges, labeled by morphisms. The
colimit operation produces a spec containing all the types, ops, and
axioms of the specs in the diagram, but all the types or ops that are
linked, directly or indirectly, through the morphisms, are identified
(i.e., they are the same type or op).

Consider, for example, a diagram with three nodes, ``a``\ , ``b``\ ,
and ``c``\ , and two edges, one from ``a`` to ``b`` and the other from
``a`` to ``c``\ . Node ``a`` is labeled by a spec consisting of a type
``X``\ , node ``b`` by a spec consisting of two types ``Y`` and ``Z``\
, and node ``c`` by a spec consisting of a type ``W``\ . The morphism
labeling the edge from ``a`` to ``b`` maps ``X`` to ``Y``\ , and the
one labeling the edge from ``a`` to ``c`` maps ``X`` to ``W``\ . The
colimit contains all types ``X``\ , ``Y``\ , ``Z``\ , and ``W``\ , but
``X``\ , ``Y``\ , and ``W`` are identified. So, the colimit
effectively contains two types, one that can be referred to as ``X``\
, ``Y``\ , or ``W``\ , and the other that can be only referred to as
``Z``\ . For diagrams of this shape, with three nodes and two edges
forming a wedge, the colimit operation is also called a pushout.

Substitutions
=============

Given a spec ``S`` and a morphism ``M``\ , it is possible (under
certain conditions) to substitute the domain of ``M`` with its
codomain inside ``S``\ . Another way to say the same thing is that it
is possible to
"apply"  the morphism ``M`` to the spec
``S``\ .

Let ``A`` and ``B`` be the domain and codomain specs of ``M``\ . The
substitution operation is possible if and only if ``A`` is a sub-spec
of ``S``\ , in the sense that all the types, ops, and axioms of ``A``
are also in ``S``\ . This is the case when ``S`` is constructed by
importing and extending, directly or indirectly, ``A``\ .

If that condition is satisfied, the result of the substitution is the
spec ``S'`` that consists of all the types, ops, and axioms of ``B``
plus all the types, ops, and axioms of ``S`` that are not in ``A``\ ;
the latter must all be translated according to the name mapping of
``M``\ .

For example, suppose that:

#. \ ``A`` consists of a type ``X``\ ;

#. \ ``S`` consists of two types ``X`` and ``Y`` and an op ``f`` of type
   ``X -> Y``\ ;

#. \ ``B`` consists of a type ``X'`` and an op ``c`` of type ``X'``\ ;

#. \ ``M`` maps type ``X`` in ``A`` to type ``X'`` in ``B``\ .

The result ``S'`` of the substitution consists of types ``X'`` and
``Y``\ , an op ``f`` of type ``X' -> Y``\ , and an op ``c`` of type
``X'``\ . In other words, ``A`` is replaced with ``B`` inside ``S``
and the remaining portion of ``S`` is renamed accordingly.

  

.. COMMENT:  substitution 

Interpretations
===============

A morphism maps a type or op of the source spec to a type or op of the
target spec. In certain cases, it may be useful to map the type or op
to a new type or op that is not present in the target spec but that
can be defined in terms of those present in the target spec. This is
captured by the concept of interpretation.

An interpretation is a morphism from a spec to a definitional
extension of another spec. A definitional extension is an extension of
a spec that only introduces new types and ops with axioms that define
them in terms of those present in the spec that is being extended.

More precisely, an interpretation contains three specs: a source spec
(the domain), a target spec (the codomain), and a mediator spec. The
mediator is a definitional extension of the target spec, and there is
an inclusion morphism from the target spec to the mediator. There is a
morphism from the source spec to the mediator.

Consider, as an example, a spec for natural numbers without any
``plus`` op, but just with ``zero`` and ``succ``\ , and with Peano's
axioms. Consider the spec (also used as an example above) consisting
of a type ``X``\ , and op ``f``\ , and a commutativity axiom about
``f``\ . There is no morphism from the latter spec to the one for
natural numbers. But there is an interpretation, where the mediator
extends the spec for natural numbers with an op ``plus`` for addition,
which can be inductively defined by the following two axioms:

.. code-block:: specware

   fa(x) plus(x,zero) = x
   fa(x,y) plus(x,succ y) = succ(plus(x,y))
   

A morphism can be viewed as a particular case of an interpretation,
where the mediator is the same spec as the target, and the inclusion
morphism from the target to the mediator is the identity morphism.

Diagrams of specs and morphisms can be generalized to diagrams of
specs and interpretations: nodes are labeled by specs and edges by
interpretations. The colimit operation works on these diagrams as
well. The types and ops in the resulting spec include not only those
from the specs labeling the nodes, but also those from the mediators
of the interpretations.

  

.. COMMENT:  components 

