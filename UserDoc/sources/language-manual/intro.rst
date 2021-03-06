

==========================
Introduction to |Specware|
==========================

What is |Specware|?
###################

|Specware| is a tool for building and manipulating a collection of
related specifications. |Specware| can be considered:

- a design tool, because it can represent and manipulate designs for
  complex systems, software or otherwise

- a logic, because it can describe concepts in a formal language with
  rules of deduction

- a programming language, because it can express programs and their
  properties

- a database, because it can store and manipulate collections of
  concepts, facts, and relationships

Specifications are the primary units of information in |Specware|. A
specification, or theory, describes a concept to some degree of
detail. To add properties and extend definitions, you create new
specifications that import or combine earlier specifications. Within a
specification, you can reason about objects and their relationships.
You declare types (data types) and operations (ops, functions), axioms
that state properties of operations, and theorems that follow
logically from axioms.

A morphism is a relationship between specifications that describes how
the properties of one map relate to the properties of another.
Morphisms describe both part-of and is-a relationships. You can
propagate theorems from one specification to another using morphisms;
for example, if the QEII is a ship, and ships cannot fly, then the
QEII cannot fly.

What is |Specware| for?
#######################

|Specware| is a general-purpose tool that you can use to develop
specifications for any system or realm of knowledge. You can do this
as an abstract process, with no reference to computer programming; or
you can produce a computer program that is provably a correct
implementation of a specification; or you can use the process to
redesign an existing program.

You can use |Specware| to:

- *Develop domain theories*
  You can use |Specware| to do
  "ontological
  engineering"  -- that is, to describe a real-world domain
  of knowledge in explicit or rigorous terms. You might wish to
  develop a domain theory in abstract terms that are not
  necessarily intended to become a computer program. You can use
  the inference engine to test the internal logic of your theory,
  derive conclusions, and propose theorems.
  You can use specifications and morphisms to represent abstract
  knowledge, with no refinement to any kind of concrete implementation.
  More commonly, you would use |Specware| to model expert knowledge of
  engineering design. In this case you would refine your theoretical
  specifications and morphisms to more concrete levels.

- *Develop code from
  specifications*
  You can use |Specware| to develop computer programs from
  specifications. One advantage of using |Specware| for this task is
  that you can prove that the generated code does implement the
  specification correctly. Another advantage is that you can develop and
  compare different implementations of the same specification.

- *Develop specifications from
  code*
  You can use |Specware| for reverse engineering -- that is, to help you
  derive a specification from existing code. To do this, you must
  examine the code to determine what problems are being solved by it,
  then use |Specware|'s language |Metaslang| to express the problems as
  specifications. In addition to providing a notation tool for this
  process, |Specware| allows you to operate on the derived
  specification. Once you have derived a specification from the original
  code, you can analyze the specification for correctness and
  completeness, and also generate different and correct implementations
  for it.

The design process in |Specware|
################################

To solve real problems, programs typically combine domain theories
about the physical world with problem solving theories about the
computational world. Your domain theory is an abstract representation
of a real-world problem domain. To implement it, you must transform
the domain theory to a concrete computational model. The built-in
specification libraries describe mathematical and computational
concepts, which are building blocks for an implementation. Your
specifications combine real-world knowledge with this built-in
computational knowledge to generate program code that solves real-
world problems in a rigorous and provable way.

You interpret designs relative to an initial universe of models. In
software design, for example, the models are programs, while in
engineering design, they are circuits or pieces of metal. To design an
object is to choose it from among the universe of possible models. You
make this choice by beginning with an initial description and
augmenting it until it uniquely describes the model you desire. In
|Specware|, this process is called refinement.

Composition and refinement are the basic techniques of application
building in |Specware|. You compose simpler specifications into more
complex ones, and refine more abstract specifications into more
concrete ones. When you refine a specification, you create a more
specific case of it; that is, you reduce the number of possible models
of it.

The process of refinement is also one of composition. To begin the
refinement, you construct primitive refinements that show how to
implement an abstract concept in terms of a concrete concept. You then
compose refinements to deepen and widen the refinement.

For example, suppose you are designing a house. A wide but not deep
view of the design specifies several rooms but gives no details. A
deep but not wide view of the design specifies one room in complete
detail. To complete the refinement, you must create a view that is
both wide and deep; however, it makes no difference which view you
create first.

The final refinement implements a complex, abstract specification from
which code can be generated.

Stages of application building
##############################

Conceptually, there are two major stages in producing a |Specware|
application. In the actual process, steps from these two stages may
alternate.

#. Building a specification

#. Refining your specifications to constructive specifications

Building a specification
========================

You must build a specification that describes your domain theory in
rigorous terms. To do this, you first create small specifications for
basic, abstract concepts, then specialize and combine these to make
them more concrete and complex.

To relate concepts to each other in |Specware|, you use specification
morphisms. A specification morphism shows how one concept is a
specialization or part of another. For example, the concept
"fast car"  specializes both
"car"  and "fast thing". The concept
"room"  is part of the concept
"house". You can specialize "room"  in
different ways, one for each room of the house.

You specialize in order to derive a more concrete specification from a
more abstract specification. Because the specialization relation is
transitive (if A specializes B and B specializes C, then A specializes
C as well), you can combine a series of morphisms to achieve a step-
wise refinement of abstract specifications into increasingly concrete
ones.

You combine specifications in order to construct a more complex
concept from a collection of simpler parts. In general, you increase
the complexity of a specification by adding more structural detail.

|Specware| helps you to handle complexity and scale by providing
composition operators that take small specifications and combine them
in a rigorous way to produce a complex specification that retains the
logic of its parts. |Specware| provides several techniques for
combining specifications, that can be used in combination:

- The import operation allows you to include earlier specifications in a
  later one.

- The translate operation allows you to rename the parts of a
  specification.

- The colimit operation glues concepts together into a shared union
  along shared subconcepts.

A shared union specification combines specializations of a concept.
For example, if you combine
"red car"
with "fast car"  sharing the concept
"car", you obtain the shared union "fast,
red car". If you combine them sharing nothing, you
obtain "red car and fast car", which is two cars
rather than one. Both choices are available.

Refining your specifications to constructive specifications
===========================================================

You combine specifications to extend the refinement iteratively. The
goal is to create a refinement between the abstract specification of
your problem domain and a concrete implementation of the problem
solution in terms of types and operations that ultimately are defined
in the |Specware| libraries of mathematical and computational
theories.

For example, suppose you want to create a specification for a card
game. An abstract specification of a card game would include concepts
such as card, suit, and hand. A refinement for this specification
might map cards to natural numbers and hands to lists containing
natural numbers.

The |Specware| libraries contains constructive specifications for
various types, including natural numbers and lists.

To refine your abstract specification, you build a refinement between
the abstract Hand specification and the List-based specification. When
all types and operations are refined to concrete library-defined types
and operations, the |Specware| system can generate code from the
specification.

Reasoning about your code
#########################

Writing software in |Metaslang|, the specification and programming
language used in |Specware|, brings many advantages. Along with the
previously-mentioned possibilities for incremental development, you
have the option to perform rigorous verification of the design and
implementation of your code, leading to the a high level of assurance
in the correctness of the final application.

Abstractness in |Specware|
==========================

|Specware| allows you to work directly with abstract concepts
independently of implementation decisions. You can put off making
implementation decisions by describing the problem domain in general
terms, specifying only those properties you need for the task at hand.

In most languages, you can declare either everything about a function
or nothing about it. That is, you can declare only its type, or its
complete definition. In |Specware| you must declare the signature of
an operation, but after that you have almost complete freedom in
stating properties of the operation. You can declare nothing or
anything about it. Any properties you have stated can be used for
program transformation.

For example, you can describe how squaring distributes over
multiplication:

.. code-block:: specware

   axiom square_distributes_over_times is
     fa(a, b) square(a * b) = square(a) * square(b)
   

This property is not a complete definition of the squaring operation,
but it is true. The truth of this axiom must be preserved as you
refine the operation. However, unless you are going to generate code
for ``square``\ , you do not need to supply a complete definition.

The completeness of your definitions determines the extent to which
you can generate code. A complete refinement must completely define
the operations of the source theory in terms of the target theory.
This guarantees that, if the target is implementable, the source is
also implementable.

Logical inference in |Specware|
===============================

|Specware| performs inference using external theorem provers; the
distribution includes SRI's SNARK theorem prover. External provers are
connected to |Specware| through logic morphisms, which relate logics
to each other.

You can apply external reasoning agents to refinements in different
ways (although only verification is fully implemented in the current
release of |Specware|).

- Verification tests the correctness of a refinement. For example, you
  can prove that quicksort is a correct refinement of the sorting
  specification.

- Simplification is a complexity-reducing refinement. For example, given
  appropriate axioms, you can rewrite ``3*a+3*b`` to ``3*(a+b)``\ .

- Synthesis derives a refinement for a given specification by combining
  the domain theory with computational theory. For example, you can
  derive quicksort semi-automatically from the sorting specification as
  a solution to a sorting problem, if you describe exactly how the
  problem is a sorting problem.

.. COMMENT: <para>Different provers can provide different functionality.
            Additional provers have been integrated with |Specware|,
            including Stanford Research Institute's SNARK, which may be
            obtained by sending email to Dr. Richard Waldinger
            (<email>waldinge@ai.research.sri.com</email>). In the future,
            additional provers will be provided or enabled.</para>

