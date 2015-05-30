

===========
|Metaslang|
===========

.. COMMENT:  ***************************************************************** 

This chapter introduces the |Metaslang| specification language.

.. COMMENT:  ================================================================= 

The following sections give the grammar rules and meaning for each
|Metaslang| language construct.

.. COMMENT:  ================================================================= 

Preliminaries
#############

.. COMMENT:  ================================================================= 

The Grammar Description Formalism
=================================

The grammar rules used to describe the |Metaslang| language use the
conventions of (extended) BNF. For example, a grammar rule like:

.. productionlist::
  wiffle: `waffle` [ `waffle_tail` ] | 
        : `piffle` { + `piffle` }*

defines a :token:`wiffle` to be: either a :token:`waffle` optionally
followed by a :token:`waffle_tail`, or a sequence of one or more
:token:`piffles` separated by terminal symbols ``+`` . (Further rules
would be needed for :token:`waffle`, :token:`waffle_tail` and
:token:`piffle`.) In a grammar rule the left-hand side of ``::=``
shows the kind of construct being defined, and the right-hand side
shows how it is defined in terms of other constructs. The sign ``|``
separates alternatives, the square brackets ``[`` ... ``]`` enclose
optional parts, and the curly braces plus asterisk ``{`` ... ``}*``
enclose a part that may be repeated any number of times, including
zero times. All other signs stand for themselves, like the symbol
``+`` in the example rule above.

.. COMMENT:  ================================================================= 

In the grammar rules terminal symbols appear in a bold font. Some of
the terminal symbols used, like ``|`` and ``{``, are very similar to
the grammar signs like ``|`` and ``{`` as described above. They can
hopefully be distinguished by their bold appearance.

.. COMMENT:  ================================================================= 

Grammar rules may be
*recursive*: a
construct may be defined in terms of itself, directly or
indirectly.
For example, given the rule:

.. productionlist::
  piffle: 1 | 
        : M { `piffle` }*

here are some possible :token:`piffles`:

.. code-block:: specware

   1       M       M1      M111    MMMM    M1M1
   

Note that the last two examples of :token:`piffles` are ambiguous.
For example, ``M1M1`` can be interpreted as:
``M`` followed by the two :token:`piffles` ``1`` and ``M1``,
but also as:
``M`` followed by the three :token:`piffles` ``1``, ``M``, and another
``1``.
Some of the actual grammar rules allow ambiguities; the
accompanying text will indicate how they are to be resolved.

.. COMMENT:  ================================================================= 

Models
======

.. productionlist::
  op: `op_name`

In |Metaslang|,
":token:`op`"  is used
used as an abbreviation for
":token:`op_name`", where :token:`op_names`
are declared :token:`names` representing values.
(*Op*  for *operator*, a
term used for historical reasons, although including
things normally not considered operators.)

.. productionlist::
  spec: `spec_form`

The term :token:`spec` is used as short for :token:`spec_form`. The
*semantics*  of |Metaslang| :token:`specs` is given
in terms of classes of *models*.
A model is an assignment of "types" to all the
:token:`type_names` and of "typed" values to all the :token:`ops`
declared -- explicitly or implicitly -- in the :token:`spec`.
The notion of *value*  includes
numbers, strings, arrays, functions, et cetera.
Each type has a set of "inhabitants", which are similar values.
A typed value can be thought of as a pair (*T*, *V*),
in which *T* is a type and *V* is a value that is an
inhabitant of *T*.
For example, the :token:`expressions` ``0 : Nat`` and ``0 : Integer``
correspond, semantically, to the typed values
(*N*, 0) and
(*Z*, 0), respectively,
in which
*N* stands for the type of
natural numbers {0, 1, 2, ...}, and 
*Z* for the type of
integers {..., -2, -1, 0, 1, 2, ...}.
For example, given this :token:`spec`:

.. code-block:: specware

   spec
     type Even
     op next : Even -> Even
     axiom nextEffect is
       fa(x : Even) ~(next x = x)
   end-spec
   

one possible model (out of many!) is the assignment of
the even integers to ``Even``, and of the function that
increments an even number by 2 to ``next``.

.. COMMENT:  ================================================================= 

Each model has to
*respect typing*; for
example, given the above assignment to ``Even``, the function
that increments a number by 1 does not map all even numbers
to even numbers, and therefore can not -- in the same model
-- be assigned to ``next``.
Additionally, the :token:`claims` (axioms, theorems and conjectures)
of the :token:`spec` have to be satisfied in the model.
The axiom labeled ``nextEffect`` above states that
the function assigned to :token:`op` ``next``
maps any value of the type assigned to :token:`type_name` ``Even``
to a different value.
So the squaring function, although type-respecting, could not
be assigned to ``next`` since it maps 0 to itself.

.. COMMENT:  ================================================================= 

If all type-respecting combinations of assignments of types to
:token:`type_names` and values to :token:`ops` fail the one or more
:token:`claims`, the :token:`spec` has no models and is called
*inconsistent*.
Although usually undesirable, an inconsistent :token:`spec` is not by
itself considered ill formed.
The |Specware| system does not attempt to detect
inconsistencies, but associated provers can sometimes be
used to find them.
Not always; in general it is undecidable whether a
:token:`spec` is consistent or not.

.. COMMENT:  ================================================================= 

In general, the meaning of a construct in a model depends on the
assignments of that model, and more generally on an
*environment*: a model possibly extended
with assignments to :token:`local_variables`.
For example, the meaning of the :token:`claim`
``fa(x : Even) ~(next x = x)`` in axiom ``nextEffect``
depends on the meanings of ``Even`` and ``next``,
while the sub-expression ``next x``, for example, also depends on
an assignment (of an "even" value) to ``x``.
To avoid laborious phrasings, the semantic descriptions use
language like "the function ``next`` applied to
``x``\ " as shorthand for this lengthy phrase:
"the function assigned in the environment to ``next`` applied
to the value assigned in the environment to ``x``\ ".

.. COMMENT:  ================================================================= 

When an environment is extended with an assignment to a
:token:`local_variable`, any assignments to synonymous :token:`ops` or
other :token:`local_variables` are superseded by the new assignment in
the new environment. In terms of |Metaslang| text, within the scope of
the binding of :token:`local_variables`, synonymous :token:`ops` and
earlier introduced :token:`local_variables` (that is, having the same
:token:`simple_name`) are "hidden"; any use of the
:token:`simple_name` in that scope refers to the textually most
recently introduced :token:`local_variable`. For example, given:

.. code-block:: specware

   op x : String = "op-x"
   op y : String = let v = "let-v" in x
   op z : String = let x = "let-x" in x
   

the value of ``y`` is ``"op-x"`` (:token:`op` ``x`` is not hidden by
the :token:`local_variable` ``v`` of the :token:`let_binding`),
whereas the value of ``z`` is ``"let-x"`` (:token:`op` ``x``
*is*
hidden by the :token:`local_variable` ``x`` of the :token:`let_binding`).

.. COMMENT:  ================================================================= 

Type-correctness
================

Next to the general requirement that each model respects typing, there
are specific restrictions for various constructs that constrain the
possible types for the components. For example, in an
:token:`application` ``f(x)``, the type of the
:token:`actual_parameter` ``x`` has to match the domain type of
function ``f``. These requirements are stated in the relevant
sections of this language manual. If no type-respecting combinations
of assignments meeting all these requirements exist for a given
:token:`spec`, it is considered
*type-incorrect*  and therefore
*ill formed*.
This is determined by |Specware| while elaborating the :token:`spec`,
and signaled as an error.
Type-incorrectness differs from inconsistency in that the
meaning of the :token:`claims` does not come into play, and the
question whether an ill-formed :token:`spec` is consistent is moot.

.. COMMENT:  ================================================================= 

To be precise, there are subtle and less subtle differences between
type-incorrectness of a :token:`spec` and its having no type-
respecting combinations of assignments. For example, the following
:token:`spec` is type-correct but has no models:

.. code-block:: specware

   spec
     type Empty = | Just Empty
     op IdoNotExist : Empty
   end-spec
   

The explanation is that the :token:`type_definition` for ``Empty``
generates an
*implicit*  axiom that all
inhabitants of the type ``Empty`` must satisfy, and for this
recursive definition the axiom effectively states that such
creatures can't exist: the type ``Empty`` is uninhabited.
That by itself is no problem, but precludes a type-respecting
assignment of an inhabitant of ``Empty`` to :token:`op` ``IdoNotExist``.
So the :token:`spec`, while type-correct, is actually inconsistent.
See further under :ref:`Type-definitions <Type-definitions>`.

.. COMMENT:  ================================================================= 

Here is a type-incorrect :token:`spec` that has type-respecting
combinations of assignments:

.. code-block:: specware

   spec
     type Outcome = | O.Positive | O.Negative
     type Sign = | S.Positive | S.Zero | S.Negative
     def whatAmI = Positive
   end-spec
   

Here there are two constructors ``O.Positive`` and ``S.Positive`` of different types, the
type ``Outcome`` and the type ``Sign`` respectively. That by itself is fine, but
when such "overloaded" constructors are used without a :token:`qualifier`, the context must give
sufficient information which is meant. Here, the use of ``Positive``
in the :token:`definition` for :token:`op` ``whatAmI`` may refer to either ``O.Positive`` 
or ``S.Positive``; as used it is *type-ambiguous*.
|Metaslang| allows omitting type information provided that, given
a type assignment to all :token:`local_type_variables` in scope, unique
types for all typed constructs, such as :token:`expressions` and
:token:`patterns`, can be inferred from the context.
If no complete and unambiguous type-assignment can be made,
the :token:`spec` is not accepted by the |Specware| system.
Type-ambiguous :token:`expressions` can be disambiguated either by using the 
full qualified name or by using a :token:`type_annotation`, as described under 
:ref:`Annotated-expressions <Annotated-expressions>`.
In the example, the :token:`definition` of ``whatAmI`` can be disambiguated in any
of the following ways:

.. code-block:: specware

   def whatAmI : Sign = Positive
   def whatAmI = Positive : Sign
   def whatAmI = S.Positive
   

Also, if the :token:`spec` elsewhere contains something along the lines of:

.. code-block:: specware

   op signToNat : Sign -> Nat
   def sw = signToNat whatAmI
   

that is sufficient to establish that ``whatAmI`` has type ``Sign``
and thereby disambiguate the use of ``Positive``.
See further under
:ref:`Op-definitions <Op-definitions>`
and :ref:`Structors <Structors>`.

.. COMMENT:  ================================================================= 

Constructive
============

When code is generated for a :token:`spec`, complete "self-contained"
code is only generated for :token:`type_definitions` and
:token:`op_definitions` that are fully
*constructive*.
Non-constructiveness is "contagious":
a :token:`definition` is only constructive if all components of the
definition are.
The type of a :token:`type_name` without :token:`definition` is not
constructive.
A type is only constructive if all component types are.
An :token:`op` without :token:`definition` is non-constructive, and so
is an :token:`op` whose type is non-constructive.
A :token:`quantification` is non-constructive.
The polymorphic :token:`inbuilt_op` ``=`` for testing equality and its inequality
counterpart ``~=`` are only
constructive for *discrete types*  (see
below).

.. COMMENT:  ================================================================= 

A type is called discrete if the equality predicate ``=`` for that
type is constructive. The inbuilt and base-library types ``Bool``\
, ``Integer``, ``NonZeroInteger``, ``Nat``, ``PosNat``,
``Char``, ``String`` and ``Compare`` are all discrete. Types
``List`` *T* and ``Option`` *T* are discrete when *T* is. All
function types are non-discrete (even when the domain type is the unit
type). Sum types, product types and record types are discrete whenever
all component types are. Subtype ``(``\ *T*\ ``|``\ *P*\ ``)`` is
discrete when supertype *T* is. (Predicate *P* need not be
constructive: the equality test is that of the supertype.) Quotient
type *T*\ ``/``\ *Q*\ is discrete when predicate *Q* is
constructive. (Type *T* need not be discrete: the equality test on the
quotient type is just the predicate *Q* applied to pairs of members of
the *Q*-equivalence classes.)

.. COMMENT:  ***************************************************************** 

Lexical conventions
###################

A |Metaslang| text consists of a sequence of :token:`symbols`,
possibly interspersed with whitespace. The term
*whitespace*  refers to any
non-empty sequence of spaces, tabs, newlines, and :token:`comments`
(described below).
A :token:`symbol` is presented in the text as a sequence of one or
more "marks" (ASCII characters).
Within a composite (multi-mark) :token:`symbol`, as well as within a
:token:`unit_identifier`, no whitespace is
allowed, but whitespace may be needed between two :token:`symbols` if
the first mark of the second :token:`symbol` could be taken to be the
continuation of the first :token:`symbol`.
More precisely, letting *X*, *Y* and *Z* stand for arbitrary (possibly
empty) sequences of :token:`marks`, and *m* for a single mark, then
whitespace is required between two adjacent
:token:`symbols`, the first being *X* and the second *mY*, when for some *Z* the
sequence *XmZ* is also a :token:`symbol`.
So, for example, whitespace is required where shown in ``succ 0`` and
``op! :Nat->Nat``, since ``succ0`` and ``!:`` are valid :token:`symbols`, but
none is required in the :token:`expression` ``n+1``.

.. COMMENT:  ================================================================= 

Inside :token:`literals` (constant-denotations) whitespace is also
disallowed, except for ":token:`significant_whitespace`" as described
under
:ref:`String-literals <String-literals>`.

.. COMMENT:  ================================================================= 

Other than that, whitespace -- or the lack of it -- has no
significance. Whitespace can be used to lay-out the text for
readability, but as far as only the meaning is concerned, the
following two presentations of the same :token:`spec` are entirely
equivalent:

.. code-block:: specware

   spec
     type Even
     op next : Even -> Even
     axiom nextEffect is
       fa(x : Even) ~(next x = x)
   end-spec
   
   spec type   Even op   next : Even -> Even axiom nextEffect
   is fa(x : Even)~(next     x            = x)end-spec
   

.. COMMENT:  ***************************************************************** 

Symbols and Names
=================

.. productionlist::
  symbol: `simple_name` | 
        : `literal` | 
        : `special_symbol`
  simple_name: `first_syllable` { _ `next_syllable` }*
  first_syllable: `first_word_syllable` | 
                : `non_word_syllable`
  next_syllable: `next_word_syllable` | 
               : `non_word_syllable`
  first_word_syllable: `word_start_mark` { `word_continue_mark` }*
  next_word_syllable: `word_continue_mark` { `word_continue_mark` }*
  word_start_mark: `letter`
  word_continue_mark: `letter` | `decimal_digit` | ' | ?
  letter: A | B | C | D | E | F | 
        : G | H | I | J | K | L |
        : M | N | O | P | Q | R | 
        : S | T | U | V | W | X | 
        : Y | Z | a | b | c | d | 
        : e | f | g | h | i | j | 
        : k | l | m | n | o | p | 
        : q | r | s | t | u | v | 
        : w | x | y | z
  decimal_digit: 0 | 1 | 2 | 3 | 4 | 5 | 
               : 6 | 7 | 8 | 9
  non_word_syllable: `non_word_mark` { `non_word_mark` }*
  non_word_mark: ` | ~ | ! | @ | $ | ^ | 
               : & | * | - | = | + | \ | 
               : "|" | : | < | > | / | ' | 
               : ?
  special_symbol: _ | ( | ) | "[" | "]" | 
                : "{" | "}" | ; | , | .

Sample :token:`simple_names`:

.. code-block:: specware

   Date                    **$*            ?!
   yymmdd2date             <*>           :=:
   well_ordered?           ~==           x'
   c_<+>                   /_47a
   

For convenience, here are the 13 printing ASCII marks that, next to
:token:`letters` and :token:`decimal_digits`, can
*not*  occur as a :token:`non_word_mark`:

.. code-block:: specware

   #    %    "    _    ;    ,    .
   (    )    [    ]    {    }
   

Restriction.
As mentioned before, no whitespace is allowed in :token:`symbols`:
while ``anode`` is a single :token:`simple_name`, both ``a node`` and
``an ode`` consist of two :token:`simple_names`.
Further, the case (lower or upper) of :token:`letters` in :token:`simple_names` is
significant: ``grandparent``, ``grandParent`` and
``grandpaRent`` are three different :token:`simple_names`.

.. COMMENT:  ================================================================= 

Restriction. In general, :token:`simple_names` can be chosen freely.
However, the following
*reserved symbols*  have a
special meaning and must not be used for :token:`simple_names`:

.. COMMENT:  Moved this inline, instead of in a separate file 

.. code-block:: specware

   as           embed     from       let           quotient
   axiom        embed?    generate   morphism      spec
   by           endspec   if         obligations   the
   case         ex        import     of            then
   choose       ex1       in         op            theorem
   conjecture   fa        infixl     project       true
   def          false     infixr     prove         type
   else         fn        is         qualifying    where
   
   :        ||       |       =        <=>       <-       <<
   ::       &&       ~=      =>        ->       +->
   

They each count as a single :token:`symbol`, and no whitespace is
allowed inside any reserved symbol.

.. COMMENT:  ================================================================= 

:token:`Non_word_syllables` can be used to choose convenient
:token:`simple_names` for :token:`ops` that, conventionally, are
written with non-alphabetic marks.

.. COMMENT:  ================================================================= 

Some |Metaslang| users follow the convention of using
:token:`simple_names` that start with a capital letter for
:token:`unit_identifiers` and :token:`type_names` and for
:token:`constructor ops`, while :token:`simple_names` chosen for
non-constructor :token:`ops` and :token:`field_names` start with a lower-case
:token:`letter`. Both plain :token:`local_variables` and
:token:`local_type_variables` are often chosen to be single lower-case
:token:`letters`: ``x``, ``y``, ``z``, ``a``, ``b``, ``c``, with the
start of the alphabet preferred for
:token:`local_type_variables`. :token:`Op_names` of predicates (that
is, having some type *T* ``-> Bool``\ ) often end with the mark
``?``. These are just conventions that users are free to follow or
ignore.

.. COMMENT:  ***************************************************************** 

Comments
========

.. productionlist::
  comment: `line_end_comment` | 
         : `block_comment`
  line_end_comment: % `line_end_comment_body`
  line_end_comment_body: `any_text_up_to_end_of_line`
  block_comment: (* `block_comment_body` *)
  block_comment_body: `any_text_including_newlines_and_nested_block_comments`

Sample :token:`comments`:

.. code-block:: specware

   % keys must be unique
   (* op yymmdd2Date : String -> Date *)
   

|Metaslang| allows two styles of :token:`comments`. The ``%``\ -style
is light-weight, for adding comment on a line
*after*  the formal text (or
taking a line on its own, but always confined to
a single line).
The ``(*``...\ ``*)``\ -style can be used for blocks of text,
spanning several lines, or stay within a line.
Any text remaining on the line after the closing ``*)`` is
processed as formal text.
:token:`Block_comments` may be nested, so the pairs of brackets
``(*`` and ``*)`` must be balanced.

A :token:`block_comment` can not contain a :token:`line_end_comment`
and vice versa: whichever starts first has "the right of way". For
example, ``(* 100 % or more! *)`` is a :token:`block_comment` with
:token:`block_comment_body` ``100 % or more!`` \ . The ``%`` here is a
mark like any other; it does not introduce a
:token:`line_end_comment`. Conversely, in the
:token:`line_end_comment` ``% op <*< stands for (*)`` the ``(*`` is
part of the :token:`line_end_comment_body`; it does not introduce a
:token:`block_comment`. Note also that ``%`` and ``(*`` have no
special significance in :token:`literals` (which must not contain
whitespace, including :token:`comments`): ``"100 % or more!"`` is a
well-formed :token:`string_literal`.

.. COMMENT:  ***************************************************************** 

Units
#####

A "unit" is an identifiable :token:`unit_term`, where "identifiable"
means that the :token:`unit_term` can be referred to by a
:token:`unit_identifier`. :token:`Unit_terms` can be "elaborated",
resulting in :token:`specs`, morphisms, diagrams or other entities.
The effect of elaborating a :token:`unit_definition` is that its
:token:`unit_term` is elaborated and becomes associated with its
:token:`unit_identifier`.

For the elaboration of a :token:`unit_term` to be meaningful, it has
to be well formed and result in a well-formed -- and therefore type-
correct -- entity. Well-formedness is a stricter requirement than
type-correctness. If a :token:`unit_term` or one of its constituent
parts does not meet any of the restrictions stated in this language
manual, it is ill formed. This holds throughout, also if it is not
mentioned explicitly for some syntactic construct. Well-formedness is
more than a syntactic property; in general, to establish well-
formedness it may be necessary to "discharge" (prove) proof
obligations engendered by the :token:`unit_term`.

A |Specware| project consists of a collection of |Metaslang|
:token:`unit_definitions`. They can be recorded in one or more
|Specware| files. There are basically two styles for recording
:token:`unit_definitions` using |Specware| files. In the single-unit
style, the file, when processed by |Specware|, contributes a single
:token:`unit_definition` to the project. In the multiple-unit style,
the file may contribute several :token:`unit_definitions`. The two
styles may be freely mixed in a project (but not in the same
|Specware| file). This is explained in more detail in what follows.

.. productionlist::
  unit_definition: `unit_identifier` = `unit_term`
  unit_term: `spec_term` | 
           : `morphism_term` | 
           : `diagram_term` | 
           : `target_code_term` | 
           : `proof_term`
  specware_file_contents: `unit_term` | 
                        : `infile_unit_definition` { `infile_unit_definition` }*
  infile_unit_definition: `fragment_identifier` = `unit_term`
  fragment_identifier: `simple_name`

.. COMMENT: ** ||     | :token:`let_term`
            ** ||     | :token:`where_term`

:token:`Unit_definitions` may use other :token:`unit_definitions`,
including standard libraries, which in |SpecwareV| are supposed to be
part of each project. However, the dependencies between units must not
form a cycle; it must always be possible to arrange the
:token:`unit_definitions` in an order in which later
:token:`unit_definitions` only depend on earlier ones. How
:token:`unit_definitions` are processed by |Specware| is further dealt
with in the
|Specware| User Manual.

As mentioned above, :token:`unit_definitions` are collected in
|Specware| files, which in |SpecwareV| must have an ``.sw`` extension.
The |Specware| files do not directly contain the
:token:`unit_definitions` that form the project. In fact, a user never
writes :token:`unit_definition` explicitly. These are instead
determined from the contents of the |Specware| files using the
following rules. There are two possibilities here. The first is that
the :token:`specware_file_contents` consists of a single
:token:`unit_term`. If ``*P*.sw`` is the path for the |Specware| file,
the unit being defined has as its :token:`unit_identifier` *P*. For
example, if file ``C:/units/Layout/Fixture.sw`` contains a single
:token:`unit_term` *U*, the :token:`unit_identifier` is
``/units/Layout/Fixture``, and the :token:`unit_definition` it
contributes to the project is

.. code-block:: specware

   /units/Layout/Fixture = *U*
   

(Note that this is not allowed as an :token:`infile_unit_definition`
in a :token:`specware_file_contents`, since the
:token:`unit_identifier` is not a :token:`fragment_identifier`.)

The second possibility is that the |Specware| file contains one or
more :token:`infile_unit_definitions`. If *I* is the
:token:`fragment_identifier` of such an
:token:`infile_unit_definition`, and ``*P*.sw`` is the path for the
|Specware| file, the unit being defined has as its
:token:`unit_identifier` *P*#*I*. For example, if file
``C:/units/Layout/Cart.sw`` contains an
:token:`infile_unit_definition` ``Pos =``\ *U*\ \ , the
:token:`unit_identifier` is ``/units/Layout/Cart#Pos``, and the
:token:`unit_definition` it contributes to the project is

.. code-block:: specware

   /units/Layout/Cart#Pos = *U*
   

.. COMMENT:  ***************************************************************** 

Unit Identifiers
================

.. productionlist::
  unit_identifier: `swpath_based_path` | 
                 : `relative_path`
  swpath_based_path: / `relative_path`
  relative_path: { `path_element` / }* `path_element` [ # `fragment_identifier` ]
  path_element: `path_mark` { `path_mark` }*
  path_mark: `letter` | `decimal_digit` | 
           : ! | * | & | " | + | 
           : - | = | 
           : @ | ^ | ` | ~ | .

:token:`Unit_identifiers` are used to identify :token:`unit_terms`, by
identifying files in a file store that contain :token:`unit_terms` or
:token:`infile_unit_definitions`. Which :token:`path_marks` can
actually be used in forming a :token:`path_element` may depend on
restrictions of the operating system. The :token:`path_elements`
``..`` and ``.`` have special meanings: "parent folder" and "this
folder". Under than this use, the mark ``.`` should not be used as the
first or last :token:`path_mark` of a :token:`path_element`.

Typically, only a final part of the full :token:`unit_identifier` is
used. When |Specware| is started with environment variable ``SWPATH``
set to a semicolon-separated list of pathnames for directories, the
|Specware| files are searched for relative to these pathnames; for
example, if ``SWPATH`` is set to
``C:/units/Layout;C:/units/Layout/Cart``, then
``C:/units/Layout/Fixture.sw`` may be shortened to ``/Fixture``, and
``C:/units/Layout/Cart.sw`` to ``/Cart``. How
:token:`unit_definitions` are processed by |Specware| is further dealt
with in the
|Specware| User Manual.

Further, :token:`unit_identifiers` can be relative to the directory
containing the |Specware| file in which they occur. So, for example,
both in file ``C:/units/Layout/Fixture.sw`` and in file
``C:/units/Layout/Cart.sw``, :token:`unit_identifier` ``Tools/Pivot``
refers to the :token:`unit_term` contained in file
``C:/units/Layout/Tools/Pivot.sw``, while ``Props#SDF`` refers to the
:token:`unit_term` of :token:`infile_unit_definition` ``SDF = ...``
contained in file ``C:/units/Layout/Props.sw``. As a special case, a
:token:`unit_term` with the same :token:`name` as the file may be
referenced without a :token:`fragment_identifier`. For example, in the
current case, if the file ``C:/units/Layout/Props.sw`` contains the
:token:`unit_term` of :token:`infile_unit_definition` ``Props = ...``\
, then this :token:`unit_term` can be referred to either by
``Props#Props`` or ``Props``.

The :token:`unit_identifier` must identify a :token:`unit_definition`
as described above; the elaboration of the :token:`unit_identifier` is
then the result of elaborating the corresponding :token:`unit_term`,
yielding a :token:`spec`, morphism, diagram, or other entity.

.. COMMENT:  ***************************************************************** 

Specs
=====

.. productionlist::
  spec_term: `unit_identifier` | 
           : `spec_form` | 
           : `spec_qualification` | 
           : `spec_translation` | 
           : `spec_substitution` | 
           : `diagram_colimit` | 
           : `obligator`

.. COMMENT: ||     | :token:`spec_visibility`

Restriction.
When used as a :token:`spec_term`, the elaboration of a
:token:`unit_identifier` must yield a :token:`spec`.

The elaboration of a :token:`spec_term`, if defined, yields an
"expanded" :token:`spec_form` as defined in the next subsection.

.. COMMENT:  ***************************************************************** 

Spec Forms
----------

.. productionlist::
  spec_form: spec { `declaration` }* end-spec

Sample :token:`spec_forms`:

.. code-block:: specware

   spec import Measures, Value end-spec
   

.. COMMENT:  ================================================================= 

An
*expanded*  :token:`spec_form` is a :token:`spec_form`
containing no :token:`import_declarations`.

The elaboration of a :token:`spec_form` yields the |Metaslang| text
which is that :token:`spec` itself, after expanding any
:token:`import_declarations`. The
*meaning*  of that text is the class
of models of the :token:`spec`, as described throughout this
Chapter.

.. COMMENT:  ***************************************************************** 

Qualifications
--------------

.. COMMENT: ====================================================================

:token:`Names` of types and :token:`ops` may be
*simple*
or *qualified*.
The difference is that :token:`simple_names` are "unqualified": they
do not contain a
dot sign "\ ``.``\ ", while :token:`qualified_names` are prefixed with
a ":token:`qualifier`" followed by a dot.  Examples of
:token:`simple_names` are ``Date``, ``today`` and ``<*<``.
Examples of :token:`qualified_names` are 
``Calendar.Date``, ``Calendar.today`` and ``Monoid.<*<``.

:token:`Qualifiers` can be used to disambiguate. For example, there
may be reason to use two different :token:`ops` called ``union`` in
the same context: one for set union, and one for bag (multiset) union.
They could then more fully be called ``Set.union`` and ``Bag.union``\
, respectively. Unlike in earlier versions of |Specware|, there is no
rigid relationship between :token:`qualifiers` and the
:token:`unit_identifiers` identifying :token:`specs`. The author of a
collection of :token:`specs` may use the :token:`qualifier` deemed
most appropriate for any :token:`type_name` or :token:`op_name`. For
example, there could be a single :token:`spec` dubbed ``SetsAndBags``
that introduces two new :token:`ops`, one called ``Set.union`` and one
called ``Bag.union``. Generally, types and :token:`ops` that "belong
together" should receive the same :token:`qualifier`. It is up to the
author of the :token:`specs` to determine what belongs together.

:token:`Type_names` and :token:`op_names` are
*introduced*  in a
:token:`declaration` or :token:`definition`, and may then be
*employed*  elsewhere in the same :token:`spec`.
Thus, all occurrences of a :token:`type_name` or :token:`op_name` can be divided
into "introductions" and "employs".
The :token:`name` as introduced in an introduction is the 
*full*  :token:`name` of the type or :token:`op`.
If that :token:`name` is a :token:`simple_name`, the full :token:`name` is a :token:`simple_name`.
If the :token:`name` as introduced is a :token:`qualified_name`, then so is the full
:token:`name`.

For employs the rules are slightly different. First, if the
:token:`name` employed occurs just like that in an introduction, then
it is the full :token:`name`. Also, if the :token:`name` employed is
qualified, it is the full :token:`name`. Otherwise, the :token:`name`
as employed may be unqualified shorthand for a qualified full
:token:`name`. For example, given an employ of the unqualified
:token:`type_name` ``Date``, possible qualified full :token:`names`
for it are ``Calendar.Date``, ``DateAndTime.Date``,
``Diary.Date``, and so on. But, of course, the full :token:`name`
must be one that is introduced in the :token:`spec`. If there is
precisely one :token:`qualified_name` introduced whose last part is
the same as the :token:`simple_name` employed, then that :token:`name`
is the full :token:`name`. Otherwise, type information may be employed
to disambiguate ("resolve overloading").

Here is an illustration of the various possibilities:

.. code-block:: specware

   spec
     type Apple
     type Fruit.Apple
     type Fruit.Pear
     type Fruit.Date
     type Calendar.Date
     type Fruit.Basket = Apple * Pear * Date
   end-spec
   

In the definition of type ``Fruit.Basket`` we have three unqualified
employs of :token:`type_names`, viz. ``Apple``, ``Pear`` and
``Date``. The :token:`name` ``Apple`` is introduced like that, so
the employ ``Apple`` already uses the full :token:`name`; it does not
refer to ``Fruit.Apple``. The :token:`name` ``Pear`` is nowhere
introduced just like that, so the employ must be shorthand for some
qualified full :token:`name`. There is only one applicable
introduction, namely ``Fruit.Pear``. Finally, for ``Date`` there are
two candidates: ``Fruit.Date`` and ``Calendar.Date``. This is
ambiguous, and in fact an error. To correct the error, the employ of
``Date`` should be changed into either ``Fruit.Date`` or
``Calendar.Date``, depending on the intention.

It is possible to give a qualification in one go to all
:token:`simple_names` introduced in a :token:`spec`. If *Q* is a
:token:`qualifier`, and *S* is a term denoting a :token:`spec`, then
the term *Q* ``qualifying`` *S* denotes the same :token:`spec` as *S*,
except that each introduction of an :token:`simple_name` *N* is
replaced by an introduction of the :token:`qualified_name` \ *Q*\
``.``\ *N*\ \ . Employs that before referred to the unqualified
introduction are also accordingly qualified, so that they now refer to
the qualified introduction. For example, the value of

.. code-block:: specware

   Company qualifying spec
     type Apple
     type Fruit.Apple
     type Fruit.Pear
     type Fruit.Basket = Apple * Pear
   end-spec
   

is the same as that of

.. code-block:: specware

   spec
     type Company.Apple
     type Fruit.Apple
     type Fruit.Pear
     type Fruit.Basket = Company.Apple * Fruit.Pear
   end-spec
   

.. COMMENT: ====================================================================

.. productionlist::
  spec_qualification: `qualifier` qualifying `spec_term`
  qualifier: `simple_name`
  name: `simple_name` | 
      : `qualified_name`
  qualified_name: `qualifier` . `simple_name`

Restriction. A :token:`spec_qualification` is a special kind of
translation, allowing for the renaming of :token:`type_names` and
:token:`op_names` declared in a :token:`spec`. Like for
:token:`spec_translations`, it is not allowed to rename a
:token:`type_name` to become the same :token:`name` as a previously
existing (and different) :token:`type_name`, or to rename an
:token:`op_name` to become the same :token:`name` as a previously
existing (and different) :token:`op_name`.

Sample :token:`names`:

.. code-block:: specware

   Key                **
   Calendar.Date      Monoid.<*<
   

Sample :token:`spec_qualification`:

.. code-block:: specware

   Weight qualifying /Units#Weights
   

Let *R* be the result of elaborating :token:`spec_term` *S*. Then the
elaboration of \ *Q* ``qualifying`` *S*\ \ , where *Q* is a
:token:`qualifier`, is *R* with each unqualified :token:`type_name`,
:token:`op_name` or :token:`claim_name` *N* introduced there replaced
by the :token:`qualified_name` \ *Q*\ ``.``\ *N*\ \ . The same
replacement applies to all employs of *N* identifying that introduced
:token:`simple_name`. As always, the result of the replacement is
required to be a well-formed :token:`spec`.

For example, the elaboration of

.. code-block:: specware

   Buffer qualifying spec
     op size : Nat
     axiom LargeSize is size >= 1024
   end-spec
   

results in:

.. code-block:: specware

   spec
     op Buffer.size : Nat
     axiom Buffer.LargeSize is Buffer.size >= 1024
   end-spec
   

Because of the restriction on collisions, the following is illegal, as
``f`` in the original :token:`spec` would be renamed to collide with
the pre-existing (and distinct!) ``X.f``.

.. code-block:: specware

   X qualifying spec
     op  X.f : Nat
     def f = 3
   end-spec
   

.. COMMENT:  ***************************************************************** 

Translations
------------

.. productionlist::
  spec_translation: translate `spec_term` by `name_map`
  name_map: "{" [ `name_map_item` { , `name_map_item` }* ] "}"
  name_map_item: `type_name_map_item` | 
               : `op_name_map_item` | 
               : `wildcard_map_item`
  type_name_map_item: [ type ] `name` +-> `name`
  op_name_map_item: [ op ] `annotable_name` +-> `annotable_name`
  annotable_name: `name` [ `type_annotation` ]
  type_annotation: : `type_descriptor`
  wildcard_map_item: `wildcard` +-> `wildcard`
  wildcard: `simple_wildcard` | 
          : `qualified_wildcard`
  simple_wildcard: _
  qualified_wildcard: `qualifier` . `simple_wildcard`

Restriction. The :token:`name_map` of a :token:`spec_translation` may
not contain more than one :token:`name_map_item` pertaining to the
same :token:`type_name` or the same :token:`op_name` in the
:token:`spec` resulting from elaborating the :token:`spec_term`. For
example, the following is not a lawful :token:`spec_translation`:

.. code-block:: specware

   translate spec type T end-spec by {T +-> A, T +-> B}
   

Restriction. A :token:`spec_translation` may not map two different
:token:`type_names` or two different :token:`op_names` to the same
:token:`simple_name`. Note that this implies that :token:`type_names`
and :token:`op_names` cannot be translated to :token:`simple_names`
defined in the base libraries.

Sample :token:`spec_translation`:

.. code-block:: specware

   translate A by {Counter +-> Register, tally +-> incr}
   

Let *R* be the result of elaborating :token:`spec_term` *S*. In
elaborating a :token:`spec_translation`, first any
:token:`wildcard_map_items` are expanded as follows. A
:token:`simple_wildcard` matches each :token:`simple_name` that is a
:token:`type_name` or :token:`op_name` of *S*. A
:token:`qualified_wildcard` \ *Q*\ ``._`` matches each
:token:`qualified_name` having the same :token:`qualifier` *Q* that is
a :token:`type_name` or :token:`op_name` of *S*. A
:token:`wildcard_map_item` \ *W0*\ ``+->``\ *W1*\ is expanded into a
list of :token:`name_map_items` not containing :token:`wildcards` by
taking each :token:`name` *N* matched by *W0*, and replacing both
:token:`simple_wildcards` occurring in \ *W0*\ ``+->``\ *W1*\ by the
:token:`simple_name` of *N*, that is, *N* with a possible
qualification stripped off. After expansion, the elaboration of
``translate`` *S* ``by {`` *M*\ :sub:`1` ``+->`` *N*\ :sub:`1`,
``...`` *M*\ :sub:`n` ``+->`` *N*\ :sub:`n` ``}``
is *R* with each occurrence of a :token:`name`
*M*\ :sub:`i` replaced by *N*\ :sub:`i`.
All other :token:`names` are mapped to themselves, i.e., they are unchanged.
The presence of a :token:`type_annotation` in a :token:`name_map_item`, as in
``E +-> cross``, indicates that the :token:`name_map_item` refers to an :token:`op_name`;
additionally, on the left-hand side such an annotation may serve to disambiguate
between several synonymous :token:`ops`, and then there must be an :token:`op` in *R* of
the type given by the :token:`type_descriptor`.
If the right-hand side of a :token:`name_map_item` carries a type
annotation, its :token:`type_descriptor` must conform to the type of
the :token:`op_name` in the resulting :token:`spec`.
Without such annotation on either side, if a :token:`name`
to be translated is introduced both as a :token:`type_name` and as an
:token:`op_name` in *R*, it must be preceded by ``type`` or ``op`` to
indicate which of the two is meant.
Otherwise the indication ``type`` or ``op`` is not
required, but allowed; if present, it must correspond to the kind of
:token:`simple_name` (:token:`type_name` or :token:`op_name`) to be translated.

For example, the elaboration of

.. code-block:: specware

   translate spec
     type E
     op i : E
   end-spec by {
     E +-> Counter,
     i +-> reset
   }
   

results in:

.. code-block:: specware

   spec
     type Counter
     op reset : Counter
   end-spec
   

To illustrate the use of :token:`wildcards`: The elaboration of

.. code-block:: specware

   translate spec
     type M.Length
     op M.+ infixl 25 : M.Length * M.Length -> M.Length
   end-spec by {M._ +-> Measure._}
   

results in this :token:`spec`:

.. code-block:: specware

   spec
     type Measure.Length
     op Measure.+ infixl 25 :
               Measure.Length * Measure.Length -> Measure.Length
   end-spec
   

A :token:`spec_qualification` *Q* ``qualifying`` *S* is
convenient shorthand for the :token:`spec_translation` ``translate``
*S* ``by {_ +->`` *Q*\ ``._}``.

.. COMMENT:  ***************************************************************** 

.. _Substitutions:

Substitutions
-------------

.. productionlist::
  spec_substitution: `spec_term` "[" `morphism_term` "]"

Sample :token:`spec_substitution`:

.. code-block:: specware

   Routing#Basis[morphism /Coll/Lattice ->
                          /Coll/LatticeWithTop {} ]
   

The elaboration of :token:`spec_substitution` *S*\ ``[``\ *M*\ \ ]
yields the :token:`spec` *T* obtained as follows. Let :token:`spec`
*R* be the result of elaborating *S*, and morphism *N* that of *M*.
Let :token:`specs` *D* and *C* be the domain and codomain of *N*.
First, remove from *R* all :token:`declarations` of *D*, and subject
the result to the effect of *N*, meaning that all :token:`name`
translations of *N* and all extensions with :token:`declarations` are
performed. Then add the :token:`declarations` of *C*, but without
duplications, i.e., as if *C* is imported. The result obtained is *T*.

Restriction. :token:`Spec` *D* must be a "sub-:token:`spec`" of
:token:`spec` *R*, meaning that each :token:`declaration` of *D* is
also a :token:`declaration` of *R*.

Informally, *T* is to *R* as *C* is to *D*.

Except when *R* introduces, next to the :token:`type_names` and
:token:`op_names` it has in common with *D*, new :token:`type_names`
or :token:`op_names` that also occur in *C*, the result :token:`spec`
*T* is a categorical colimit of this pushout diagram:

.. code-block:: specware

   *D* ---------> *R*
   |            |
   |            |
   |            |
   v            v
   *C* ---------> *T*
   

Although isomorphic to the result that would be obtained by using a
:token:`diagram_colimit`, *T* is more "user-oriented" in two ways: the
:token:`names` in *T* are :token:`names` from *C*, and :token:`claims`
of *D* not repeated in *C* are not repeated here either.

For example, assume we have:

.. code-block:: specware

   A = spec
     type Counter
     op reset : Counter
     op tally : Counter -> Counter
     axiom Effect is
       fa (c : Counter) ~(tally c = c)
   end-spec
   
   B = spec
     type Register = Nat
     def reset = 0
     def incr c = c+1
   end-spec
   
   M = morphism A -> B {Counter +-> Register, tally +-> incr}
   
   AA = spec
     import A
     type Interval = {start: Counter, stop: Counter}
     op isEmptyInterval? : Interval -> Bool
     def isEmptyInterval? {start = x, stop = y} = (x = y)
   end-spec
   

Then the result of ``AA[M``\ ] is the same as that of this
:token:`spec`:

.. code-block:: specware

   spec
     import B
     type Interval = {start: Register, stop: Register}
     op isEmptyInterval? : Interval -> Bool
     def isEmptyInterval? {start = x, stop = y} = (x = y)
   end-spec
   

.. COMMENT:  ***************************************************************** 

Diagram Colimits
----------------

.. productionlist::
  diagram_colimit: colimit `diagram_term`

The result of elaborating a :token:`diagram_colimit` is the
:token:`spec` which is the apex of the cocone forming the colimit in
the category of :token:`specs` and :token:`spec_morphisms`. As always,
the result is required to be well formed. See further the |Specware|
Tutorial.

.. COMMENT:  TODO: weird :token:`names` 

.. COMMENT:  ***************************************************************** 

Obligators
----------

.. productionlist::
  obligator: obligations `unit_term`

Restriction. The :token:`unit_term` of an :token:`obligator` must
either be a :token:`spec_term` or a :token:`morphism_term`.

The result of elaborating an :token:`obligator` is a :token:`spec`
containing the proof obligations engendered by the :token:`spec` or
morphism resulting from elaborating its :token:`unit_term`. These
proof obligations are expressed as conjectures; they can be discharged
by proving them, using :token:`proof_terms`. See further the
|Specware| User Manual.

.. COMMENT:  ***************************************************************** 

Morphisms
=========

.. productionlist::
  morphism_term: `unit_identifier` | 
               : `spec_morphism`
  spec_morphism: morphism `spec_term` -> `spec_term` `name_map`

A morphism is a formal mapping between two expanded
:token:`spec_forms` that describes exactly how one is translated or
extended into the other. It consists of the two :token:`specs`,
referred to as "domain" and "codomain", and a mapping of all
:token:`type_names` and :token:`op_names` introduced in the domain
:token:`spec` to :token:`type_names` and :token:`op_names` of the
codomain :token:`spec`. To be well-formed, a morphism must obey
conditions that express that it is a proper refinement of the domain
:token:`spec` into the codomain :token:`spec`.

Restriction. When used as a :token:`morphism_term`, the elaboration of
a :token:`unit_identifier` must yield a morphism.

Restriction ("proof obligations"). Given :token:`spec_morphism`
``morphism`` *S* ``->`` *T* ``{`` *M*\ :sub:`1` ``+->`` *N*\ :sub:`1`,
``...`` *M*\ :sub:`n` ``+->`` *N*\ :sub:`n` ``}`` let *R* be the result
of elaborating *S*, and let *S'* be *R* with each occurrence of a
:token:`name` *M*\ :sub:`i` replaced by *N*\ :sub:`i`.  The same rules
apply as for :token:`spec_translation` ``translate`` *S* ``by
{``... ``}``, and the result *S'* must be well formed, with the
exception that the restriction on :token:`spec_translations` requiring
different :token:`type_names` or :token:`op_names` to be mapped to
different :token:`simple_names` does not apply here.  Let *T'* be the
result of elaborating *T*.  Then, first, each :token:`type_name` or
:token:`op_name` introduced in *S'* must also be introduced in *T'*.
Further, no :token:`type_name` or :token:`op_name` originating from a
library :token:`spec` (or built in to Specware) may have been subject to translation.  Finally,
each :token:`claim` in *S'* must be a theorem that follows from the
:token:`claims` of *T'*.  Collectively, the :token:`claims` in *S'*
are known as the *proof obligations* engendered by the morphism.  They
are the formal expression of the requirement that the step from *S'*
to *T'* is a proper refinement.

For example, in

.. code-block:: specware

   S = spec end-spec
   T = spec type Bullion = (Char | isAlpha) end-spec
   M = morphism S -> T {Bool +-> Bullion}
   

the type-name ``Bool``, which is built in to Specware, is subject to translation. Therefore, ``M`` is not a
proper morphism. Further, in

.. code-block:: specware

   S = spec
         op f : Nat -> Nat
         axiom ff is fa(n:Nat) f(n) ~= f(n+1)
       end-spec
   
   T = spec
         def f(n:Nat) = n*n rem 5
       end-spec
   
   M = morphism S -> T {}
   

axiom ``ff`` does not follow from (the axiom implied by) the
:token:`op_definition` for ``f`` in :token:`spec` ``T``, since
``f(2)`` = ``f(3)`` = 4. Therefore, ``M`` is not a proper morphism
here either.

Sample :token:`spec_morphism`:

.. code-block:: specware

   morphism A -> B {Counter +-> Register, tally +-> incr}
   

The elaboration of :token:`spec_morphism`\ ``morphism``\ *S*\ ``->``\
*T*\ ``{``\ *M*\ ``}`` results in the morphism whose domain and
codomain are the result of elaborating *S* and *T*, respectively, and
whose mapping is given by the list of :token:`name_map_items` in *M*,
using :token:`type_annotations` and indicators ``type`` and ``op`` as
described for :token:`spec_translations`, and extended to all domain
:token:`type_names` and :token:`op_names` not yet covered by having
these map to themselves. (In particular, :token:`simple_names` from
the base-libraries always map to themselves.)

.. COMMENT:  ***************************************************************** 

.. COMMENT: ** <section><title>Spec type and operator visibility</title>
            ** <para>
            ** &lt;&lt;
            ** ||:token:`spec_visibility` ::=
            ** ||     hide :token:`name_list` in :token:`spec_term`
            ** ||   | export :token:`name_list` from :token:`spec_term`
            ** ||
            ** ||:token:`name_list` ::= '{ :token:`name` { , :token:`name` }* "}"
            ** ``
            ** </para>
            ** </section>

.. COMMENT:  ***************************************************************** 

Diagrams
========

.. productionlist::
  diagram_term: `unit_identifier` | 
              : `diagram_form`
  diagram_form: diagram "{" `diagram_element` { , `diagram_element` }* "}"
  diagram_element: `diagram_node` | 
                 : `diagram_edge`
  diagram_node: `simple_name` +-> `spec_term`
  diagram_edge: `simple_name` : `simple_name` -> `simple_name` +-> `morphism_term`

Restriction. When used as a :token:`diagram_term`, the elaboration of
a :token:`unit_identifier` must yield a diagram.

Restriction. In a :token:`diagram_term`, the first
:token:`simple_name` of each :token:`diagram_node` and
:token:`diagram_edge` must be unique (i.e., not be used more than once
in that :token:`diagram_term`). Further, for each
:token:`diagram_edge` \ *E*\ ``:``\ *ND*\ ``->``\ *NC*\ ``+->``\ *M*\
\ , there must be :token:`diagram_nodes` \ *ND*\ ``+->``\ *D* and \
*NC*\ ``+->``\ *C* of the :token:`diagram_term` such that, after
elaboration, *M* is a morphism from *D* to *C*.

Sample :token:`diagram_term`:

.. code-block:: specware

   diagram {
      A          +-> /Coll/Lattice,
      B          +-> /Coll/LatticeWithTop,
      m : A -> B +-> /Coll/AddTop,
      C          +-> Routing#Basis,
      i : A -> C +-> morphism /Coll/Lattice ->
                                  Routing#Basis {}
   }
   

The result of elaborating a :token:`diagram_form` is the categorical
diagram whose nodes are labeled with the :token:`specs` and whose
edges are labeled with the morphisms that result from elaborating the
corresponding :token:`spec_terms` and :token:`morphism_terms`.

.. COMMENT:  ***************************************************************** 

.. COMMENT: ** <section><title>Let and Where Expressions</title>
            ** <para>
            ** ``
            ** ||:token:`let_term` ::= let :token:`local_bindings` in :token:`unit_term`
            ** ||
            ** ||:token:`where_term` ::= :token:`unit_term` where :token:`local_bindings` end
            ** ||
            ** ||:token:`local_bindings` ::= :token:`simple_name` = :token:`unit_term` { :token:`simple_name` = :token:`unit_term` }*
            ** ``
            ** </para>
            ** </section>

.. COMMENT:  ***************************************************************** 

Target Code Terms
=================

.. productionlist::
  target_code_term: generate `target_language_name` `spec_term` [ `generate_option` ]
  generate_option: in `string_literal` | 
                 : with `unit_identifier`
  target_language_name: c | 
                      : java | 
                      : lisp

Sample :token:`target_code_term`:

.. code-block:: specware

   generate lisp /Vessel#Contour
                     in "C:/Projects/Vessel/Contour.lisp"
   

The elaboration of a :token:`target_code_term` for a well-formed
:token:`spec_term` generates code in the language suggested by the
:token:`target_language_name` (currently only C, Java, and Common
Lisp); see further the
|Specware| User Manual.

.. COMMENT:  ***************************************************************** 

Proof Terms
===========

.. productionlist::
  proof_term: prove `claim_name` in `spec_term`
            :  [ with `prover_name` ]
            :  [ using `claim_list` ]
            :  [ options `prover_options` ]
  prover_name: snark
  claim_list: `claim_name` { , `claim_name` }*
  prover_options: `string_literal`

Restriction. The :token:`claim_names` must occur as
:token:`claim_names` in the :token:`spec` that results from
elaborating the :token:`spec_term`.

Sample :token:`proof_term`:

.. code-block:: specware

   prove Effect in obligations M
                        options "(use-paramodulation t)"
   

The elaboration of a :token:`proof_term` invokes the prover suggested
by the :token:`prover_name` (currently only SNARK). The property to be
proved is the :token:`claim` of the first :token:`claim_name`; the
:token:`claim_list` lists the hypotheses (assumptions) that may be
used in the proof. The :token:`prover_options` are prover-specific and
are not further described here. For details, see the
|Specware| User Manual.

.. COMMENT:  ***************************************************************** 

Declarations
############

.. productionlist::
  declaration: `import_declaration` | 
             : `type_declaration` | 
             : `op_declaration` | 
             : `claim_declaration` | 
             : `definition`
  definition: `type_definition` | 
            : `op_definition`
  equals: is | 
        : =

Sample :token:`declarations`:

.. code-block:: specware

   import Lookup
   type Key
   type Key = String
   op present : Database * Key -> Bool
   def present(db, k) = embed? Some (lookup (db, k))
   axiom norm_idempotent is fa(x) norm (norm x) = norm x
   

.. COMMENT:  ***************************************************************** 

Import-declarations
===================

.. COMMENT: ====================================================================

A :token:`spec` may contain one or more :token:`import_declarations`.
On elaboration, these are "expanded". The effect is as if the bodies
of these imported :token:`specs` (themselves in elaborated form, which
means that all :token:`import_declarations` have been expanded, all
translations performed and all shorthand employs of :token:`names`
have been resolved to full :token:`names`, after which only
declarations or definitions of types, :token:`ops` and :token:`claims`
are left) is inserted in place in the receiving :token:`spec`.

For example, the result of

.. code-block:: specware

   spec
     import spec
              type A.Z
              op b : Nat -> Z
            end
     def A.Z = String
     def b = toString
   end-spec
   

is this "expanded" :token:`spec`:

.. code-block:: specware

   spec
     type A.Z
     op b : Nat -> A.Z
     def A.Z = String
     def b = toString
   end-spec
   

For this to be well formed, the imported :token:`specs` must be well
formed by themselves; in addition, the result of expanding them in
place must result in a well-formed :token:`spec`.

There are a few restrictions, which are meant to catch unintentional
naming mistakes. First, if two different imported :token:`specs` each
introduce a type or :token:`op` with the same (full) :token:`name`,
the introductions must be identical declarations or definitions, or
one may be a declaration and the other a "compatible" definition. For
example, given

.. code-block:: specware

   S1 = spec op e : Integer end
   S2 = spec op e : Char end
   S3 = spec def e = 0 end
   

the :token:`specs` ``S1`` and ``S3`` can be imported together, but all
other combinations of two or more co-imported :token:`specs` result in
an ill-formed :token:`spec`. This restriction is in fact a special
case of the general requirement that import expansion must result in a
well-formed :token:`spec`. Secondly, a :token:`type_name` introduced
in any of the imported :token:`specs` cannot be re-introduced in the
receiving :token:`spec` except for the case of an "imported"
declaration together with a definition in the receiving :token:`spec`.
Similarly for :token:`op_names`, with the addition that an
:token:`op_definition` in the receiving :token:`spec` must be
compatible with an :token:`op_declaration` for the same :token:`name`
in an imported :token:`spec`. The latter is again a special case of
the general requirement that import expansion must result in a well-
formed :token:`spec`.

What is specifically excluded by the above, is giving a definition of
a type or :token:`op` in some :token:`spec`, import it, and then
redefining or declaring that type or :token:`op` with the same full
:token:`name` in the receiving :token:`spec`.

.. COMMENT: ====================================================================

.. productionlist::
  import_declaration: import `spec_term` { , `spec_term` }*

Sample :token:`import_declaration`:

.. code-block:: specware

   import Lookup
   

.. COMMENT:  ================================================================= 

An :token:`import_declaration` of the form ``import`` *S*\ :sub:`1`
``,`` ... ``,`` *S*\ :sub:`n`, where *n* ``> 1``, is equivalent to
the sequence of :token:`import_declarations`::

   import S1
   ...
   import S2
   

.. COMMENT:  ================================================================= 

An :token:`import_declaration` is contained in some
:token:`spec_form`, and to elaborate that :token:`spec_form` the
:token:`spec_terms` of its :token:`import_declarations` are elaborated
first, giving a sequence of :token:`specs`. The
:token:`import_declaration` has then the effect as if the
:token:`declarations` of the imported :token:`specs` as elaborated are
expanded in place, replacing the :token:`import_declaration`. This
cascades: if :token:`spec` *A* imports *B*, and :token:`spec` *B*
imports *C*, then effectively :token:`spec` *A* also imports *C*. An
important difference with earlier versions of |Specware| than version
4 is that multiple imports of the same :token:`spec` have the same
effect as a single import.

.. COMMENT:  ================================================================= 

If :token:`spec` *A* is imported by *B*, each model of *B* is
necessarily a model of *A* (after "forgetting" any
:token:`simple_names` newly introduced by *B*). So *A* is then refined
by *B*, and the morphism from *A* to *B* is known as the "import
morphism". As it does not involve translation of :token:`type_names`
or :token:`op_names`, it can be denoted by ``morphism`` *A* ``->`` *B* ``{}``.

.. COMMENT:  ***************************************************************** 

.. _Type-declarations:

Type-declarations
=================

.. productionlist::
  type_declaration: type `type_name` 
                  :      [ `formal_type_parameters` ] 
  formal_type_parameters: `local_type_variable` | 
                        : ( `local_type_variable_list` )
  local_type_variable: `simple_name`
  local_type_variable_list: `local_type_variable` { , `local_type_variable` }*

Restriction. Each :token:`local_type_variable` of the
:token:`formal_type_parameters` must be a different
:token:`simple_name`.

.. COMMENT:  ================================================================= 

Sample :token:`type_declarations`:

.. code-block:: specware

   type Date
   type Array a
   type Map(a, b)
   

.. A :token:`type_declaration` of the form ``type`` *T* ``=`` *D* is
.. equivalent to the :token:`type_declaration` ``type`` *T* followed by
.. the :token:`type_definition` ``def type`` *T* ``=`` *D* .

.. COMMENT:  ================================================================= 

Every :token:`type_name` used in a :token:`spec` must be declared or defined (in
the same :token:`spec` or in an imported :token:`spec`, including the
"base-library" :token:`specs` that are always implicitly imported) in
a :token:`type_declaration` or :token:`type_definition`. A
:token:`type_name` may have
*type parameters*.
Given the example :token:`type_declarations` above, some valid
:token:`type_descriptors` that can be used in this context are ``Array Date``,
``Array (Array Date)`` and ``Map (Nat, Bool)``.

.. COMMENT:  ================================================================= 

Restriction. Except for the exception provided in the next paragraph,
:token:`type_names` may not be redeclared and/or redefined, whether in
the same :token:`spec` or after having been declared/defined in an imported
:token:`spec`, not even when both declarations or definitions are identical.

In |SpecwareV|, a type may be declared in a :token:`type_declaration` and in the same context also be defined in a :token:`type_definition`.

.. COMMENT:  ================================================================= 

In a model of the :token:`spec`, a type is assigned to each
unparameterized :token:`type_name`, while an infinite
*family*  of types is assigned to
parameterized :token:`type_names` "indexed" by tuples
of types, that is, there is one family member, a type,
for each possible assignment
of types to the :token:`local_type_variables`.
So for the above example :token:`type_declaration` of ``Array``
one type must be assigned to ``Array Nat``, one to
``Array Bool``, one to ``Array (Array Date)``, and so on.
These assigned types could all be the same type, or perhaps all
different, as long as the model respects typing.

.. COMMENT:  ***************************************************************** 

.. _Type-definitions:

Type-definitions
================

.. productionlist::
  type_definition: `type_abbreviation` | `new_type_definition`
  type_abbreviation: type `type_name` 
                   :     [ `formal_type_parameters` ] = `type_descriptor`
  new_type_definition: type `type_name` 
                     : [ `formal_type_parameters` ] = `new_type_descriptor`

Restriction. Each :token:`local_type_variable` of the
:token:`formal_type_parameters` must be a different
:token:`simple_name`.

Sample :token:`type_abbreviations`:

.. code-block:: specware

   type MyFun = Nat -> Nat
   type MyProd = Nat * Nat
   type MyProd2 = MyProd
   type Date = {year : Nat, month : Nat, day : Nat}
   type Array a = List a
   type PosNat = (Nat | positive?)
   type PosNat2 = {x:Nat | positive? x}
   type Map(a, b) = (Array (a * b) | key_uniq?)
   

Sample :token:`new_type_definitions`:

.. code-block:: specware

   type Tree         a = | T.Leaf a | T.Fork (Tree a * Tree a)
   type Bush         a = | B.Leaf a | B.Fork (Tree a * Tree a)
   type Z3 =  Nat / (fn (m, n) -> m rem 3 = n rem 3)
   

Restriction. If the :token:`type_name` of a :token:`type_definition` 
was previously declared in a :token:`type_declaration`, 
either the :token:`declaration` and :token:`definition` both must
contain no :token:`formal_type_parameters`, or they must agree in the number of
:token:`local_type_variables` in their
:token:`formal_type_parameters`.

.. COMMENT:  ================================================================= 

In each model, the type assigned to the :token:`type_name` of a
:token:`type_abbreviation` must be the same as the right-hand-side
:token:`type_descriptor`, while that assigned to the
:token:`type_name` of a :token:`new_type_definition` must be
isomorphic to the type of the :token:`new_type_descriptor`. Thus,
while ``Array Nat`` and ``List Nat`` from the examples denote the same
type, the types assigned to ``Tree Nat`` and ``Bush Nat`` are
equivalent but not necessarily equal, and commingling them in a
:token:`spec` results in a type error. 

.. COMMENT:  On the other hand, ``Bush Nat`` and ``Shrub Nat`` are truly synonymous.

For parameterized types, this extends to all possible assignments of
types to the :token:`local_type_variables`, taking the right-hand
:token:`type_descriptors` and :token:`new_type_descriptors` as
interpreted under each of these assignments. So, for the example,
``Map(Nat, Char)`` is the same type as ``(Array (Nat * Char) |
key_uniq?)``, and so on.

.. COMMENT:  ================================================================= 

With
*recursive*  :token:`type_definitions`, there are additional requirements.
Consider

.. code-block:: specware

   type Stack a =
     | Empty
     | Push {top : a, pop : Stack a}
   

This means that for each type ``a`` there is a value
``Empty`` of type ``Stack a``, and further a function
``Push`` that maps values of type ``{top : a, pop : Stack a}`` to ``Stack a``.
Furthermore, the type assigned to ``Stack a`` must be such
that all its inhabitants can be constructed
*exclusively*  and
*uniquely*  in this way:
there is one inhabitant ``Empty``, and all others are the
result of a ``Push``.
Finally -- this is the point -- the type in the model must
be such that its inhabitants can be constructed this way in
*a finite number of steps*.
So there can be no "bottom-less" stacks:
deconstructing a stack using

.. code-block:: specware

   op [a] hasBottom? (s : Stack a) : Bool =
     case s of
        | Empty -> true
        | Push {top, pop = rest} -> hasBottom? rest
   

is a procedure that is guaranteed to terminate, always
resulting in ``true``.

.. COMMENT:  ================================================================= 

In general, :token:`type_definitions` generate implicit axioms, which
for recursive definitions imply that the type is not "larger" than
necessary. In technical terms, in each model, the type is the least
fixpoint of a recursive domain equation.

.. COMMENT:  ================================================================= 

.. COMMENT: ** <para>
            ** Note.  Not all recursive definitions have such least fixpoints,
            ** in which case the :token:`spec` is inconsistent.
            ** The corresponding axioms are higher-order of a nature that
            ** the provers that can currently be coupled to the |Specware|
            ** system can not handle, and are not actually generated.
            ** For normal cases of "algebraic types"
            ** like ``Stack a`` above, there is a first-order
            ** characterization, and the appropriate axioms are generated for
            ** use by provers.
            ** </para>

.. COMMENT:  ***************************************************************** 

.. _Op-declarations:

Op-declarations
===============

.. productionlist::
  op_declaration: op [ `type_variable_binder` ] `formal_expression` 
                :    [ `fixity` ] `type_annotation` [ = `expression` ] | 
                : op `formal_expression` [ `fixity` ]
                :    `polytype_annotation`  [ = `expression` ]
  polytype_annotation: : `type_variable_binder` `type_descriptor`
  type_variable_binder: "[" `local_type_variable_list` "]"
  formal_expression: `op_name` | `formal_application`
  formal_application: `formal_application_head` `formal_parameter`
  formal_application_head: `op_name` | `formal_application`
  formal_parameter: `closed_pattern` | 
                  : "(" `pattern` "|" `expression` ")"
  fixity: `associativity` `priority`
  associativity: infixl | infixr
  priority: `nat_literal`

Note that the :token:`formal_expression` of an :token:`op_declaration`
always uses prefix notation, even for :token:`infix_operators`.

Sample :token:`op_declarations`:

.. code-block:: specware

   op usage : String
   
   op usage : String = "Usage: Lookup key [database]"
   
   op [a,b,c] o infixl 24 :         (b -> c) * (a -> b) -> a -> c
   op         o infixl 24 : [a,b,c] (b -> c) * (a -> b) -> a -> c
   
   op f (s : String) ((i, j) : Nat * Nat | i < j) (c : Char) : String = 
     substring (s, i, j) ^ toString c
   

The placement of a :token:`type_variable_binder`, if present, is of no
significance; the two :token:`declarations` given above for
:token:`op` ``o`` are completely equivalent. Note that the presence of
a :token:`type_annotation` or :token:`polytype_annotation` is
mandatory even if the type can be determined from a defining
:token:`expression`, as in the second example for :token:`op`
``usage`` above.

The meaning of a :token:`formal_parameter` ``(``\ *P*\ ``|``\ *E*\
``)`` is the same as that of the :token:`formal_parameter` ``((``\
*P*\ ``):{(``\ *P*\ ``):``\ *T*\ ``|``\ *E*\ ``})``, in which *T* is
a :token:`type_descriptor` such that in the context the
:token:`annotated_pattern` ``(``\ *P*\ ``):``\ *T* is type-correct.
If no such :token:`type_descriptor` exists, or its type cannot be
unambiguously be determined, the :token:`formal_parameter` is type-
incorrect. For example, in the :token:`declaration` for ``f`` above,
the :token:`formal_parameter` ``((i, j) : Nat * Nat | i<j)`` is a
shorthand notation for ``(((i, j) : Nat * Nat) : {(((i, j) : Nat *
Nat) : Nat * Nat | i<j)})``, which can be simplified to ``((i, j)
: {((i, j) : Nat * Nat | i<j)})``.

Restriction. The restricting :token:`expression` following a vertical
bar in a formal-parameter must not refer to local variables introduced
by preceding :token:`formal_parameters`. (To do so would effectively
create dependent types, which are currently not supported.)

An :token:`op_declaration` of the form ``op`` *B* *F*  *X* \
*A* ``=`` *E*, in which *B* is an optional
:token:`type_variable_binder`, *F* is a :token:`formal_expression`,
*X* is an optional :token:`fixity`, *A* is a :token:`type_annotation`
and *E* is an :token:`expression`, is equivalent to the
:token:`op_declaration` ``op``\ *B*\ \ *F*\ \ *X*\ \ *A*\ followed by
the :token:`op_definition` ``def op``\ *B*\ \ *F*\ ``=``\ *E*\ \ .

.. COMMENT:  ================================================================= 

In an :token:`op_declaration` of the form ``op`` *N*\ ``:``\ *T*\ \ ,
in which *N* is an :token:`op_name`, *N* is declared to have type *T*.
An :token:`op_declaration` of the form ``op`` *H*\ ``(``\ *P*\ ``:``\
*S*\ ``) :``\ *T*\ \ , in which *P* is a :token:`pattern` whose type
is given by :token:`type_descriptor` *T*, is equivalent to ``op``
*H*\ ``:``\ *S*\ ``->``\ *T*\ \ . So the :token:`simple_names` used as
:token:`local_variables` in each :token:`formal_parameter` are only
bound to that :token:`formal_parameter`, and are further irrelevant
for its type. For example, the :token:`op_declaration` of ``f`` above
is equivalent to the following:

.. code-block:: specware

   op  f : String -> {(i, j) : Nat * Nat | i<j} -> Char -> String 
   def f s (i, j) c = substring (s, i, j) ^ toString c
   

in which the :token:`type_annotations` in the :token:`op_definition`
have been omitted as being redundant.

.. COMMENT:  ====================== NOT YET ==================================
            ** <para>
            ** Restriction.
            ** Although :token:`ops` may be "overloaded",
            ** an :token:`op` can not be redeclared and/or redefined with overlapping
            ** <emphasis>source types</emphasis> (see below), whether in the
            ** same :token:`spec` or after having been defined in an imported :token:`spec`,
            ** not even when the meaning of both :token:`definitions` is the same.
            ** For example, ``op abs : Nat -> Nat`` cannot coexist with
            ** ``op abs : Integer -> Integer``, but either can coexist
            ** with ``op abs : Char -> Nat``.
            ** There may be both an :token:`op_declaration` and an :token:`op_definition`
            ** for the same :token:`op`, provided that the type information supplied
            ** by the :token:`op_declaration` is compatible with the (explicit or
            ** inferred) type of the :token:`op_definition`, and that the
            ** :token:`op_definition` is not given in an imported :token:`spec` (but in the
            ** current :token:`spec`, or in a later :token:`spec` importing the current
            ** :token:`spec`).
            ** </para>
            ** 
            ** <para>
            ** Restriction.
            ** When an :token:`infix_operator` (see below) is overloaded,
            ** all :token:`op_declarations` for the :token:`op` must have the same
            ** :token:`fixity`.
            ** </para>
                 ====================== TEY TON ================================== 

Restriction. User-defined :token:`ops` may not be "overloaded", or
otherwise be redeclared and/or redefined, whether in the same
:token:`spec` or after having been defined in an imported
:token:`spec`, not even when both :token:`declarations` or
:token:`definitions` are identical.

However, one can get the effect of overloading by declaring distinct
:token:`ops` with different qualifiers for the same unqualified name,
e.g.

.. code-block:: specware

   op Table.length  : Table  -> Nat
   op Vector.length : Vector -> Nat
   

Here, subsequent references of the form ``length`` may be resolved to
refer to ``Table.length`` or ``Vector.length`` as appropriate,
provided exactly one is type-consistent in the context of the
reference.

.. COMMENT:  ================================================================= 

An :token:`op_declaration` introduces an :token:`op` with an
associated type. The type can be "monomorphic", like ``String``, or
"polymorphic" (indicated by a :token:`type_variable_binder`). In the
latter case, an indexed family of values is assigned to parameterized
:token:`type_names` "indexed" by tuples of types, that is, there is
one family member, a typed value, for each possible assignment of
types to the :token:`local_type_variables` of the
:token:`type_variable_binder`, and the type of that value is the
result of the corresponding substitution of types for
:token:`local_type_variables` on the polymorphic type of the
:token:`op`. In the examples above, the two forms given for the
declaration of polymorphic ``o`` are entirely equivalent; they can be
thought of as introducing a family of (fictitious) :token:`ops`, one
for each possible assignment to the :token:`local_type_variables`
``a``, ``b`` and ``c``\.

``o``\ :sub:`Nat,String,Char`  ``: (String -> Char) * (Nat -> String) -> Nat -> Char``
   
``o``\ :sub:`Nat,Nat,Bool`  ``: (Nat -> Bool) * (Nat -> Nat) -> Nat -> Bool``
   
``o``\ :sub:`Char,Bool,Nat` ``: (Bool -> Nat) * (Char -> Bool) -> Char -> Nat``
   
and so on.  Any :token:`op_definition` for ``o`` must be likewise
accommodating.

.. COMMENT:  ================================================================= 

.. COMMENT:  ====================== NOT YET ==================================
            ** <para>
            ** Given a type *T*, the type
            ** super(*T*) is defined to be
            ** *T* if *T*
            ** is not a subtype.
            ** For a subtype ``(``\ *T*\  ``|``\ *P*\ ``)``,
            ** super(\ ``(``\ *T*\  ``|``\ *P*\ ``)``\ ) is the type
            ** super(*T*).
            ** For example, super(\ ``(Nat | even)``\ ) is ``Integer``.
            ** </para>
            ** 
            ** <para>
            ** The source types of an :token:`op` are the set of types determined
            ** as follows.
            ** If the type of the :token:`op` is some monomorphic function type
            ** \ *S*\  ``->``\ *T*\ \ , the source types are the
            ** singleton set {super(*S*)}.
            ** If the type of the :token:`op` is a polymorphic function type
            ** corresponding to some :token:`type_scheme`
            ** ``[``\ *V*\ ``]``\ *S*\  ``->``\ *T*\ \ , the source types are the
            ** set of all types super(*S'*)
            ** for the types
            ** ``*S'* ->`` \ *T'* of the indexed family of
            ** values,
            ** obtainable by the substitution of types for
            ** the :token:`local_type_variables` in
            ** *V*.
            ** For example, for
            ** [[
            ** ||   op f : [a] a * a -> a
            ** ]]
            ** the source types are the set
            ** {\ ``Integer * Integer``, ``Bool * Bool``, [[Char *
            ** Char]], ...}.
            ** </para>
            ** 
            ** <para>
            ** Finally, if the type of the :token:`op` is not a (monomorphic or
            ** polymorphic) function type, the source types of the :token:`op` are
            ** the singleton set {\ ``()``\ }, containing just the unit type.
            ** </para>
                 ====================== TEY TON ================================== 

.. COMMENT:  ================================================================= 

Only binary :token:`ops` (those having some type \ *S*\ ``*``\ *T*\
``->``\ *U*\ \ ) may be declared with a :token:`fixity`. When declared
with a :token:`fixity`, the :token:`op` may be used in infix notation,
and then it is called an :token:`infix_operator`. For ``o`` above,
this means that ``o(f, g)`` and ``f o g`` may be used,
interchangeably, with no difference in meaning. If the
:token:`associativity` is ``infixl``, the :token:`infix_operator` is
called
*left-associative*; otherwise,
if the :token:`associativity` is ``infixr``, it is
called *right-associative*.
If the :token:`priority` is ``priority``\ *N*\ \ ,
the operator is said to have
*priority*  *N*.
The :token:`nat_literal` *N* stands for a
natural number; if :token:`infix_operator` 
*O1* has priority
*N1*,
and *O2* has priority
*N2*, with
*N1* < *N2*,
we say that *O1* has
*lower priority*  than
*O2*,
and that *O2* has
*higher priority*  than
(or *takes priority over*)
*O1*.
For the role of the :token:`associativity` and :token:`priority`, see further at
`Applications`_.

.. COMMENT:  ***************************************************************** 

.. _Op-definitions:

Op-definitions
==============

.. productionlist::
  op_definition: def [ op ] [ `type_variable_binder` ] `formal_expression` [ `type_annotation` ]      = `expression` | 
               : def [ op ] `formal_expression` `polytype_annotation`      = `expression`

.. COMMENT:  ====================== NOT YET ==================================
            ** ||:token:`formal_application` ::= :token:`formal_prefix_application` | :token:`formal_infix_application`
            ** ||
            ** ||:token:`formal_prefix_application` ::= :token:`formal_application_head` `formal-parameter
            ** ||
            ** ||:token:`formal_application_head` ::= :token:`op_name` | :token:`formal_prefix_application`
            ** ||
            ** ||:token:`formal_parameter` ::= :token:`closed_pattern`
            ** ||
            ** ||:token:`formal_infix_application` ::= :token:`formal_parameter` `op-name :token:`formal_parameter`
            ** >>
            ** </para>
            ** <para>
            ** Restriction.
            ** The :token:`op_name` of a :token:`formal_infix_application` must be an infix
            ** operator.
            ** </para>
            ** <para>
                 ====================== TEY TON ================================== 

Sample :token:`op_definitions`:

.. code-block:: specware

   def op usage = "Usage: Lookup key [database]"
   
   def [a,b,c] o(f : b -> c, g: a -> b) : a -> c =
     fn (x : a) -> f(g x)
   
   def o : [a,b,c] (b -> c) * (a -> b) -> a -> c =
     fn (f, g) -> fn (x) -> f(g x)
   
   def o (f, g) x = f(g x)
   

The keyword ``op`` may be omitted after ``def`` unless the part between the
keyword ``def`` and the :token:`=` has the syntactic form of a :token:`name`
*N* followed by an optional :token:`formal_type_parameters`, where the :token:`name` *N*
is declared or defined in the context as a :token:`type_name`.
As for :token:`op_declarations`, the placement of any
:token:`type_variable_binder` is of no significance.

Restriction. See the restriction under
:ref:`Op-declarations <Op-declarations>`
on redeclaring/redefining :token:`ops`.

.. COMMENT:  ================================================================= 

.. COMMENT:  ====================== NOT YET ==================================
            ** <para>
            ** Disambiguation.
            ** The grammar for :token:`formal_application` is ambiguous for cases
            ** like
            ** *M N P*, in which
            ** *M* is any :token:`simple_name`, and
            ** *N* is an :token:`infix_operator`.
            ** The ambiguity is resolved in favor of the reading
            ** as a :token:`formal_infix_application`, and then the
            ** :token:`formal_infix_application` *M N P*
            ** is equivalent to the :token:`formal_prefix_application`
            ** \ *N*\  ``(``\ *M*\ ``,``\ *P*\ ``)``.
            ** For example, for :token:`infix_operator` ``o``,
            ** [[
            ** ||    def f o g = fn x -> f(g x)
            ** ]]
            ** is equivalent to
            ** [[
            ** ||    def o (f, g) = fn x -> f(g x)
            ** ]]
            ** </para>
            **      ====================== TEY TON ================================== 

Note that a :token:`formal_expression` always contains precisely one
:token:`op_name`, which is the :token:`op`
*being defined*  by
the :token:`op_definition`.
Note further that the :token:`formal_expression` of an :token:`op_definition`
always uses prefix notation, even for :token:`infix_operators`.

.. COMMENT:  ================================================================= 

Restriction. The type information, if any, presented in an
:token:`op_definition` must be consistent with the type specified by
the preceding :token:`op_declaration`. For example, the presence of a
:token:`type_variable_binder` signals that the :token:`op` being
defined is polymorphic, but then the :token:`op_declaration` must
contain an identical :token:`type_variable_binder`. (A
:token:`type_variable_binder` may be needed to introduce
:token:`local_type_variables` for employ in :token:`type_annotations`
within the defining :token:`expression`, as exemplified in the first
definition for ``o``.)

.. COMMENT:  ================================================================= 

In |SpecwareV|, an :token:`op` still may be defined without having
been previously declared, but
*this is now a deprecated feature*.
When an :token:`op` is defined without having been declared, the :token:`op_definition`
generates an implicit :token:`op_declaration` for the :token:`op`, provided a
monomorphic type for the :token:`op` can be unambiguously determined
from the :token:`op_definition` together with the uses of the
:token:`op` in :token:`applications` and other contexts, so that all
:token:`expressions` can be assigned a type in the context in which
they occur.
This feature may not persist in future releases, so users are advised 
to provide an :token:`op_declaration` somewhere before each :token:`op_definition`, either in 
the same :token:`spec` or (more typically) in an imported :token:`spec`.
Alternatively, the newly expanded syntax for :token:`op_definitions`
makes it simple to both give a unique type to and define an :token:`op`
within one :token:`declaration`.

.. COMMENT:  ================================================================= 

In a model of the :token:`spec`, an indexed family of typed values is
assigned to a polymorphic :token:`op`, with one family member for each
possible assignment of types to the :token:`local_type_variables` of
the :token:`type_variable_binder`, and the type of that value is the
result of the corresponding :token:`type_instantiation` for the
polymorphic type of the :token:`op`. Thus, we can reduce the meaning
of a polymorphic :token:`op_definition` to a family of (fictitious)
monomorphic :token:`op_definitions`.

An :token:`op_definition` with :token:`formal_application`

.. code-block:: specware

   def op *H* *P* = *E*
   

in which *H* is a :token:`formal_application_head`, *P* is a
:token:`formal_parameter` and *E* an :token:`expression`, is
equivalent to the :token:`op_definition`

.. code-block:: specware

   def op *H* = fn *P* -> *E*
   

For example,

.. code-block:: specware

   def o (f, g) x = f(g x)
   

is equivalent to

.. code-block:: specware

   def o (f, g) = fn x -> f(g x)
   

which in turn is equivalent to

.. code-block:: specware

   def o = fn (f, g) -> fn x -> f(g x)
   

.. COMMENT:  ====================== NOT YET ==================================
            ** using the transformation from infix to prefix if
            ** applicable, and
            ** repeating
                 ====================== TEY TON ================================== 

By this deparameterizing transformation for each
:token:`formal_parameter`, an equivalent unparameterized :token:`op_definition`
is reached.
The semantics is described in terms of such :token:`op_definitions`.

.. COMMENT:  ================================================================= 

In each model, the typed value assigned to the :token:`op` being
defined must be the same as the value of the right-hand-side
:token:`expression`. For polymorphic :token:`op_definitions`, this
extends to all possible assignments of types to the
:token:`local_type_variables`.

.. COMMENT:  ================================================================= 

An :token:`op_definition` can be thought of as a special notation for
an axiom. For example,

.. code-block:: specware

   op double : [a] a -> a * a
   def double x = (x, x)
   

can be thought of as standing for:

.. code-block:: specware

   op double : [a] a -> a * a
   
   axiom double_def is
     [a] fa(x : a) double x = (x, x)
   

In fact, |Specware| generates such axioms for use by provers. But in
the case of recursive definitions, this form of axiomatization does
not adequately capture the meaning. For example,

.. code-block:: specware

   def f (n : Nat) : Nat = 0 * f n
   

is an improper :token:`definition`, while

.. code-block:: specware

   axiom f_def is
       fa(n : Nat) f n = 0 * f n
   

characterizes the function that maps every natural number to 0. The
issue is the following. Values in models can not be |undefined| and
functions assigned to :token:`ops` must be
*total*.
But in assigning a meaning to a recursive :token:`op_definition`, we
-- temporarily -- allow |undefined| and partial functions
(functions that are not everywhere defined on their domain
type) to be assigned to recursively defined :token:`ops`.
In the thus extended class of models, the recursive :token:`ops` must be
the least-defined solution to the "axiomatic"
equation (the least fixpoint as in domain theory), given the
assignment to the other :token:`ops`.
For the example of ``f`` above this results in the
everywhere undefined function, since
0 times |undefined| is |undefined|.
If the solution results in an undefined value or a function
that is not total (or for higher-order functions, functions
that may return non-total functions, and so on), the
:token:`op_definition` is improper.
Although |SpecwareV| does attempt to generate proof obligations
for this condition, it currently covers only "simple"
recursion, and not mutual recursion or recursion introduced by
means of higher-order functions.

.. COMMENT:  ================================================================= 

Functions that are determined to be the value of an
:token:`expression`, but that are not assigned to :token:`ops`, need
not be total, but the context must enforce that the function can not
be applied to values for which it is undefined. Otherwise, the
:token:`spec` is ill formed.

.. COMMENT:  ***************************************************************** 

Claim-declarations
==================

.. productionlist::
  claim_declaration: `claim_kind` `claim_name` is `claim` [ `proof_script` ]
  claim_kind: axiom | theorem | conjecture
  claim_name: `name`
  claim: [ `type_variable_binder` ] `expression`

Sample :token:`claim_declarations`:

.. code-block:: specware

   axiom norm_idempotent is
     norm o norm = norm
   
   theorem o_assoc is
     [a,b,c,d] fa(f : c -> d, g : b -> c, h : a -> b)
       f o (g o h) = (f o g) o h
   
   conjecture pivot_hold is
     let p = pivot hold in
       fa (n : {n : Nat | n < p}) ~(hold n = hold p)
   

:token:`Proof_scripts` are currently only available for use with
Isabelle, and are not described here. For further details, see the
|Specware| to Isabelle Translator Manual.

.. COMMENT:  ================================================================= 

Restriction. The type of the :token:`claim` must be ``Bool``.

.. COMMENT:  ================================================================= 

Restriction. A :token:`claim` must not be an :token:`expression` whose
first symbol is ``[``. In order to use such an :token:`expression`
as a :token:`claim`, it can be parenthesized, as in

.. code-block:: specware

   axiom nil_fits_nil is ([] fits [])
   

This restriction prevents ambiguities between :token:`claims` with and
without :token:`type_variable_binders`.

.. COMMENT:  ================================================================= 

When a :token:`type_variable_binder` is present, the :token:`claim` is
polymorphic. A polymorphic :token:`claim` may be thought of as
standing for an infinite family of monomorphic :token:`claims`, one
for each possible assignment of types to the
:token:`local_type_variables`.

.. COMMENT:  ================================================================= 

The :token:`claim_kind` ``theorem`` should only be used for
:token:`claims` that have actually been proved to follow from the
(explicit or implicit) axioms. In other words, giving them axiom
status should not change the class of models. Theorems can be used by
provers.

.. COMMENT:  ================================================================= 

Conjectures are meant to represent proof obligations that should
eventually attain theoremhood. Like theorems, they can be used by
provers. This is only sound if circularities (vicious circles) are
avoided. This kind of :token:`claim` is usually created automatically
by the elaboration of an :token:`obligator`, but can also be created
manually.

.. COMMENT:  ================================================================= 

The |Specware| system passes on the :token:`claim_name` of the
:token:`claim_declaration` with the :token:`claim` for purposes of
identification. Both may be transformed to fit the requirements of the
prover, and appear differently there. Not all :token:`claims` can be
faithfully represented in all provers, and even when they can, the
logic of the prover may not be up to dealing with them.

.. COMMENT:  ================================================================= 

Remark. It is a common mistake to omit the part ":token:`claim_name`
is" from a :token:`claim_declaration`. A defensive style against this
mistake is to have the :token:`claim` always start on a new text line.
This is additionally recommended because it may become required in
future revisions of |Metaslang|.

.. COMMENT:  ***************************************************************** 

Type-descriptors
################

.. productionlist::
  type_descriptor: `type_arrow` | `slack_type_descriptor`
  new_type_descriptor: `type_sum` | `type_quotient`
  slack_type_descriptor: `type_product` | `tight_type_descriptor`
  tight_type_descriptor: `type_instantiation` | `closed_type_descriptor`
  closed_type_descriptor: `type_name` | Bool |  `local_type_variable` |
                        : `type_record` | `type_restriction` | 
                        : `type_comprehension` | ( `type_descriptor` )

Note that in |SpecwareV|, :token:`new_type_descriptors` now may appear
only as the right-hand-side of a :token:`type_definition`. In other
words, sum and quotient types no longer may appear anonymously. For
example, they may not be used in an :token:`annotated_pattern` or an
:token:`annotated_expression`. Thus the following :token:`spec` is no
longer legal:

.. code-block:: specware

   spec
     type T
     op f : T -> Nat
     op q : T * T -> Bool
     op q_f (x : T / q) : Nat = let quotient[T / q] y = x in f y
   end-spec
   

but can be expressed legally as follows:

.. code-block:: specware

   spec
     type T
     op f : T -> Nat
     op q : T * T -> Bool
     type Q = T / q
     op q_f (x : Q) : Nat = let quotient[Q] y = x in f y
   end-spec
   

(The distinctions ":token:`slack_`", ":token:`tight_`" and
":token:`closed_`" before ":token:`type_descriptor`" have no semantic
significance. The distinction merely serves the purpose of diminishing
the need for parenthesizing in order to avoid grammatical
ambiguities.)

.. COMMENT:  ================================================================= 

Sample :token:`type_descriptors`:

.. code-block:: specware

   List String * Nat -> Option String
   a * Order a * a
   PartialFunction (Key, Value)
   Key
   Bool
   a
   {center : XYpos, radius : Length}
   (Nat | even)
   {k : Key | present (db, k)}
   (Nat * Nat)
   

Sample :token:`new_type_descriptors`:

.. code-block:: specware

   | Point XYpos | Line XYpos * XYpos
   Nat / (fn (m, n) -> m rem 3 = n rem 3)
   

The meaning of the :token:`type_descriptor` ``Bool`` is the
"inbuilt" type inhabited by the two logical (truth) values ``true``
and ``false``. The meaning of a parenthesized
:token:`type_descriptor` ``(`` *T* ``)`` is the same as that of the
enclosed :token:`type_descriptor` *T*.

.. COMMENT:  ================================================================= 

The various other kinds of :token:`type_descriptors` and
:token:`new_type_descriptors` not defined here are described each in
their following respective sections, with the exception of
:token:`local_type_variable`, whose (lack of) meaning as a
:token:`type_descriptor` is described below.

.. COMMENT:  ================================================================= 

Restriction. A :token:`local_type_variable` may only be used as a
:token:`type_descriptor` if it occurs in the scope of a
:token:`formal_type_parameters` or :token:`type_variable_binder` in
which it is introduced.

.. COMMENT:  ================================================================= 

Disambiguation. A single :token:`simple_name` used as a
:token:`type_descriptor` is a :token:`local_type_variable` when it
occurs in the scope of a :token:`formal_type_parameters` or
:token:`type_variable_binder` in which it is introduced, and then it
identifies the textually most recent introduction. Otherwise, the
:token:`simple_name` is a :token:`type_name`.

.. COMMENT:  ================================================================= 

A :token:`local_type_variable` used as a :token:`type_descriptor` has
no meaning by itself, and where relevant to the semantics is either
"indexed away" (for parameterized types) or "instantiated away" (when
introduced in a :token:`formal_type_parameters` or
:token:`type_variable_binder`) before a meaning is ascribed to the
construct in which it occurs. Textually, it has a scope just like a
plain :token:`local_variable`.

.. COMMENT:  ***************************************************************** 

.. _Type-sums:

Type-sums
=========

.. productionlist::
  type_sum: `type_summand` { `type_summand` }*
  type_summand: "|" `constructor` [ `slack_type_descriptor` ]
  constructor: `name`

Sample :token:`type_sum`:

.. code-block:: specware

   | Point XYpos | Line XYpos * XYpos
   

Restriction. The :token:`constructors` of a :token:`type_sum` must all
have different :token:`simple_names` even if they have different :token:`qualifiers`, 
so the following is illegal:

.. code-block:: specware

   | Start.Point XYpos | End.Point XYpos * XYpos
 

Also, note that since a :token:`type_sum` is a
:token:`new_type_descriptor`, it may appear only on the right hand
side of a :token:`new_type_definition`.

.. COMMENT:  ================================================================= 

The ordering of the :token:`type_summands` has no significance: ``|
Zero | Succ Peano`` denotes the same "sum type" as ``| Succ Peano |
Zero``.

.. COMMENT:  ================================================================= 

A :token:`type_sum` denotes a
*sum type*, which
is a type that is inhabited by "tagged values".
A tagged value is a pair
(*C*, *v*),
in which 
*C* is a :token:`constructor` and
*v* is a typed value.

.. COMMENT:  ================================================================= 

A :token:`type_sum` introduces a number of :token:`constructor ops`, one for
each :token:`type_summand`, along with implicit axioms described below.

.. COMMENT:  ================================================================= 

For a :token:`type_sum` *T* with :token:`type_summand` *C* *S*, in
which *C* is a :token:`constructor` and *S* a
:token:`type_descriptor`, the corresponding :token:`op`
introduced is typed as follows:

.. code-block:: specware

   op C : S -> T
   

It maps a value *v* of type *S* to the tagged value (*C*, *v*). If the
:token:`type_summand` is a single
*parameter-less*  :token:`constructor` (the
:token:`slack_type_descriptor` is missing),
the :token:`op` introduced is typed as follows:

.. code-block:: specware

   op C : T
   

It denotes the tagged value
(*C*, ()), in which () is the
inhabitant of the unit type (see under :ref:`Type-records <Type-records>`).

.. COMMENT:  ================================================================= 

The sum type denoted by the :token:`type_sum` then consists of the
union of the ranges (for parameter-less constructors the values) of
the :token:`ops` for all constructors.

.. COMMENT:  ================================================================= 

The :token:`constructor ops` are individually, jointly and severally
*injective*,
and jointly *surjective*.

.. COMMENT:  ================================================================= 

This means, first, that for any pair of :token:`constructors` *C1* and
*C2* of
*any*  :token:`type_sum`, and for any pair
of values *v1* and *v2*
of the appropriate type
(to be omitted for parameter-less :token:`constructors`),
the value of *C1* *v1* is only equal to
*C2* *v2* when *C1* and *C2*
are the same :token:`constructor`, and *v1* and *v2* are both absent or are the same value.
In other words, whenever the :token:`constructors` are different or the values are different, the
results are different.

.. COMMENT:  ================================================================= 

Secondly, for any value *u* of any sum type, there is a
:token:`constructor` *C* of that sum type and a value *v* of the
appropriate type (to be omitted for parameter-less
:token:`constructors`), such that the value of *C* *v* is *u*. In
other words, all values of a sum type can be constructed with an
:token:`constructor op`.

.. COMMENT:  ================================================================= 

For example, consider

.. code-block:: specware

   type Peano =
     | Zero
     | Succ Peano
   

This means that there is a value ``Zero`` of type ``Peano``, and
further a function ``Succ`` that maps values of type ``Peano`` to type
``Peano``. Then ``Zero`` and ``Succ n`` are guaranteed to be
different, and each value of type ``Peano`` is either ``Zero :
Peano``, or expressible in the form ``Succ (n : Peano)`` for a
suitable :token:`expression` ``n`` of type ``Peano``. Subtypes of a type 
can only be made with a :token:`type_restriction`, for instance as in
``(Peano | embed? Zero)``.)
For recursively defined :token:`type_sums`, see also the discussion
under :ref:`Type-definitions <Type-definitions>`.

.. COMMENT:  ***************************************************************** 

Type-arrows
===========

.. productionlist::
  type_arrow: `arrow_source` -> `type_descriptor`
  arrow_source: `type_sum` | 
              : `slack_type_descriptor`

Sample :token:`type_arrow`:

.. code-block:: specware

   (a -> b) * b -> List a -> List b
   

In this example, the :token:`arrow_source` is ``(a -> b) * b``, and
the (target) :token:`type_descriptor` ``List a -> List b``.

.. COMMENT:  ================================================================= 

The
*function type*  \ *S*\  ``->``\ *T*\  is inhabited by
precisely all *partial or total*  functions from
*S*
to *T*.
That is, function *f* has type
\ *S*\  ``->``\ *T*\  if, and only if,
for each value *x* of type
*S* such that the value of
*f* *x* is
defined, that value has type *T*.
Functions can be constructed with :token:`lambda_forms`, and be used
in :token:`applications`.

.. COMMENT:  ================================================================= 

In considering whether two functions (of the same type) are equal,
only the meaning on the domain type is relevant. Whether a function is
undefined outside its domain type, or might return some value of some
type, is immaterial to the semantics of |Metaslang|. (For a type-
correct :token:`spec`, the difference is unobservable.)

.. COMMENT:  ***************************************************************** 

Type-products
=============

.. productionlist::
  type_product: `tight_type_descriptor` * `tight_type_descriptor` { * `tight_type_descriptor` }*

Sample :token:`type_product`:

.. code-block:: specware

   (a -> b) * b * List a
   

Note that a :token:`type_product` contains at least two constituent
:token:`tight_type_descriptors`.

.. COMMENT: ====================================================================

A :token:`type_product` denotes a *product type* that has at least two
"component types", represented by its :token:`tight_type_descriptors`.
The ordering of the component types is significant: unless *S* and *T*
are the same type, the product type \ *S*\ ``*``\ *T*\ is different
from the type \ *T*\ ``*``\ *S*\ \ .  Further, the three types ``(``\
*S*\ ``*``\ *T*\ ``) *``\ *U*\ \ , \ *S*\ ``* (``\ *T*\ ``*``\ *U*\
``)`` and \ *S*\ ``*``\ *T*\ ``*``\ *U*\ are all different; the first
two have two component types, while the last one has three.  The
inhabitants of the product type *T*\ :sub:`1` ``*`` *T*\ :sub:`2`
``*`` ...  ``*`` \ *T*\ :sub:`n` are precisely all *n*-tuples (*v*\
:sub:`1`, *v*\ :sub:`2`, ... , *v* :sub:`n`), where each *v*\
:sub:`i` has type *T* :sub:`i`, for *i* = 1, 2, ... , *n*.  Values
of a product type can be constructed with :token:`tuple_displays`, and
component values can be extracted with :token:`tuple_patterns` as well
as with :token:`projectors`.

.. COMMENT:  ***************************************************************** 

Type-instantiations
===================

.. productionlist::
  type_instantiation: `type_name` `actual_type_parameters`
  actual_type_parameters: `closed_type_descriptor` | 
                        : ( `proper_type_list` )
  proper_type_list: `type_descriptor` , `type_descriptor` { , `type_descriptor` }*

Sample :token:`type_instantiation`:

.. code-block:: specware

   Map (Nat, Bool)
   

Restriction. The :token:`type_name` must have been declared or defined
as a parameterized type (see
:ref:`Type-declarations <Type-declarations>`), and
the number of :token:`type_descriptors` in the :token:`actual_type_parameters` must match
the number of :token:`local_type_variables` in the
:token:`formal_type_parameters` of the :token:`type_declaration` and/or :token:`type_definition`.

.. COMMENT:  ================================================================= 

The :token:`type_descriptor` represented by a
:token:`type_instantiation` is the type assigned for the combination
of types of the :token:`actual_type_parameters` in the indexed family
of types for the :token:`type_name` of the
:token:`type_instantiation`.

.. COMMENT:  ***************************************************************** 

Type-names
==========

.. productionlist::
  type_name: `name`

Sample :token:`type_names`:

.. code-block:: specware

   Key
   Calendar.Date
   

Restriction. A :token:`type_name` may only be used if there is a
:token:`type_declaration` and/or :token:`type_definition` for it in
the current :token:`spec` or in some :token:`spec` that is imported
(directly or indirectly) in the current :token:`spec`. If there is a
unique :token:`qualified_name` for a given unqualified ending, the
qualification may be omitted for a :token:`type_name` used as a
:token:`type_descriptor`.

.. COMMENT:  ================================================================= 

The type of a :token:`type_name` is the type assigned to it in the
model. (In this case, the context can not have superseded the original
assignment.)

.. COMMENT:  ***************************************************************** 

.. _Type-records:

Type-records
============

.. productionlist::
  type_record: "{" [ `field_typer_list` ] "}" | 
             : ( )
  field_typer_list: `field_typer` { , `field_typer` }*
  field_typer: `field_name` `type_annotation`
  field_name: `simple_name`

Sample :token:`type_record`:

.. code-block:: specware

   {center : XYpos, radius : Length}
   

Restriction. The :token:`field_names` of a :token:`type_record` must
all be different.

.. COMMENT:  ================================================================= 

Note that a :token:`type_record` contains either no constituent
:token:`field_typers`, or else at least two.

.. COMMENT: ====================================================================

A :token:`type_record` is like a :token:`type_product`, except that
the components, called "fields", are identified by :token:`name`
instead of by position. The ordering of the :token:`field_typers` has
no significance: ``{center : XYpos, radius : Length}`` denotes the
same *record type* as ``{radius : Length, center : XYpos}``.

Therefore we assume in the following, without loss of generality, that
the fields are ordered lexicographically according to their
:token:`field_names` (as in a dictionary: ``a`` comes before ``ab``
comes before ``b``\ ) using some fixed collating order for all marks
that may comprise a :token:`name`.  Then each field of a record type
with *n* fields has a *position* in the range 1 to *n*.  The
inhabitants of the record type ``{`` *F*\ :sub:`1` ``:`` *T*\ :sub:`1`
``,`` *F*\ :sub:`2` ``:`` *T*\ :sub:`2` ``,`` ...  ``,`` *F*\ :sub:`n` : *T*\ :sub:`n` ``}`` are precisely all
*n*-tuples (*v*\ :sub:`1`, *v*\ :sub:`2`, ... , *v*\ :sub:`n`), where
each *v*\ :sub:`i` has type *T*\ :sub:`i`, for *i* = 1, 2, ... , *n*.
The :token:`field_names` of that record type are the
:token:`field_names` *F*\ :sub:`1`, ... , *F*\ :sub:`n`, and, given
the lexicographic ordering, :token:`field_name` *F*\ :sub:`i`
*selects* position *i*, for *i* = 1, 2, ... , *n*.  Values of a record
type can be constructed with :token:`record_displays`, and field
values can be extracted with :token:`record_patterns` and (as for
product types) with :token:`projectors`.

.. COMMENT: ====================================================================

For the :token:`type_record` ``{}``, which may be equivalently
written as ``()``, the record type it denotes has zero components,
and therefore no :token:`field_names`. This zero-component type has
precisely one inhabitant, and is called the
*unit
type*.
The unit type may equally well be
considered a product type, and is the only type that is both
a product and a record type.

.. COMMENT: ====================================================================

.. COMMENT:  ***************************************************************** 

Type-restrictions
=================

.. productionlist::
  type_restriction: ( `slack_type_descriptor` "|" `expression` )

Sample :token:`type_restriction`:

.. code-block:: specware

   (Nat | even)
   

Restriction. In a :token:`type_restriction` ``(``\ *T*\ ``|``\ *P*\
``)``, the :token:`expression` *P* must be a predicate on the type
*T*, that is, *P* must be a function of type \ *T*\ ``-> Bool``.

.. COMMENT:  ================================================================= 

Note that the parentheses in ``(``\ *T*\ ``|``\ *P*\ ``)`` are
mandatory.

.. COMMENT:  ================================================================= 

The inhabitants of type ``(``\ *T*\ ``|``\ *P*\ ``)`` are precisely
the inhabitants of type *T* that satisfy the predicate *P*, that is,
they are those values *v* for which the value of *P* *v* is ``true``\
.

.. COMMENT:  ================================================================= 

If *P1* and *P2* are the same function, then ``(``\ *T*\ ``|``\ *P1*\
``)`` and ``(``\ *T*\ ``|``\ *P2*\ ``)`` are equivalent, that is, they
denote the same type. Furthermore, ``(``\ *T*\ ``| fn _ -> true)`` is
equivalent to *T*.

.. COMMENT:  ================================================================= 

The type ``(``\ *T*\ ``|``\ *P*\ ``)`` is called a
*subtype*  of
*supertype*  *T*.
Values can be shuttled between a subtype and its supertype
and vice versa, in the direction from supertype to subtype only
if the value satisfies predicate *P*.

.. COMMENT:  OLD:
            %%%with
            %%%:token:`relaxators` and :token:`restrict_expressions`; see also
            %%% <link linkend="metaslang-relax-pattern"><emphasis>Relax-patterns</emphasis></link>.
            %%%</para>
            %%%<para>
            %%%|Metaslang| does not require the explicit use of a :token:`relaxator` to relax
            %%%an :token:`expression` from a subtype to its supertype if the
            %%%context requires the latter.
            %%%Implicit relaxation will take place when needed.

For example, in the :token:`expression` ``-1`` the :token:`nat_literal` ``1``
of type ``Nat`` is implicitly "coerced" to type ``Integer`` to
accommodate the unary negation operator ``-``, which has type
``Integer -> Integer``.

.. COMMENT: ====================================================================

Likewise,

.. COMMENT:  OLD:
            %%%|Metaslang| does not require the explicit use of a
            %%%:token:`restrict_expression`
            %%%to restrict
            %%%an :token:`expression` from a type to a subtype if the
            %%%context requires the latter.
            %%%Implicit restriction will take place when needed.
            %%%For example,

in the :token:`expression` ``7 div 2`` the :token:`nat_literal` ``2``
of type ``Nat`` is implicitly "coerced" to type ``PosNat``,
a subtype of ``Nat``, to accommodate the division operator
``div``, whose second argument has type ``PosNat``.
But note that this engenders the proof
obligation that the value satisfies the predicate of the subtype.

.. COMMENT: ====================================================================

These coercions extend to composed types. For example, an
:token:`expression` of type ``List PosNat`` may be used where a value
of type ``List Nat`` is required. Conversely, an :token:`expression`
of type ``List Nat`` may be used in a context requiring ``List
PosNat`` if the corresponding proof obligation can be discharged,
namely that the value of the :token:`expression`, in its context,
satisfies the predicate ``all posNat?`` testing whether all elements
of a list of naturals are positive.

.. COMMENT:  ***************************************************************** 

Type-comprehensions
===================

.. productionlist::
  type_comprehension: "{" `annotated_pattern` "|" `expression` "}"

Sample :token:`type_comprehension`:

.. code-block:: specware

   {n : Nat | even n}
   

Restriction. In a :token:`type_comprehension` ``{``\ *P*\ ``:``\ *T*\
``|``\ *E*\ ``}``, the :token:`expression` *E* must have type
``Bool``.

.. COMMENT:  ================================================================= 

:token:`Type_comprehensions` provide an alternative notation for
:token:`type_restrictions` that is akin to the common mathematical
notation for set comprehensions. The meaning of
:token:`type_comprehension` ``{``\ *P*\ ``:``\ *T*\ ``|``\ *E*\ ``}``
is the same as that of the :token:`type_restriction` ``(``\ *T* ``| fn`` *P*
``->`` *E*\ ``)``. So the meaning of the example :token:`type_comprehension`
above is ``(Nat | fn n -> even n)``.

.. COMMENT:  ***************************************************************** 

.. _Type-quotients:

Type-quotients
==============

.. productionlist::
  type_quotient: `closed_type_descriptor` / `closed_expression`

Sample :token:`type_quotient`:

.. code-block:: specware

   Nat / (fn (m, n) -> m rem 3 = n rem 3)
   

Restriction. In a :token:`type_quotient` \ *T*\ ``/``\ *q*\ \ , the
:token:`expression` *q* must be a (binary) predicate on the type \
*T*\ ``*``\ *T*\ that is an equivalence relation, as explained below.

Also, note that since a :token:`type_quotient` is a
:token:`new_type_descriptor`, it may appear only as the right-hand
side of a :token:`new_type_definition`.

.. COMMENT:  ================================================================= 

Equivalence relation. Call two values *x* and *y* of type *T*
"*q*-related" if (*x*, *y*) satisfies *q*. Then *q* is an
*equivalence relation*  if,
for all values *x*, *y* and *z* of type *T*,
*x* is *q*-related to itself,
*y* is *q*-related to *x* whenever *x* is *q*-related to *y*, and
*x* is *q*-related to *z* whenever *x* is *q*-related to *y*
and *y* is *q*-related to *z*.
The equivalence relation *q* then partitions the inhabitants of
*T* into *equivalence classes*, being the
maximal subsets of *T* containing mutually *q*-related members.
These equivalence classes will be called "*q*-equivalence classes".

.. COMMENT:  ================================================================= 

The inhabitants of the
*quotient type*  \ *T*\  ``/``\ *q*\ 
are precisely the *q*-equivalence classes into which the inhabitants of
*T* are partitioned by *q*.
For the example above, there are three equivalence classes of natural numbers 
leaving the same remainder on division by 3: the sets {0, 3, 6, ...},
{1, 4, 7, ...} and {2, 5, 8, ...}, and so the quotient type has
three inhabitants.

.. COMMENT:  ================================================================= 

.. COMMENT:  ***************************************************************** 

Expressions
###########

.. productionlist::
  expression: `lambda_form` | `case_expression` | `let_expression` | 
            : `if_expression` | `quantification` | `unique_solution` | 
            : `annotated_expression` | `tight_expression`
  tight_expression: `application` | `closed_expression`
  closed_expression: `op_name` | `local_variable` | `literal` | 
                   : `field_selection` | `tuple_display` | `record_display` | 
                   : `sequential_expression` | `list_display` | `monadic_expression` | 
                   : `structor` | ( `expression` ) | ( `inbuilt_op` )
  inbuilt_op: `inbuilt_prefix_op` | 
            : `inbuilt_infix_op`
  inbuilt_prefix_op: ~
  inbuilt_infix_op: <=> | 
                  : => | 
                  : "|'|" | 
                  : & | 
                  : = | 
                  : ~= | 
                  : |lt||lt|

(The distinctions :token:`tight_` and :token:`closed_` for
:token:`expressions` lack semantic significance, and merely serve the
purpose of avoiding grammatical ambiguities.)

.. COMMENT: ====================================================================

Sample :token:`expressions`:

.. code-block:: specware

   fn (s : String) -> s ^ "."
   case z of {re = x, im = y} -> {re = x, im = -y}
   let x = x + 1 in f(x, x)
   if x <= y then x else y
   fa(x,y) (x <= y)  <=>  ((x<y) or (x = y))
   f(x, x)
   [] : List Arg
   abs(x-y)
   ++
   x
   3260
   z.re
   ("George", Poodle : Dog, 10)
   {name = "George", kind = Poodle : Dog, age = 10}
   (writeLine "key not found"; embed Missing)
   ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
   project 2
   (n + 1)
   (||)
   

Restriction. Like all polymorphic or type-ambiguous constructs, an
:token:`expression` can only be used in a context if its type can be
inferred uniquely, given the :token:`expression` and the context. This
restriction will not be repeated for the various kinds of
:token:`expressions` defined in the following subsections.

.. COMMENT:  ================================================================= 

The meaning of a parenthesized :token:`expression` ``(``\ *E*\ ``)``
is the same as that of the enclosed :token:`expression` *E*. The
meaning of the parenthesized :token:`inbuilt_prefix_op` ``(``\ *P*\
``)`` is the same as that of the :token:`lambda_form` ``fn x ->``\
*P*\ ``x``. The meaning of a parenthesized :token:`inbuilt_infix_op`
``(``\ *I*\ ``)`` is the same as that of the :token:`lambda_form` ``fn
(x,y) -> x``\ *I*\ ``y``. Note that this function is strict in both
arguments, unlike *I* itself.

.. COMMENT:  ================================================================= 

The various other kinds of :token:`expressions` not defined here are
described each in their following respective sections, with the
exception of :token:`local_variable`, whose meaning as an
:token:`expression` is described below.

.. COMMENT:  ================================================================= 

Restriction. A :token:`local_variable` may only be used as an
:token:`expression` if it occurs in the scope of the
:token:`local_variable_list` of a :token:`quantification` or of a
:token:`variable_pattern` in which it is introduced.

.. COMMENT:  ================================================================= 

Disambiguation. A single :token:`simple_name` used as an
:token:`expression` is a :token:`local_variable` when it occurs in the
scope of a :token:`local_variable_list` or :token:`variable_pattern`
in which a synonymous :token:`local_variable` is introduced, and then
it identifies the textually most recent introduction. Otherwise, the
:token:`simple_name` is an :token:`op_name`.

.. COMMENT:  ================================================================= 

A :token:`local_variable` used as an :token:`expression` has the typed
value assigned to it in the environment.

.. COMMENT:  ***************************************************************** 

Lambda-forms
============

.. productionlist::
  lambda_form: fn `match`

Sample :token:`lambda_forms`:

.. code-block:: specware

   fn (s : String) -> s ^ "."
   
   fn | Point _      -> 0
      | Line(z0, z1) -> dist(z0, z1)
   

The value of a :token:`lambda_form` is a partial or total function. If
the value determined for a :token:`lambda_form` as described below is
not a total function, the context must enforce that the function can
not be applied to values for which it is undefined. Otherwise, the
:token:`spec` is ill formed. |SpecwareV| does not attempt to generate
proof obligations for establishing this.

.. COMMENT:  ================================================================= 

The type of a :token:`lambda_form` is that of its :token:`match`. The
meaning of a given :token:`lambda_form` of type \ *S*\ ``->``\ *T*\ is
the function *f* mapping each inhabitant *x* of *S* to a value *y* of
type *T*, where *y* is the return value of *x* for the :token:`match`
of the :token:`lambda_form`. If the :token:`match` accepts each *x* of
type *S* (for acceptance and return value, see the section on
:ref:`Matches <Matches>`) function
*f* is total; otherwise it is
partial, and undefined for those values
*x* rejected.

.. COMMENT:  ================================================================= 

In case of a recursive definition, the above procedure may fail to
determine a value for *y*, in which case function *f* is not total,
but undefined for *x*.

.. COMMENT:  ***************************************************************** 

Case-expressions
================

.. productionlist::
  case_expression: case `expression` of `match`

Sample :token:`case_expressions`:

.. code-block:: specware

   case z of {re = x, im = y} -> {re = x, im = -y}
   
   case s of
      | Empty -> true
      | Push {top = _, pop = rest} -> hasBottom? rest
   

The value of a :token:`case_expression` ``case``\ *E*\ ``of``\ *M*\ is
the same as that of the :token:`application` ``(fn``\ *M*\ ``) (``\
*E*\ ``)``.

.. COMMENT:  ***************************************************************** 

Let-expressions
===============

.. productionlist::
  let_expression: let `let_bindings` in `expression`
  let_bindings: `recless_let_binding` | 
              : `rec_let_binding_sequence`
  recless_let_binding: `pattern` `equals` `expression`
  rec_let_binding_sequence: `rec_let_binding` { `rec_let_binding` }*
  rec_let_binding: def `simple_name` 
                 :    `formal_parameter_sequence` [ `type_annotation`] 
                 :    `equals` `expression`
  formal_parameter_sequence: `formal_parameter` { `formal_parameter` }*

Sample :token:`let_expressions`:

.. code-block:: specware

   let x = x + e in f(x, x)
   let def f x = x + e in f (f x)
   

In the case of a :token:`recless_let_binding` (recless = recursion-
less), the value of the :token:`let_expression` ``let``\ *P*\ ``=``\
*A*\ ``in``\ *E*\ is the same as that of the :token:`application`
``(fn``\ *P*\ ``->``\ *E*\ ``) (``\ *A*\ ``)``. For the first
example above, this amounts to ``f(x + e, x + e)``. Note that ``x =
x + e`` is not interpreted as a recursive definition.

.. COMMENT:  ================================================================= 

In case of a :token:`rec_let_binding_sequence` (rec = recursive), the
:token:`rec_let_bindings` have the role of "local"
:token:`op_definitions`; that is, they are treated exactly like
:token:`op_definitions` except that they are interpreted in the local
environment instead of the global model. For the second example above,
this amounts to ``(x + e) + e``. (If ``e`` is a
:token:`local_variable` in this scope, the definition of ``f`` can not
be "promoted" to an :token:`op_definition`, which would be outside the
scope binding ``e``.) A :token:`spec` with :token:`rec_let_bindings`
can be transformed into one without such by creating
:token:`op_definitions` for each :token:`rec_let_binding` that take
additional arguments, one for each of the :token:`local_variables`
referenced. For the example, in which ``f`` references
:token:`local_variable` ``e``, the :token:`op_definition` for the
"extended" :token:`op` ``f\
\ :sup:`+\```
would be ``def f\\ :sup:`+\`  e x = x + e``, and the
:token:`let_expression` would become ``f\\ :sup:`+\`  e (f\\ :sup:`+\`  e x)``.
The only difference in meaning is that the models of the
transformed :token:`spec` assign a value to the newly introduced
:token:`op` ``f\\ :sup:`+\```.

.. COMMENT:  ================================================================= 

Note that the first occurrence of ``x`` in the above example of a
:token:`rec_let_binding` is a :token:`variable_pattern` and the
second-occurrence is in its scope; the third and last occurrence of
``x``, however, is outside the scope of the first ``x`` and
identifies an :token:`op` or :token:`local_variable` ``x`` introduced
elsewhere. So, without change in meaning, the :token:`rec_let_binding`
can be changed to:

.. code-block:: specware

   let def f xena = xena + e in f (f x)
   

.. COMMENT:  ***************************************************************** 

If-expressions
==============

.. productionlist::
  if_expression: if `expression` then `expression` else `expression`

Sample :token:`if_expression`:

.. code-block:: specware

   if x <= y then x else y
   

The value of an :token:`if_expression` ``if``\ *B*\ ``then``\ *T*\
``else``\ *F*\ is the same as that of the :token:`case_expression`
``case`` *B* ``of true -> (``\ *T*\ ``) | false -> (``\ *F*\ ``)``.

.. COMMENT:  ***************************************************************** 

Quantifications
===============

.. productionlist::
  quantification: `quantifier` ( `local_variable_list` ) `expression`
  quantifier: fa | ex | ex1
  local_variable_list: `annotable_variable` { , `annotable_variable` }*
  annotable_variable: `local_variable` [ `type_annotation` ]
  local_variable: `simple_name`

Sample :token:`quantifications`:

.. code-block:: specware

   fa(x) norm (norm x) = norm x
   ex(e : M) fa(x : M) x <*< e = x & e <*< x = x
   

Restriction. Each :token:`local_variable` of the
:token:`local_variable_list` must be a different :token:`simple_name`.

.. COMMENT:  ================================================================= 

:token:`Quantifications` are non-constructive, even when the domain
type is finitely enumerable. The main uses are in
:token:`type_restrictions` and :token:`type_comprehensions`, and
:token:`claims`. The type of a :token:`quantification` is ``Bool``\
. There are three kinds of quantifiers: ``fa``, for "universal
quantifications" (fa = for all); ``ex``, for "existential
quantifications" (ex = there exists); and ``ex1``, for "uniquely
existential quantifications" (ex1 = there exists one).

.. COMMENT:  ================================================================= 

The value of a :token:`quantification` ``fa (``\ *V*\ ``)``\ *E*\ \ ,
in which *V* is a :token:`local_variable_list` and *E* is an
:token:`expression`, is determined as follows. Let *M* be the
:token:`match` ``(``\ *V*\ ``) ->``\ *E*\ \ . If *M* has return value
``true`` for each value *x* in its domain, the value of the
:token:`quantification` is ``true``\ ; otherwise it is ``false``.

.. COMMENT:  ================================================================= 

The value of a :token:`quantification` ``ex (``\ *V*\ ``)``\ *E*\ in
which *V* is a :token:`local_variable_list` and *E* is an
:token:`expression`, is determined as follows. Let *M* be the
:token:`match` ``(``\ *V*\ ``) ->``\ *E*\ \ . If *M* has return value
``true`` for at least one value *x* in its domain, the value of the
:token:`quantification` is ``true``\ ; otherwise it is ``false``.

.. COMMENT:  ================================================================= 

The value of a :token:`quantification` ``ex1 (``\ *V*\ ``)``\ *E*\ in
which *V* is a :token:`local_variable_list` and *E* is an
:token:`expression`, is determined as follows. Let *M* be the
:token:`match` ``(``\ *V*\ ``) ->``\ *E*\ \ . If *M* has return value
``true`` for precisely one value *x* in its domain, the value of the
:token:`quantification` is ``true``\ ; otherwise it is ``false``.

.. COMMENT:  ================================================================= 

Note that a :token:`quantifier` must be followed by an opening
parenthesis\ ``(`` \ . So ``fa x (x = x)``, for example, is
ungrammatical.

.. COMMENT:  ***************************************************************** 

Unique-solutions
================

.. productionlist::
  unique_solution: the ( `local_variable_list` ) `expression`

Sample :token:`unique_solution`:

.. code-block:: specware

   the(x : S) f(x) = y
   

Restriction, Each :token:`local_variable` of the
:token:`local_variable_list` must be a different :token:`simple_name`.

.. COMMENT:  ================================================================= 

Restriction. The type of the :token:`expression` must be ``Bool``\
.

.. COMMENT:  ================================================================= 

Restriction. A :token:`unique_solution` ``the (``\ *V*\ ``)``\ *E*\
may only be used in a context where the value of ``ex1 (``\ *V*\
``)``\ *E*\ is ``true``.

.. COMMENT:  ================================================================= 

:token:`Unique_solutions` are non-constructive, even when the domain
type is finitely enumerable. The type of a :token:`unique_solution` is
the type of its :token:`local_variable_list`.

.. COMMENT:  ================================================================= 

The value of a :token:`unique_solution` ``the (``\ *V*\ ``)``\ *E*\ \
, in which *V* is a :token:`local_variable_list` and *E* is an
:token:`expression`, is determined as follows. Let *M* be the
:token:`match` ``(``\ *V*\ ``) ->``\ *E*\ \ . The value of the
:token:`unique_solution` is then the unique value *x* in the domain of
*M* such that the :token:`match` ``(``\ *V*\ ``) ->``\ *E*\ has return
value ``true`` for *x*.

.. COMMENT:  ***************************************************************** 

.. _Annotated-expressions:

Annotated-expressions
=====================

.. productionlist::
  annotated_expression: `tight_expression` `type_annotation`

Restriction. In an :token:`annotated_expression` *E* ``:`` *T*, the
:token:`expression` *E* must have type *T*.

.. COMMENT:  ================================================================= 

Sample :token:`annotated_expression`:

.. code-block:: specware

   [] : List Arg
   Positive : Sign
   

The value of an :token:`annotated_expression` \ *E*\ ``:``\ *T*\ is
the value of *E*.

.. COMMENT:  ================================================================= 

The type of some :token:`expressions` is polymorphic. For example, for
any type *T*, ``[]`` denotes the empty list of type ``List``\ *T*\ \
. Likewise, :token:`constructors` of parameterized sum types can be
polymorphic, as the constructor ``None`` of

.. code-block:: specware

   type Option a = | Some a | None
   

.. COMMENT:  ***************************************************************** 

Applications
============

.. productionlist::
  application: `prefix_application` | `infix_application`
  prefix_application: `application_head` `actual_parameter`
  application_head: `closed_expression` | `inbuilt_prefix_op` | `prefix_application`
  actual_parameter: `closed_expression`
  infix_application: `operand` `infix_operator` `operand`
  operand: `tight_expression`
  infix_operator: `op_name` | 
                : `inbuilt_infix_op`

Sample :token:`applications`:

.. code-block:: specware

   f (x, x)
   f x (g y)
   x + 1
   

Restriction. An :token:`infix_operator`, whether qualified or
unqualified, can not be used without more as an
:token:`actual_parameter` or :token:`operand` (and in the case of an
:token:`inbuilt_op`, it can not be used without more as any other kind
of :token:`expression` either). To use an :token:`infix_operator` in
such cases, it must be enclosed in parentheses, as for example in the
:token:`prefix_applications` ``foldl (+) 0`` and ``foldl ( *) 1`` or
the :token:`infix_application` ``(<) o ival``. Note the space
between "\ ``(``\ " and "\ ``*``\ ", since without space "\ ``(*``\ "
signals the start of a :token:`comment`.

.. COMMENT: ====================================================================

Restriction. An :token:`op_name` can be used as an
:token:`infix_operator` only if it has been declared as such in an
:token:`op_declaration` (see under
:ref:`Op-declarations <Op-declarations>`).

.. COMMENT:  ================================================================= 

Disambiguation. An :token:`infix_application` *P M Q N R*, in which
*P*, *Q* and *R* are :token:`operands` and *M* and *N* are
:token:`infix_operators`, is interpreted as either ``(*P M Q*)`` \ *N
R* or ``*P M* (*Q N R*)``. The choice is made as follows. If *M* has
higher priority than *N*, or the priorities are the same but *M* is
left-associative, the interpretation is ``(*P M Q*)`` \ *N R*. In all
other cases the interpretation is ``*P M* (*Q N R*)``. For example,
given

.. code-block:: specware

   op @ infixl 10: Nat * Nat -> Nat
   op ** infixr 20: Nat * Nat -> Nat
   

the following interpretations hold:

.. code-block:: specware

   1 ** 2 @ 3  =  (1 **  2) @ 3
   1 @ 2 @ 3  =  (1 @  2) @ 3
   1 @ 2 ** 3  =   1 @ (2  ** 3)
   1 ** 2 ** 3  =   1 ** (2  ** 3)
   

Note that no type information is used in the disambiguation. If ``(1 @
2) ** 3`` is type-correct but ``1 @ (2 ** 3)`` is not, the
:token:`expression` ``1 @ 2 ** 3`` is type-incorrect, since its
interpretation is.

For the application of this disambiguation rule, the
:token:`inbuilt_ops` have :token:`fixity` as suggested by the
following pseudo-:token:`op_declarations`:

.. code-block:: specware

   op <=> infixr 12 : Bool * Bool -> Bool 
   op =>  infixr 13 : Bool * Bool -> Bool 
   op ||  infixr 14 : Bool * Bool -> Bool 
   op &&  infixr 15 : Bool * Bool -> Bool 
   op =   infixr 20 : [a]   a * a       -> Bool 
   op ~=  infixr 20 : [a]   a * a       -> Bool 
   op <<  infixl 25 : {*x*:*A*, ... , *y*:*B*, ...} * {*x*:*A*, ... , *z*:*C*, ...}
                   -> {*x*:*A*, ... , *y*:*B*, ... , *z*:*C*, ...}
   

.. COMMENT:  ================================================================= 

Restriction. In an :token:`application` *H* *P*, in which *H* is an
:token:`application_head` and *P* an :token:`actual_parameter`, the
type of *(H)* must be some function type \ *S*\ ``->``\ *T*\ \ , and
then *P* must have the domain type *S*. The type of the whole
:token:`application` is then *T*. In particular, in an
:token:`application` ``~``\ *P*\ the type of both *P* and the
:token:`application` is ``Bool``.

.. COMMENT:  ================================================================= 

The meaning of :token:`prefix_application` ``~``\ *P* is the same as
that of the :token:`if_expression` ``if`` *P* ``then false else
true``.

The value of :token:`prefix_application` *H P*, in which
:token:`application_head` *H* is a :token:`closed_expression` or
another :token:`prefix_application`, is the value returned by function
*(H)* for the argument value *P*.

The meaning of :token:`infix_application` *P N Q*, in which *P* and
*Q* are :token:`operands` and *N* is an :token:`op_name`, is the same
as that of the :token:`prefix_application` *N(P, Q)*.

The meaning of :token:`infix_application` \ *P*\ ``=>``\ *Q*\ \ , in
which *P* and *Q* are :token:`operands`, is the same as that of the
:token:`if_expression` ``if`` *P* ``then`` *Q* ``else true``.

The meaning of :token:`infix_application` \ *P*\ ``||``\ *Q*\ \ , in
which *P* and *Q* are :token:`operands`, is the same as that of the
:token:`if_expression` ``if`` *P* ``then true else`` *Q*.

The meaning of :token:`infix_application`  *P* ``&&`` *Q*
, in which *P* and *Q* are :token:`operands`, is the same as that of
the :token:`if_expression` ``if`` *P* ``then`` *Q* ``else false``.

The value of :token:`infix_application` \ *P*\ ``=``\ *Q*\ \ , in
which *P* and *Q* are :token:`operands`, is ``true`` if *P* and *Q*
have the same value, and ``false`` otherwise. *P* and *Q* must have
the same type, or else have types that are subtypes of the same
supertype. In the latter case, the comparison is the same as for the
values of the :token:`operands` coerced to the supertype, so, for
example, the value of ``(1:Nat)=(1:PosNat)`` is ``true``.

The meaning of :token:`infix_application` \ *P*\ ``~=``\ *Q*\ \ , in
which *P* and *Q* are :token:`operands`, is the same as that of the
:token:`prefix_application` ``~(``\ *P*\ ``=``\ *Q*\ ``)``.

An :token:`infix_application` *P* ``<<`` *Q* is also called a
"record update". In a record update *P* ``<<`` *Q* , in which
*P* and *Q* are :token:`operands`, *P* and *Q* must have record types,
referred to as *S* and *T*, respectively. Moreover, for each
:token:`field_name` *F* these types *S* and *T* have in common, the
field types for *F* in *S* and *T* must be the same, or be subtypes of
the same supertype. The type of *P* ``<<`` *Q* is then the record
type *R* whose :token:`field_names` are formed by the union of the
:token:`field_names` of *S* and *T*, where for each
:token:`field_name` *F* in that union, the type of field *F* in *R* is
that of field *F* in *T* if *F* is a field of *T*, and otherwise the
type of field *F* in *S*. Likewise, the value of *P* ``<<`` *Q*
is the record value of type *R* whose field value of each field *F* is
that of field *F* in *Q* if *F* is a field of *T*, and otherwise the
field value of field *F* in *P*. So, for example, the value of ``{a=1,
b=#z} << {a=2, c=true}`` is ``{a=2, b=#z, c=true}``\ : fields of the
right-hand side :token:`operand` take precedence over the left-hand
side when present in both.

.. COMMENT:  ***************************************************************** 

.. COMMENT:  OLD:
            %%%<section id="Restrict-expressions"><title>Restrict-expressions</title>
            %%%<para>
            %%%&lt;&lt;
            %%%||:token:`restrict_expression` ::= restrict :token:`closed_expression` `closed-expression
            %%%``
            %%%Sample :token:`restrict_expression`:
            %%%[[
            %%%||    restrict posNat? (n+1)
            %%%]]
            %%%Restriction.
            %%%In a :token:`restrict_expression`
            %%%\ ``restrict``\ *P*\  *E*
            %%%the :token:`expression` *P* must have function
            %%%type \ *T*\  ``-> Bool`` and the
            %%%:token:`expression` *E* must have type
            %%%*T* for some
            %%%*T*.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%The type of a :token:`restrict_expression`
            %%%\ ``restrict``\ *P*\ 
            %%%*E*,
            %%%where *P* has
            %%%type \ *T*\  ``-> Bool``,
            %%%is the type
            %%%\ ``(``\ *T*\  ``|``\ *P*\ ``)``.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%A :token:`restrict_expression`
            %%%\ ``restrict``\ *P*\  *E*
            %%%is a convenient notation for the :token:`let_expression`
            %%%\ ``let relax``\ *P*\  \ *V*\  ``=``\ *E*\  ``in``\ *V*\ \ , where
            %%%*V* is some unique fresh :token:`simple_name`, that
            %%%is, it is any :token:`simple_name` that does not already occur in the
            %%%:token:`spec`, directly or indirectly through an import.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%The use of this :token:`restrict_expression` engenders a proof obligation
            %%%that the value of *E* satisfies predicate
            %%%*P*.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%For example, assuming the :token:`definitions` from the Base Library
            %%%for ``Nat``, the :token:`restrict_expression`
            %%%\ ``restrict posNat? (n+1)`` has type
            %%%\ ``PosNat``.
            %%%The proof obligation here is that, in the context,
            %%%\ ``(n+1)>0``.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%The purpose of :token:`restrict_expressions` is to make it
            %%%explicit that an :token:`expression` whose a-priori type is some
            %%%supertype *T* actually is guaranteed
            %%%(or required) to have subtype
            %%%\ ``(``\ *T*\  ``|``
            %%%\ \ *P*\ ``)``.
            %%%Note, however, that |Metaslang| does not require the explicit use of a
            %%%:token:`restrict_expression`
            %%%to restrict
            %%%an :token:`expression` from a type to a subtype if the
            %%%context requires the latter.
            %%%Implicit restriction will take place when needed.
            %%%For example, in the :token:`expression` ``7 div 2`` the :token:`nat_literal` ``2``
            %%%of type ``Nat`` is implicitly restricted to type ``PosNat``,
            %%%a subtype of ``Nat``, to accommodate the division operator
            %%%\ ``div``, whose second argument has type ``PosNat``.
            %%%But note that implicit restriction engenders the same proof
            %%%obligation as results when using an explicit
            %%%:token:`restrict_expression`.
            %%%</para>
            %%%</section>

.. COMMENT:  ***************************************************************** 

Op-names
========

.. productionlist::
  op_name: `name`

Sample :token:`op_names`:

.. code-block:: specware

   length
   >=
   DB_LOOKUP.Lookup
   

Restriction. An :token:`op_name` may only be used if there is an
:token:`op_declaration` and/or :token:`op_definition` for it in the
current :token:`spec` or in some :token:`spec` that is imported
(directly or indirectly) in the current :token:`spec`. If there is a
unique :token:`qualified_name` for a given unqualified ending that is
type-correct in the context, the qualification may be omitted for an
:token:`op_name` used as an :token:`expression`. So overloaded
:token:`ops` may only be used as such when their type can be
disambiguated in the context.

.. COMMENT:  ================================================================= 

.. COMMENT:  ====================== NOT YET ==================================
            ** <para>
            ** Restriction.
            ** Overloaded :token:`ops`, when used as :token:`expressions`, have an ambiguous type.
            ** They may only be used as such when their type can be
            ** disambiguated in the context.
            ** For example, consider
            ** [[
            ** ||    op abs : Nat -> Nat
            ** ||    op abs : Char -> Nat
            ** ||
            ** ||    def ok (c : Char) = abs c
            ** ||    def ko x          = abs x
            ** ]]
            ** In the application ``abs c``
            ** (the right-hand side of the :token:`definition` for ``ok``\ )
            ** ``c`` is known to have type ``Char`` in the context.
            ** This is enough to determine ``abs`` as identifying here
            ** ``op abs : Char -> Nat``.
            ** In the application ``abs x``
            ** (the right-hand side of the :token:`definition` for ``ko``\ )
            ** the context gives no constraint on the type of ``x``,
            ** and no type-disambiguation for ``abs`` is possible, so its
            ** use there is incorrect.
            ** </para>
                 ====================== TEY TON ================================== 

.. COMMENT:  ================================================================= 

The value of an :token:`op_name` is the value assigned to it in the
model. (In this case, the context can not have superseded the original
assignment.)

.. COMMENT:  ***************************************************************** 

Literals
========

.. productionlist::
  literal: `bool_literal` | `nat_literal` | `char_literal` | `string_literal`

Sample :token:`literals`:

.. code-block:: specware

   true
   3260
   #z
   "On/Off switch"
   

Restriction: No whitespace is allowed anywhere inside any kind of
:token:`literal`, except for "significant" whitespace in
:token:`string_literals`, as explained there.

.. COMMENT: ====================================================================

:token:`Literals` provide denotations for the inhabitants of the
inbuilt and "base-library" types ``Bool``, ``Nat``, ``Char``
and ``String``. The value of a :token:`literal` is independent of
the environment.

.. COMMENT: ====================================================================

(There are no :token:`literals` for the base-library type ``Integer``\
. For non-negative integers, a :token:`nat_literal` can be used. For
negative integers, apply the unary base-library :token:`op` ``-``,
which negates an integer: ``-1`` denote the negative integer ``-`` 1.)

.. COMMENT:  ***************************************************************** 

Bool-literals
----------------

.. productionlist::
  bool_literal: true | 
                 : false

Sample :token:`bool_literals`:

.. code-block:: specware

   true
   false
   

The type ``Bool`` has precisely two inhabitants, the values of
``true`` and ``false``.


.. COMMENT:  ***************************************************************** 

Nat-literals
------------

.. productionlist::
  nat_literal: `decimal_digit`     { `decimal_digit` }* | 
             : 0 X `hexadecimal_digit` { `hexadecimal_digit` }* | 
             : 0 x `hexadecimal_digit` { `hexadecimal_digit` }* | 
             : 0 O `octal_digit`       { `octal_digit`  }* | 
             : 0 o `octal_digit`       { `octal_digit`  }* | 
             : 0 B `binary_digit`      { `binary_digit` }* | 
             : 0 b `binary_digit`      { `binary_digit` }*
  hexadecimal_digit: `decimal_digit` | 
                   : a | b | c | d | e | f | 
                   : A | B | C | D | E | F
  octal_digit: 0 | 1 | 2 | 3 | 4 | 
             : 5 | 6 | 7
  binary_digit: 0 | 1

Sample :token:`nat_literals`:

.. code-block:: specware

   3260
   007
   0Xdeadbeef
   0O777
   0b111001111
   

The :token:`type_descriptor` ``Nat`` is, by definition, the subtype of
``Integer`` restricted to the non-negative integers 0, 1, 2,

... , which we identify with the natural numbers.
The value of a :token:`nat_literal` composed entirely of
:token:`decimal_digits` is the natural number of which it is a decimal
representation; for example, the :token:`nat_literal` ``3260`` denotes
the natural number 3260.
If the :token:`nat_literal` starts with ``0X`` or ``0x``, its value is the
natural number of which the following sequence of :token:`hexadecimal_digits` is a
hexadecimal representation.
For example, ``0x17B`` denotes the value 1|times|16|sup2|+7|times|16+11
= 379.
Likewise, ``0O`` or ``0o`` (a digit ``0`` followed by an uppercase
letter ``O`` or a lower case letter ``o``\ ) introduces an octal
representation, and ``0B`` or ``0b`` a binary representation.
Leading digits ``0`` have no significance:
both ``007`` and ``7`` denote the number 7.

Note that hexadecimal, octal, and binary literals are converted to an
internal representation that does not retain their base. For example,
given

.. code-block:: specware

   Ned = spec 
     op N : Nat = 0x17B
   end-spec
   

the |Specware| Shell command ``show Ned`` will print as

.. code-block:: specware

   spec 
     op N : Nat = 379
   end-spec
   

.. COMMENT:  ***************************************************************** 

Char-literals
-------------

.. productionlist::
  char_literal: #`char_literal_glyph`
  char_literal_glyph: `char_glyph` | 
                    : "
  char_glyph: `letter` | `decimal_digit` | `other_char_glyph`
  other_char_glyph: ! |  : | @ | # | * | % | 
                  : ^ | & | * | ( | ) | _ | 
                  : - | + | = | "|" | ~ | ` | 
                  : . | , | < | > | ? | / | 
                  : ; | " | "[" | "]" | "{" | "}" | 
                  : \\ | \" | \a | \b | \t | 
                  : \n | \v | \f | \r | \s | 
                  : \x `hexadecimal_digit` `hexadecimal_digit`

.. COMMENT: ====================================================================

Sample :token:`char_literals`:

.. code-block:: specware

   #z
   #\x7a
   

The type ``Char`` is inhabited by the 256 8-bit
*characters*
occupying decimal positions 0 through 255 (hexadecimal
positions 00 through FF) in the ISO 8859-1 code table.
The first 128 characters of that code table are the
traditional ASCII characters (ISO 646).
(Depending on the operating environment, in particular the
second set of 128 characters -- those with
"the high bit set" -- may print or otherwise
be visually presented differently than intended by the
ISO 8859-1 code.)
The value of a :token:`char_literal` is a character of type
``Char``.

.. COMMENT: ====================================================================

The value of a :token:`char_literal` ``#``\ *G*\ \ , where *G* is a
:token:`char_glyph`, is the character denoted by *G*. For example,
``#z`` is the character that prints as ``z``. The two-mark
:token:`char_literal` ``#"`` provides a variant notation of the three-
mark :token:`char_literal` ``#\"`` and yields the character\ ``"`` \
(decimal position 34).

.. COMMENT: ====================================================================

Each one-mark :token:`char_glyph` *C* denotes the character that
"prints" as *C*. The two-mark :token:`char_glyph` ``\\`` denotes the
character\ ``\`` \ (decimal position 92), and the two-mark
:token:`char_glyph` ``\"`` denotes the character ``"`` \ (decimal
position 34).

.. COMMENT: ====================================================================

Notations are provided for denoting eight "non-printing" characters,
which, with the exception of the first, are meant to regulate lay-out
in printing; the actual effect may depend on the operating
environment:

.. list-table::
   :widths: 40 40 40
   :header-rows: 1


   *  - glyph
      - decimal
      - :token:`name`
   *  - ``\a``
      -    7
      - bell
   *  - ``\b``
      -    8
      - backspace
   *  - ``\t``
      -    9
      - horizontal tab
   *  - ``\n``
      -   10
      - newline
   *  - ``\v``
      -   11
      - vertical tab
   *  - ``\f``
      -   12
      - form feed
   *  - ``\r``
      -   13
      - return
   *  - ``\s``
      -   32
      - space

Finally, every character can be obtained using the
hexadecimal representation of its position.
The four-mark :token:`char_glyph`
``\x``\ *H*\ :sub:`1`\ *H*\ :sub:`0`
denotes the character with hexadecimal position
*H*\ :sub:`1` *H*\ :sub:`0`,
which is decimal position
16 times the decimal value of :token:`hexadecimal_digit`
*H*\ :sub:`1`  plus
the decimal value of :token:`hexadecimal_digit`
*H*\ :sub:`0`,
where the decimal value of the digits ``0`` through ``9`` is
conventional, while the six extra digits ``A`` through ``F``
correspond to 10 through 15.
The case (lower or upper) of the six extra
digits is not significant.
For example, ``\x7A`` or equivalently ``\x7a`` has decimal
position 16 times 7 plus 10 = 122, and either version denotes
the character ``z``.
The "null" character can be obtained by using
``\x00``.

.. COMMENT:  ***************************************************************** 

.. _String-literals:

String-literals
---------------

.. productionlist::
  string_literal: "`string_body`"
  string_body: { `string_literal_glyph` }*
  string_literal_glyph: `char_glyph` | `significant_whitespace`
  significant_whitespace: `space` | `tab` | `newline`

The presentation of a :token:`significant_whitespace` is the
whitespace suggested by the :token:`name` (:token:`space`,
:token:`tab` or :token:`newline`).

.. COMMENT: ====================================================================

Sample :token:`string_literals`:

.. code-block:: specware

   ""
   "see page"
   "see\spage"
   "the symbol ' is a single quote"
   "the symbol \" is a double quote"
   

The type ``String`` is inhabited by the
*strings*, which are (possibly empty)
sequences of characters.
The type ``String`` is primitive; it is a different type
than the isomorphic type ``List Char``, and the list operations 
can not be directly applied to strings.

.. COMMENT: ====================================================================

The value of a :token:`string_literal` is the sequence of characters
denoted by the :token:`string_literal_glyphs` comprising its
:token:`string_body`, where the value of a
:token:`significant_whitespace` is the whitespace character suggested
by the :token:`name` (space, horizontal tab or newline). For example,
the :token:`string_literal` ``"seepage"`` is different from ``"see
page"``\ ; the latter denotes an eight-character string of which the
fourth character is a space. The space can be made explicit by using
the :token:`char_glyph` ``\s``.

.. COMMENT: ====================================================================

When a double-quote character\ ``"`` \ is needed in a string, it must
be escaped, as in ``"[6'2\"]"``, which would print like this:
``[6'2"``\ ].

.. COMMENT:  ***************************************************************** 

Field-selections
================

.. productionlist::
  field_selection: `closed_expression` . `field_selector`
  field_selector: `nat_literal` | `field_name`

.. COMMENT:  No longer needed because of transformation to project F E ****
            ** Restriction.
            ** When the :token:`field_selector` is some :token:`nat_literal` with value
            ** *i*, the type of the
            ** :token:`closed_expression` must be a product type,
            ** and if the number of components of that product type is
            ** *n*, it must hold that
            ** *i* is one of the values 1 through 
            ** *n*.
            ** When the :token:`field_selector` is some :token:`field_name`
            ** *F*, the type of the
            ** :token:`closed_expression` must be a record type, one of whose
            ** fields has that :token:`field_name` *F*.
            ** </para>
            ** ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
            ** <para>
            **** No longer needed because of transformation to project F E 

Disambiguation.
A :token:`closed_expression` of the form *M*\ ``.``\ *N*, in which *M* and
*N* are :token:`simple_names`, is interpreted as an :token:`op` if *M*\ ``.``\ *N*
occurs as the :token:`op_name` of an :token:`op_declaration` or :token:`op_definition`
in the :token:`spec` in which it occurs or in the set of :token:`simple_names`
imported from another :token:`spec` through an :token:`import_declaration`.
Otherwise, *M*\ ``.``\ *N* is interpreted as a :token:`field_selection`.
(The effect of a :token:`field_selection` can always be obtained
with a :token:`projector`.)

.. COMMENT: ====================================================================

Sample :token:`field_selections`:

.. code-block:: specware

   triple.2
   z.re
   

.. COMMENT:  No longer needed because of transformation to project F E ****
            ** Let the tuple or record *v* be the value of the
            ** :token:`closed_expression` of the :token:`field_selection`, and let the natural
            ** number *i* be determined as follows.
            ** When the :token:`field_selector` is some :token:`nat_literal`
            ** *N*,
            ** *i* is the value of
            ** *N*.
            ** When the :token:`field_selector` is some :token:`field_name`
            ** *F*, *i*
            ** is the position selected by *F* in
            ** type *T*, as discussed under
            ** :token:`Type_records`.
            ** The value of the :token:`field_selection` is then the
            ** *i*th component of
            ** *v*.
            **** No longer needed because of transformation to project F E 

A :token:`field_selection` *E*\ ``.``\ *F* 
is a convenient notation for the equivalent :token:`expression`
``(project`` *F* *E* ``)``.
(See under :ref:`Projectors <Projectors>`.)

.. COMMENT:  ***************************************************************** 

Tuple-displays
==============

.. productionlist::
  tuple_display: ( `tuple_display_body` )
  tuple_display_body: [ `expression` , `expression` { , `expression` }* ]

Sample :token:`tuple_display`:

.. code-block:: specware

   ("George", Poodle : Dog, 10)
   

Note that a :token:`tuple_display_body` contains either no
:token:`expressions`, or else at least two.

.. COMMENT: ====================================================================

The value of a :token:`tuple_display` whose
:token:`tuple_display_body` is not empty, is the tuple whose
components are the respective values of the :token:`expressions` of
the :token:`tuple_display_body`, taken in textual order. The type of
that tuple is the "product" of the corresponding types of the
components. The value of ``()`` is the empty tuple, which is the sole
inhabitant of the unit type ``()``. (The fact that the notation
``()`` does double duty, for a :token:`type_descriptor` and as an
:token:`expression`, creates no ambiguity. Note also that -- unlike
the empty :token:`list_display` ``[]`` -- the :token:`expression`
``()`` is monomorphic, so there is no need to ever annotate it with a
:token:`type_descriptor`.)

.. COMMENT:  ***************************************************************** 

Record-displays
===============

.. productionlist::
  record_display: "{" `record_display_body` "}"
  record_display_body: [ `field_filler` { , `field_filler` }* ]
  field_filler: `field_name` = `expression`

Sample :token:`record_display`:

.. code-block:: specware

   {name = "George", kind = Poodle : Dog, age = 10}
   

The value of a :token:`record_display` is the record whose components
are the respective values of the :token:`expressions` of the
:token:`record_display_body`, taken in the lexicographic order of the
:token:`field_names`, as discussed under
:ref:`*Type-records* <Type-records>`.
The type of that record is the record type with the same set
of :token:`field_names`, where the type for each :token:`field_name`
*F* is the type of
the corresponding type of the component selected by
*F* in the record.
The value of ``{}`` is the empty tuple, which is the sole
inhabitant of the unit type ``()``.
(For :token:`expressions` as well as for :token:`type_descriptors`, the notations
``{}`` and ``()`` are fully interchangeable.)

.. COMMENT:  ***************************************************************** 

Sequential-expressions
======================

.. productionlist::
  sequential_expression: ( `open_sequential_expression` )
  open_sequential_expression: `void_expression` ; `sequential_tail`
  void_expression: `expression`
  sequential_tail: `expression` | `open_sequential_expression`

Sample :token:`sequential_expression`:

.. code-block:: specware

   (writeLine "key not found"; embed Missing)
   

A :token:`sequential_expression` ``(`` *V* ``;`` *T* ``)`` is
equivalent to the :token:`let_expression` ``let _ =`` *V* ``in (`` *T*
``)``. So the value of a :token:`sequential_expression` ``(`` *V*\
:sub:`1`\ ``;`` ... ``;`` *V*\ :sub:`n` ``;`` *E* ``)`` is the value
of its last constituent :token:`expression` *E*.

.. COMMENT: ====================================================================

:token:`Sequential_expressions` can be used to achieve non-functional
"side effects", effectuated by the elaboration of the
:token:`void_expressions`, in particular the output of a message. This
is useful for tracing the execution of generated code. The equivalent
effect of the example above can be achieved by a :token:`let_binding`:

.. code-block:: specware

   let _ = writeLine "key not found" in
   embed Missing
   

(If the intent is to temporarily add, and later remove or disable the
tracing output, this is probably a more convenient style, as the
modifications needed concern a single full text line.) Any values
resulting from elaborating the :token:`void_expressions` are
discarded.

.. COMMENT:  ***************************************************************** 

List-displays
=============

.. productionlist::
  list_display: "[" `list_display_body` "]"
  list_display_body: [ `expression` { , `expression` }* ]

Sample :token:`list_display`:

.. code-block:: specware

   ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
   

Restriction. All :token:`expressions` of the
:token:`list_display_body` must have the same type.

.. COMMENT: ====================================================================

Note that a :token:`list_display` ``[]`` with empty
:token:`list_display_body` is polymorphic, and may need to be type-
disambiguated, for example with a :token:`type_annotation`. In a case
like ``[[], [1]]``, there is no need to disambiguate ``[]``, since
the above restriction already implies that ``[]`` here has the same
type as ``[1]``, which has type ``List Nat``.

.. COMMENT: ====================================================================

The parameterized type ``List``, although a base-library type, is
actually not primitive, but defined by:

.. code-block:: specware

   type List a =
     | Nil
     | Cons a * List a
   

The empty :token:`list_display` ``[]`` denotes the same list as the
:token:`expression` ``Nil``, a singleton :token:`list_display` ``[``\
*E*\ ``]`` denotes the same list as the :token:`expression` ``Cons
(``\ *E*\ ``, Nil)``, and a multi-element :token:`list_display` ``[``
*E*\ :sub:`1`, *E*\ :sub:`2`, ``...``, *E*\ :sub:`n`\ ``]`` denotes
the same list as the :token:`expression` ``Cons``\ (\ *E*\ :sub:`1`,
``Cons`` (\ *E*\ :sub:`2`, ``...``, ``Cons`` (*E*\ :sub:`n`,
``Nil``))).

.. COMMENT:  ***************************************************************** 

Monadic-expressions
===================

.. productionlist::
  monadic_expression: "{" `open_monadic_expression` "}"
  open_monadic_expression: `monadic_statement` ; `monadic_tail`
  monadic_statement: `expression` | `monadic_binding`
  monadic_binding: `pattern` <- `expression`
  monadic_tail: `expression` | `open_monadic_expression`

Sample :token:`monadic_expression`:

.. code-block:: specware

   {x <- a; y <- b; f(x, y)}
   

Restriction. :token:`Monadic_expressions` can only be used in a
context containing the following :token:`spec`, or a refinement
thereof, possibly qualified, as a sub-:token:`spec` (see under
:ref:`Substitutions <Substitutions>`):

.. code-block:: specware

   spec
     type Monad a
   
     op monadBind : [a,b] (Monad a) * (a -> Monad b) -> Monad b
     op monadSeq  : [a,b] (Monad a) *      (Monad b) -> Monad b
     op return : [a] a -> Monad a
   
     axiom left_unit is
       [a,b] fa (f : a -> Monad b, x : a)
         monadBind (return x, f) = f x
   
     axiom right_unit is
       [a] fa (m : Monad a)
         monadBind (m, return) = m
   
     axiom associativity is
       [a,b,c] fa (m : Monad a, f : a -> Monad b, h : b->Monad c)
         monadBind (m, (fn x -> monadBind (f x, h))) =
         monadBind (monadBind (m, f), h)
   
     axiom non_binding_sequence is
       [a] fa (f : Monad a, g : Monad a)
         monadSeq (f, g) = monadBind (f, fn _ -> g)
   
   end-spec
   

(This :token:`spec` can be found, qualified with ``Monad``, in the library :token:`spec`
``/Library/General/Monad``.)
A :token:`monadic_expression` may further only be used when
the non-monadic :token:`expression` it is equivalent to (see below)
is itself a valid :token:`expression`.

A :token:`monadic_expression` ``{`` *M* ``}`` is equivalent to the
:token:`open_monadic_expression` *M*.

A :token:`monadic_tail` *E*, where *E* is an :token:`expression`, is
equivalent to the :token:`expression` *E*.

A :token:`monadic_tail` *M*, where *M* is an
:token:`open_monadic_expression`, is equivalent to the
:token:`open_monadic_expression` *M*.

An :token:`open_monadic_expression` *E* ``;`` *T*, where *E* is an
:token:`expression`, is equivalent to the :token:`application`
``monadSeq (``\ *E*\ ``,``\ *T'*\ ``)``, where *T'* is an
:token:`expression` that is equivalent to the :token:`monadic_tail`
*T*.

An :token:`open_monadic_expression` *P*\ ``<-`` *E*\ ``;``\ *T* is
equivalent to the :token:`application` ``monadBind (`` *E* ``, fn``
*P* ``->`` *T'* ``)``, where *T'* is an :token:`expression`
that is equivalent to the :token:`monadic_tail` *T*.

.. COMMENT:  ***************************************************************** 

.. _Structors:

Structors
=========

.. productionlist::
  structor: `projector` | `quotienter` | `chooser` | `embedding_test`

.. COMMENT:  *****************************************************************
            .. productionlist::
            ********************************************************************** 

The :token:`structors` are a medley of constructs, all having polymorphic
or type-ambiguous function types and denoting special functions
that go between structurally related types, the destructors of product types.

.. COMMENT: ====================================================================

Restriction. Like all polymorphic or type-ambiguous constructs, a
:token:`structor` can only be used in a context where its type can be
inferred uniquely. This restriction will not be repeated for the
various kinds of :token:`structors` described in the following
subsections.

.. COMMENT: ====================================================================

For example, the following well-formed :token:`spec` becomes ill
formed when any of the :token:`type_annotations` is omitted:

.. code-block:: specware

   spec
     def [a] p2 = project 2 : String *  a  ->  a
     def     q2 = project 2 : String * Nat -> Nat
   end-spec
   

.. COMMENT:  ***************************************************************** 

.. _Projectors:

Projectors
----------

.. productionlist::
  projector: project `field_selector`

Sample :token:`projectors`:

.. code-block:: specware

   project 2
   project re
   

When the :token:`field_selector` is some :token:`nat_literal` with
value *i*, it is required that *i* be at least 1. The type of the
:token:`projector` is a function type (whose domain type is a product
type) of the form *T*\ :sub:`1` ``*`` *T*\ :sub:`2` ``* ... *`` *T*\
:sub:`n` ``->``\ *T*\ :sub:`i`, where *n* is at least *i*, and the
value of the :token:`projector` is the function that maps each
*n*-tuple (*v*\ :sub:`1`, *v*\ :sub:`2`, ... , *v*\ :sub:`n`)
inhabiting the domain type to its *i*\th component *v*\ :sub:`i`.

.. COMMENT: ====================================================================

When the :token:`field_selector` is some :token:`field_name` *F*, the
type of the :token:`projector` is a function type (whose domain type
is a record type) of the form ``{``\ *F*\ :sub:`1` ``:``\ *T*\
:sub:`1` ``,`` *F*\ :sub:`2` ``:`` *T*\ :sub:`2` ``, ...,`` *F*\
:sub:`n` : *T* :sub:`n` ``}` ->`` \ *T*\ :sub:`i`, where *F* is the
same :token:`field_name` as *F*\ :sub:`i` for some natural number *i*
in the range 1 through *n*.  Assuming that the fields are
lexicographically ordered by :token:`field_name` (see under
:ref:`Type-records <Type-records>`), the value of the
:token:`projector` is the function that maps each *n*-tuple (*v*\
:sub:`1`, *v*\ :sub:`2`, ... , *v*\ :sub:`n`) inhabiting the domain
type to its *i*\ th component *v*\ :sub:`i`.

.. COMMENT:  ***************************************************************** 

.. COMMENT:  OLD:
            %%%<section id="Relaxators"><title>Relaxators</title>
            %%%<para>
            %%%``
            %%%||:token:`relaxator` ::= relax :token:`closed_expression`
            %%%``
            %%%Sample :token:`relaxator`:
            %%%[[
            %%%||    relax even
            %%%]]
            %%%Restriction.
            %%%The :token:`closed_expression` of a :token:`relaxator` must have some function
            %%%type \ *T*\  ``-> Bool``.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%The type of :token:`relaxator` ``relax``\ *P*\ \ ,
            %%%where *P* has type
            %%%\ \ *T*\  ``-> Bool``, is the function
            %%%type (whose domain is a subtype) ``(``\ *T*\  ``|``\ *P*\ ``) ->``\ *T*\ \ .
            %%%The value of the :token:`relaxator` is the function that maps each
            %%%inhabitant of subtype
            %%%\ ``(``\ *T*\  ``|``\ *P*\ ``)`` to the same value %%
            %%%apart from the type information %% inhabiting supertype
            %%%*T*.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%For example, given
            %%%[[
            %%%||    type Even = (Nat | even)
            %%%]]
            %%%we have the typing
            %%%[[
            %%%||    relax even : Even -> Nat
            %%%]]
            %%%for the function that injects the even natural numbers back
            %%%into the supertype of ``Even``.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%|Metaslang| does not require the explicit use of a :token:`relaxator` to relax
            %%%an :token:`expression` from a subtype to its supertype if the
            %%%context requires the latter.
            %%%Implicit relaxation will take place when needed.
            %%%For example, in the :token:`expression` ``-1`` the :token:`nat_literal` ``1``
            %%%of type ``Nat`` is implicitly relaxed to type ``Integer`` to
            %%%accommodate the unary negation operator ``-``, which has type
            %%%\ ``Integer -> Integer``.
            %%%</para>
              %%====================================================================%%
            %%%<para>
            %%%Note the remarks about equivalence of :token:`type_restrictions` in
            %%%the corresponding section.
            %%%</para>
            %%%</section>

.. COMMENT:  ***************************************************************** 

Quotienters
-----------

.. productionlist::
  quotienter: quotient "[" `type_name` "]"

Sample :token:`quotienter`:

.. code-block:: specware

   quotient[Q]
   

Restriction. In a :token:`quotienter` ``quotient[``\ *Q* ``]``, *Q*
must be defined as a :ref:`quotient type <Type-quotients>`.

.. COMMENT: ====================================================================

The type of :token:`quotienter` ``quotient[``\ *Q*\ ``]``, where *Q* is
defined by ``type``\ *Q*\ ``=`` *T* ``/`` *q*, is the function
type  *T* ``->`` *Q*, that is, it goes from the base type to
the quotient type. The value of the :token:`quotienter` is the
function that maps each inhabitant of type *T* to the *q*-equivalence
class inhabiting *Q* of which it is a member.

.. COMMENT: ====================================================================

For example, given

.. code-block:: specware

   op congMod3 : Nat * Nat -> Bool =
     (fn (m, n) -> m rem 3 = n rem 3)
   
   type Z3 = Nat / congMod3
   

we have the typing

.. code-block:: specware

   quotient[Z3] : Nat -> Z3
   

and the function maps, for example, the number 5 to the equivalence
class {2, 5, 8, ...}, which is one of the three inhabitants of ``Z3``.

.. COMMENT:  ***************************************************************** 

Choosers
--------

.. productionlist::
  chooser: choose "[" `type_name` "]"

Sample :token:`chooser`:

.. code-block:: specware

   choose[Q]
   

Restriction. In a :token:`chooser` ``choose[`` *Q* ``]``, *Q* must be
defined as a :ref:`quotient type <Type-quotients>`.

.. COMMENT: ====================================================================

The type of :token:`chooser` ``choose[`` *Q* ``]``, where *Q*
``=`` *T*\ ``/``\ *q*, is a function type of the form *F* ``->
(`` *Q* ``->`` *R* ``)``, where *F* is the subtype of *T*
``->`` *R* consisting of the *q*-constant (explained below)
functions. Expressed more formally, *F* is the type ``{f :`` *T*
``->`` *R* ``| fa((x,y) :`` *T* ``*`` *T* ``)`` *q* ``(x,y) =>
f x = f y}``, where the :token:`simple_names` ``f``, ``x`` and
``y`` must be replaced by "fresh" :token:`simple_names` not clashing
with :token:`simple_names` already in use in *T*, *R* or *q*.

.. COMMENT: ====================================================================

The value of the :token:`chooser` is the function mapping each
*q*-constant (explained below) function *f* inhabiting type *T*
``->`` *R* to the function of type *Q* ``->`` *R* that maps
each inhabitant *C* of *Q* to *f* *x*, where *x* is any member of *C*.
Expressed symbolically, using a pseudo-function ``any`` that
arbitrarily picks any member from a nonempty set, this is the function

.. code-block:: specware

   fn f  ->  fn C -> f (any C)
   

The requirement of *q*-constancy on *f* is precisely what is needed to
make this function insensitive to the choice made by ``any``.

.. COMMENT: ====================================================================

Function *f* is *q*-constant if, for each *q*-equivalence class *C*
inhabiting *Q*, *f* *x* equals *f* *y* for any two values *x* and *y*
that are members of *C*, or *f* is undefined on all members of *C*.
(Since the result of *f* is constant across each equivalence class, it
does not matter which of its elements is selected by ``any``.) For
example -- continuing the example of the previous section -- function
``fn n -> n*n rem 3`` is ``congMod3``\ -constant; for the equivalence
class {2, 5, 8, ...}, for example, it maps each member to the same
value 1. So ``choose[Z3] (fn n -> n*n rem 3)`` maps the inhabitant {2,
5, 8, ...} of type ``Z3`` to the natural number 1.

.. COMMENT: ====================================================================

.. COMMENT:  ====================== MORE CONFUSING THAN HELPFUL (jlm/sjw) ==================================
            ** <para>
            ** The most discriminating *q*-constant functions, where *q* has type \ *T*\  ``*``\ *T*\  ``-> Bool``,
            ** are :token:`quotienters` of the form ``quotient[``\ *Q*\ \ ], where \ *Q*\  ``=``\ *T*\  ``/ q``.
            ** Since all such *Q* are isomorphic to one another (but not necessarily equal),
            ** all these :token:`quotienters` are isomorphic to one another.
            ** </para>
                 ====================== (wjs/mlj) LUFPLEH NAHT GNISUFNOC EROM ================================== 

.. COMMENT: ====================================================================

The meaning of ``choose[``\ *Q*\ ``] (fn x ->``\ *E*\ ``)``\ *A*\ is
the same as that of the :token:`let_expression` ``let quotient[``\
*Q*\ ``] x =``\ *A*\ ``in``\ *E*\ \ . Indeed, often a
:token:`quotient_pattern` offers a more convenient way of expressing
the intention of a :token:`chooser`. Note, however, the remarks on the
proof obligations for :token:`quotient_patterns`.


.. COMMENT:  ***************************************************************** 

Embedding-tests
---------------

.. productionlist::
  embedding_test: embed? `constructor`

Sample :token:`embedding_test`:

.. code-block:: specware

   embed? Cons
   

Restriction. The type of an :token:`embedding_test` ``embed?`` *C*
must be of the form *T* ``-> Bool``, where *T* is a sum type
that has a :token:`constructor` *C*.

.. COMMENT:  ================================================================= 

The value of :token:`embedding_test` ``embed?`` *C* is the predicate
that returns ``true`` if the argument value -- which, as inhabitant of
a sum type, is tagged -- has tag *C*, and otherwise ``false``. The
:token:`embedding_test` can be equivalently rewritten as

.. code-block:: specware

   fn
    | C _  ->  true
    | _    ->  false
   

where the wildcard ``_`` in the first :token:`branch` is omitted when
*C* is parameter-less.

.. COMMENT:  ================================================================= 

In plain words, ``embed?`` *C* tests whether its sum-typed argument
has been constructed with the :token:`constructor` *C*. It is an error
when *C* is not a constructor of the sum type.

.. COMMENT:  ***************************************************************** 

.. COMMENT:  *****************************************************************
            ** <section id="Selectors"><title>Selectors</title>
            ** <para>
            ** ``
            ** ||:token:`selector` ::= select :token:`constructor`
            ** ``
            ** </para>
            ** </section>
            ********************************************************************** 

Matches and Patterns
####################

.. COMMENT:   ***************************************************************** 

.. _Matches:

Matches
=======

.. productionlist::
  match: [ "|" ] `branch` { "|" `branch` }*
  branch: `pattern` [ `guard` ] -> `expression`
  guard: "|" `expression`

Sample :token:`matches`:

.. code-block:: specware

   {re = x, im = y} -> {re = x, im = -y}
   
     Empty -> true
   | Push {top = _, pop = rest} -> hasBottom? rest
   
   | Empty -> true
   | Push {top = _, pop = rest} -> hasBottom? rest
   
   | Line(z0, z1) | z0 ~= z1 -> dist(z0, z1)
   

Restriction. In a :token:`match`, given the environment, there must be
a unique type *S* to which the :token:`pattern` of each
:token:`branch` conforms, and a unique type *T* to which the
:token:`expression` of each :token:`branch` conforms, and then the
:token:`match` has type \ *S*\ ``->``\ *T*\ \ . The :token:`pattern`
of each :token:`branch` then has type *S*.

Restriction. The type of the :token:`expression` of a :token:`guard`
must be ``Bool``

.. COMMENT:  ================================================================= 

Disambiguation. If a :token:`branch` could belong to several open
:token:`matches`, it is interpreted as being a :token:`branch` of the
textually most recently introduced :token:`match`. For example,

.. code-block:: specware

   case x of
     | A -> a
     | B -> case y of
              | C -> c
     | D -> d
   

is not interpreted as suggested by the indentation, but as

.. code-block:: specware

   case x of
     | A -> a
     | B -> (case y of
               | C -> c
               | D -> d)
   

If the other interpretation is intended, the :token:`expression`
introducing the inner :token:`match` needs to be parenthesized:

.. code-block:: specware

   case x of
     | A -> a
     | B -> (case y of
               | C -> c)
     | D -> d
   

.. COMMENT:  ================================================================= 

Acceptance and return value *y*, if any, of a value *x* for a given
:token:`match` are determined as follows. If each :token:`branch` of
the :token:`match` rejects *x* (see below), the whole :token:`match`
rejects *x*, and does not return a value. Otherwise, let *B* stand for
the textually first :token:`branch` accepting *x*. Then *y* is the
return value of *x* for *B*.

.. COMMENT:  ================================================================= 

The meaning of a "guardless" :token:`branch`  *P* ``->`` *R*,
where *P* is a :token:`pattern` and *R* an :token:`expression`, is the
same as that of the :token:`branch` *P* ``| true ->`` *R* with a
:token:`guard` that always succeeds.

Acceptance and return value *y*, if any, of a value *x* for a
:token:`branch` *P* ``|`` *G* ``->`` *R* in an environment *C*
are determined as follows. If :token:`pattern` *P* rejects *x*, the
:token:`branch` rejects *x*, and does not return a value. (For
acceptance by a :token:`pattern`, see under
:ref:`Patterns <Patterns>`.)
Otherwise, let *C'* be environment
*C* extended with the acceptance
binding of :token:`pattern` *P* for
*x*.
If :token:`pattern` *P* accepts *x*, but the value of
:token:`expression` *G* in the environment
*C'* is false, the :token:`branch` also rejects
*x*, and does not return a value.
Otherwise, when the :token:`pattern` accepts *x* and the :token:`guard` succeeds,
the :token:`branch` accepts *x* and the return value
*y* is the value of
:token:`expression` *R* in the environment
*C'*.

.. COMMENT:  ================================================================= 

For example, in

.. code-block:: specware

   case z of
      | (x, true)  -> Some x
      | (_, false) -> None
   

if ``z`` has value ``(3, true)``, the first branch accepts this
value with acceptance binding ``x = 3``. The value of ``Some x`` in
the extended environment is then ``Some 3``. If ``z`` has value
``(3, false)``, the second branch accepts this value with empty
acceptance binding (empty since there are no "accepting"
:token:`local_variables` in :token:`pattern` ``(_, false)``\ ), and
the return value is ``None`` (interpreted in the original
environment).

Here is a way of achieving the same result using a :token:`guard`:

.. code-block:: specware

   case z of
      | (x, b) | b -> Some x
      | _          -> None
   

.. COMMENT:   ***************************************************************** 

.. _Patterns:

Patterns
========

.. productionlist::
  pattern: `annotated_pattern` | `tight_pattern`
  tight_pattern: `aliased_pattern` | `cons_pattern` | `embed_pattern` | 
               : `quotient_pattern` | `closed_pattern`
  closed_pattern: `variable_pattern` | `wildcard_pattern` | `literal_pattern` | `list_pattern` | 
                : `tuple_pattern` | `record_pattern` | ( `pattern` )

(As for :token:`expressions`, the distinctions :token:`tight_` and
:token:`closed_` for :token:`patterns` have no semantic significance,
but merely serve to avoid grammatical ambiguities.)

.. productionlist::
  annotated_pattern: `pattern` `type_annotation`
  aliased_pattern: `variable_pattern` as `tight_pattern`
  cons_pattern: `closed_pattern` :: `tight_pattern`
  embed_pattern: `constructor` [ `closed_pattern` ]
  quotient_pattern: quotient "[" `type_name` "]"
  variable_pattern: `local_variable`
  wildcard_pattern: _
  literal_pattern: `literal`
  list_pattern: "[" `list_pattern_body` "]"
  list_pattern_body: [ `pattern` { , `pattern` }* ]
  tuple_pattern: ( `tuple_pattern_body` )
  tuple_pattern_body: [ `pattern` , `pattern` { , `pattern` }* ]
  record_pattern: "{" `record_pattern_body` "}"
  record_pattern_body: [ `field_patterner` { , `field_patterner` }* ]
  field_patterner: `field_name` [ `equals` `pattern` ]

Sample :token:`patterns`:

.. code-block:: specware

   (i, p) : Integer * Bool
   z as {re = x, im = y}
   hd :: tail
   Push {top, pop = rest}
   embed Empty
   x
   _
   #z
   [0, x]
   (c1 as (0, _), x)
   {top, pop = rest}
   

Restriction. Like all polymorphic or type-ambiguous constructs, a
:token:`pattern` may only be used in a context where its type can be
uniquely inferred.

.. COMMENT: ====================================================================

Disambiguation. A single :token:`simple_name` used as a
:token:`pattern` is an :token:`embed_pattern` if it is a
:token:`constructor` of the type of the :token:`pattern`. Otherwise,
the :token:`simple_name` is a :token:`variable_pattern`.

.. COMMENT: ====================================================================

Restriction. Each :token:`local_variable` in a :token:`pattern` must
be a different :token:`simple_name`, disregarding any
:token:`local_variables` introduced in :token:`expressions` or
:token:`type_descriptors` contained in the :token:`pattern`. (For
example, ``Line (z, z)`` is not a lawful :token:`pattern`, since ``z``
is repeated; but ``n : {n : Nat | n<p}`` is lawful: the second
``n`` is "shielded" by the :token:`type_comprehension` in which it
occurs.)

.. COMMENT:   ================================================================= 

.. COMMENT:  OLD:
            %%%<para>
            %%%Restriction.
            %%%The :token:`closed_expression` of a :token:`quotient_pattern` must have some type
            %%%\ \ *T*\  ``*``\ *T*\  ``-> Bool``\ ;
            %%%in addition, it must be an equivalence relation, as explained
            %%%under <link
            %%%linkend="Type-quotients"><emphasis>Type-quotients</emphasis></link>.
            %%%</para>
            %%% ================================================================= %%
            %%%<para>
            %%%Restriction.
            %%%:token:`Quotient_patterns` may only be used in a :token:`definition` or
            %%%:token:`claim` if the result is insensitive to the choice of representative
            %%%from the equivalence class.
            %%%|SpecwareV| does not attempt to generate proof obligations for
            %%%establishing this.
            %%%</para>
            %%% ================================================================= %%
            %%%<para>
            %%%Restriction.
            %%%The :token:`closed_expression` of a :token:`relax_pattern` must have some function
            %%%type \ *T*\  ``-> Bool``.
            %%%</para>

.. COMMENT:   ================================================================= 

To define acceptance and acceptance binding (if any) for a value and a
:token:`pattern`, we introduce a number of auxiliary definitions.

.. COMMENT:   ================================================================= 

The *accepting* :token:`local_variables` of a :token:`pattern` *P* are
the collection of :token:`local_variables` occurring in *P*,
disregarding any :token:`local_variables` introduced in
:token:`expressions` or :token:`type_descriptors` contained in the
*P*.  For example, in :token:`pattern` ``u : {v : S | p v}``, ``u`` is
an accepting :token:`local_variable`, but ``v`` is not.  (The latter
is an accepting :token:`local_variable` of :token:`pattern` ``v : S``,
but not of the larger :token:`pattern`.)

.. COMMENT:   ================================================================= 

The *expressive descendants* of a :token:`pattern` are a finite set of
:token:`expressions` having the syntactic form of :token:`patterns`,
as determined in the following three steps (of which the order of
steps 1 and 2 is actually immaterial).

.. COMMENT:   ================================================================= 

#. From :token:`pattern` *P*, form some *tame variant* *P*\ :sub:`t`
   by replacing each :token:`field_patterner` consisting of a single
   :token:`field_name` *F* by the :token:`field_patterner` \ *F*\ ``=``\
   *F*\ and replacing each :token:`wildcard_pattern` ``_`` in *P* by a
   unique fresh :token:`simple_name`, that is, any :token:`simple_name`
   that does not already occur in the :token:`spec`, directly or
   indirectly through an import.  For example, assuming that the
   :token:`simple_name` ``v7944`` is fresh, a tame variant of::

      s0 as _ :: s1 as (Push {top, pop = rest}) :: ss

   is::

      s0 as v7944 :: s1 as (Push {top = top, pop = rest}) :: ss
   
#. Next, from *P*\ :sub:`t`, form a (tamed) *construed version*
   *P* :sub:`tc` by replacing each constituent :token:`cons_pattern` 
   *H* ``::`` *T* by the :token:`embed_pattern` ``Cons (``\ *H*\ ``,``
   *T* ``)``, where ``Cons`` denotes the :token:`constructor` of the parameterized
   type ``List``.  For the example, the construed version is::

     s0 as Cons (v7944,
                 s1 as Cons (Push {top = top, pop = rest}, ss))
   

#. Finally, from *P* :sub:`tc`, form the set *ED* :sub:`P` of
   *expressive descendants*  of *P*, where :token:`expression` *E* is an
   expressive descendant if *E* can be obtained by repeatedly replacing some constituent
   :token:`aliased_pattern`  *L* ``as`` *R* ``of`` *P*\ :sub:`tc`
   by one of the two :token:`patterns` *L* and *R* until no :token:`aliased_patterns`
   remain, and then interpreting the result as an :token:`expression`.
   For the example, the expressive descendants are the three :token:`expressions`::

     s0
     Cons (v7944, s1)
     Cons (v7944, Cons (Push {top = top, pop = rest}, ss))
   

.. COMMENT:   ================================================================= 

An *accepting binding* of a :token:`pattern` *P* for a value *x* in an
environment *C* is some binding *B* of typed values to the accepting
:token:`local_variables` of the *tame* variant *P*\ :sub:`t`, such
that the value of each expressive descendant *E* in *ED*\ :sub:`P` in
the environment *C* extended with binding *B*, is the same typed value
as *x*.

.. COMMENT:   ================================================================= 

Acceptance and acceptance binding, if any, for a value *x* and a
:token:`pattern` *P* are then determined as follows. If there is no
accepting binding of *P* for *x*, *x* is rejected. If an accepting
binding exists, the value *x* is accepted by :token:`pattern` *P*.
There is a unique binding *B* among the accepting bindings in which
the type of each assigned value is as "restricted" as possible in the
subtype-supertype hierarchy without violating well-typedness
constraints (in other words, there are no avoidable implicit
coercions). The acceptance binding is then the binding *B* *projected
on* the accepting :token:`local_variables` of *P*.

.. COMMENT:   ================================================================= 

For the example, the accepting :token:`local_variables` of *P* \
:sub:`t` are the six :token:`local_variables` ``s0``, ``s1``, ``ss``,
``rest`` and ``v7944``.  In general, they are the accepting
:token:`local_variables` of the original :token:`pattern` together
with any fresh :token:`simple_names` used for taming.  Let the value
*x* being matched against the pattern be::

   Cons (Empty, Cons (Push {top = 200, pop = Empty}, Nil))
   
Under the accepting binding::

   s0 = Cons (Empty, Cons (Push {top = 200, pop = Empty}, Nil))
   s1 = Cons (Push {top = 200, pop = Empty}, Nil)
   ss = Nil
   top = 200
   rest = Empty
   v7944 = Empty
   

the value of each *E* in *ED*\ :sub:`P` amounts to the value *x*.
Therefore, *x* is accepted by the original :token:`pattern`, with
acceptance binding::

   s0 = Cons (Empty, Cons (Push {top = 200, pop = Empty}, Nil))
   s1 = Cons (Push {top = 200, pop = Empty}, Nil)
   ss = Nil
   top = 200
   rest = Empty
   

obtained by "forgetting" the fresh :token:`simple_name` ``v7944``.

.. COMMENT:  *****************************************************************
            TODO:
            More type-correctness restrictions.
            Unification, monomorphicity restriction.
            Unspecified op types.
            Constructive
            Test constructs used
            At Semantics: transformational semantics.
            Relationship choose & quotient?
            **********************************************************************
            Wishes for further syntax changes:
            (Maybe) Allow ``type op`` for infix parameterized types.
            ********************************************************************** 

