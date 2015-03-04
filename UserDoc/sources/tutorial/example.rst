

=======
Example
=======

This chapter presents a step-by-step example of a small application
developed with |Specware|. Despite its small size, the example
illustrates the general methodology to develop software with
|Specware|. Furthermore, the description of the example includes
concrete explanations to run the example through |Specware|, thus
serving as a usage tutorial. The code for this example may be found in
the ``Examples\Matching\`` (Windows) or ``Examples/Matching/`` (Linux)
folder in your installation directory (e.g., ``C:\Program
Files\Specware\`` or ``/usr/local/specware``).

The Problem
###########

The problem solved by this simple application is the following. A
message is given, consisting of a sequence of characters, some of
which are "obscured", i.e., it may look something like:

.. code-block:: specware

   **V*ALN**EC*E*S
   

Then, a list of words is given, where a word is a sequence of
characters, e.g.:

.. code-block:: specware

   CERAMIC
   CHESS
   DECREE
   FOOTMAN
   INLET
   MOLOCH
   OCELOT
   PROFUSE
   RESIDE
   REVEAL
   SECRET
   SODIUM
   SPECIES
   VESTIGE
   WALNUT
   YOGURT
   

Even though the above list is alphabetically sorted, the list of words
can be given in any order.

The application must find which words of the list may occur somewhere
in the message, where an obscured character in the message may match
any character in a word, while a non-obscured character must be
matched exactly. The application must also show the offset in the
message at which the possible occurrence is found; if there is more
than one offset, the smallest one should be returned. So, the output
for the example message and word list above is the following:

.. code-block:: specware

   10 CHESS
    8 DECREE
    0 REVEAL
    8 SECRET
    7 SPECIES
    3 WALNUT
   

Again, even though the list of words and numbers is alphabetically
ordered, the application can produce it in any order.

Specification
#############

Construction
============

We specify the application in a bottom-up fashion. We build specs for
the concepts involved in the application, starting with the simplest
ones up to the spec for the application.

|Metaslang| provides strings of characters among the built-in types,
ops, and axioms. We could define messages and words as strings
satisfying certain properties, e.g., that the character ``*`` can
appear in messages but not in words, etc.

However, it is generally better to specify things as abstractly as
possible. It is clear that the problem as stated above does not depend
on obscured characters being represented as ``*`` and on non-obscured
characters being uppercase letters only, or letters and numbers, or
other. The abstract notion is that there are characters that form
words, and messages are made of those characters but some characters
may be obscured.

So, we start with a spec for symbols (i.e., characters):

.. code-block:: specware

   Symbols = spec
     type Symbol
   end-spec
   

This is a very simple spec: it just consists of one type. This is
perfectly adequate because the application treats symbols atomically:
it only compares them for equality (which is built-in in |Metaslang|
for every type). Any further constraint on symbols would just make the
spec unnecessarily less general.

The text above is |Metaslang| syntax: it not only introduces a spec
consisting of the type ``Symbol``, but also assigns a name to it,
``Symbols``. This spec can thus be referred to by its name, as shown
shortly. The exact way in which the text above is supplied to
|Specware| is explained later.

Now that we have the concept of symbols, we can introduce the concept
of word as a sequence of symbols. |Metaslang| provides lists, built-
in. The polymorphic type ``List a`` is used to define words:

.. code-block:: specware

   Words = spec
     import Symbols
     type Word = List Symbol
   end-spec
   

The name of the spec is ``Words``. The spec imports ``Symbols``
defined above, and extends it with a new type ``Word``, defined to
be ``List Symbol``. This type is obtained as an instantiation of
``List a`` by replacing the type parameter ``a`` with ``Symbol``.

A message is a sequence of symbols some of which may be obscured. This
can be specified by lists whose elements are either symbols or a
special extra value that stands for an "obscured symbol" (the "\
``*``\ " in the problem description given earlier).

|Metaslang| provides, built-in, a polymorphic type ``Option a`` that
adds an extra element to a type. More precisely, it is defined as
``type Option a = | Some a | None``. The type ``Option a`` is defined
as a coproduct of type ``a`` tagged by ``Some`` and the singleton type
consisting of the constant ``None``.

So, we can define messages as follows:

.. code-block:: specware

   Messages = spec
     import Symbols
     type Message = List (Option Symbol)
   end-spec
   

At this point, we can define the notion of symbol matching: a symbol
must be matched by the exact same symbol, while an obscured symbol may
be matched by any symbol. This is captured by the following spec:

.. code-block:: specware

   SymbolMatching = spec
   import Symbols
   
   op symb_matches?(s: Symbol, os: Option Symbol): Bool
     = case os of
         | Some s1 -> s = s1
         | None    -> true
   end-spec
   

The spec imports ``Symbols`` and extends it with an op
``symb_matches?`` that returns a boolean from a pair whose first
component is a symbol and the second component is a possibly obscured
symbol. This op can be viewed as a binary predicate. The op is defined
by pattern matching on the second argument, in a straightforward way.
Note that ``s = s1`` is a term of type ``Bool``.

The definition is constructive in the sense that code can be
eventually generated directly, without any need to refine it. This is
one of those cases where the simplest and most abstract definition of
an op happens to be directly executable.

Having the notion of symbol matching, now we define the notion of word
matching, i.e., when a word matches a message. We could define an op
(predicate) of type ``Word * Message -> Bool``. However, since
the application involves offsets for matching words, it is better to
declare the op to have type ``Word * Message * Nat -> Bool``: the
predicate is true if the given word matches the given message at the
given position. Here is the spec:

.. code-block:: specware

   WordMatching = spec
   
   import Words
   import Messages
   import SymbolMatching
   
   op word_matches_at?(wrd: Word, msg: Message, pos: Nat)
        : Bool =
     pos + length wrd <= length msg &&
     (fa(i:Nat) i < length wrd
        => symb_matches?(wrd@i, msg@(pos+i)))
   
   end-spec
   

First, the spec imports the specs for words, messages, and symbol
matching. Then it introduces the op ``word_matches_at?``, with the
type explained above. Its definition says that the predicate holds on
a triple ``(wrd,msg,pos)`` if and only if two conditions are
satisfied:

#. ``msg`` is long enough to possibly contain the whole ``wrd`` at
   position ``pos``;

#. every symbol of ``wrd`` at position ``i`` matches the corresponding,
   possibly obscured symbol in ``msg`` at position ``pos + i``.

Note the use of ``symb_matches?`` previously defined. The ops
``length`` and ``@`` are built-in, polymorphic ops over lists: the
former returns the length of a list, while the latter returns the n-th
element of a list (n is numbered starting from 0).

Unlike ``symb_matches?`` above, the definition of ``word_matches_at?``
is not executable. This means that it must be eventually refined. An
executable definition of this op involves some kind of loop through
the message: so, it would not be as simple and abstract as it is now.
The general rule is that, at the specification level, things should be
expressed as simply, clearly, and declaratively as possible.

Having all the above concepts in hand, we are ready to define how a
message and a list of words are processed by the application to
produce a list of matches. As explained in the problem description
above, a match is not only a word, but also the (least) position in
the message at which the match occurs. So, it is appropriate to define
the concept of a match, as a pair consisting of a word and a position
(i.e., a natural number):

.. code-block:: specware

   Matches = spec
     import Words
     type Match = {word : Word, position : Nat}
   end-spec
   

The type ``Match`` is defined to be a record with two components,
named ``word`` and ``position``. A record is like a cartesian
product, but the components have user-chosen names.

Finally, the spec for the whole application is the following:

.. code-block:: specware

   FindMatches = spec
   
   import WordMatching
   import Matches
   
   op find_matches : Message * List Word -> List Match
   axiom match_finding is
     fa(msg,wrds,mtch)
       mtch in? find_matches(msg,wrds)
        <=>
       mtch.word in? wrds
        && word_matches_at?(mtch.word,msg,mtch.position)
        && (fa(pos) word_matches_at?(mtch.word,msg,pos)
              => pos >= mtch.position)
   
   end-spec
   

The spec imports ``WordMatching`` and ``Matches``, and declares an
op ``find_matches`` that, given a message and a list of words, returns
a list of matches. This op captures the processing performed by the
application. The axiom (whose name is ``match_finding``) states the
required properties. The built-in polymorphic op ``member`` is a
predicate that says whether an element belongs to a list or not. So,
the required property for ``find_matches`` is the following: given a
message ``msg`` and a list of words ``wrds``, a match ``mtch``
belongs to the result of ``find_words`` if and only if:

#. the word of the match is in ``wrds``, i.e., the word must have been
   given as input;

#. the word can be matched with ``msg`` at the position indicated by the
   match;

#. the position of the match is the least position where the word
   matches.

Note how the specification of this word matching application is simple
and abstract. No commitments have been made to particular data
structures or algorithms. These commitments are made during the
refinement process. Note also that the op ``find_matches`` is not
completely defined by the axiom: the order of the resulting matches is
not specified (the axiom only says what the members of the resulting
list are, but not their order). The axiom does not prohibit duplicate
elements in the output list; a suitable conjunct could be added to
enforce uniqueness, if desired. This under-specification is consistent
with the informal problem description given above. Of course, it is
possible to change the axiom to require a particular order (e.g., the
same as in the input list), if desired.

  

.. COMMENT:  construction 

Processing by |Specware|
========================

How do we actually enter the above text into |Specware| and how do we
have |Specware| process it?

The current version of |Specware| works more or less like a compiler:
it processes one or more files producing results. The files define
specs, morphisms, etc. The results include error messages if something
is wrong (e.g., type errors in specs), and possibly the generation of
other files (e.g., containing code generated by |Specware|).

The files processed by |Specware| are text files with extension
``.sw`` (the "s" and "w" come from the first and fifth letter of
"|Specware|"). A ``.sw`` file contains a sequence of definitions of
specs, morphisms, etc.

For the word matching application constructed above, it is sensible to
put all the specs above inside a file ``MatchingSpecs.sw``:

.. code-block:: specware

   Symbols = spec
     type Symbols
   end-spec
   
   ...
   
   FindMatches = spec
    ...
   end-spec
   

Unlike a traditional compiler, the interaction with |Specware| is
within a shell. When |Specware| is started, the shell is available for
interaction with |Specware| (|Specware| is part of the Lisp image). In
the shell, the user can move to any desired directory of the file
system by means of the ``cd`` command, followed by the name of the
directory, e.g., ``cd c:\mydir`` (Windows) and ``cd ~/mydir`` (Linux).
Usually, the ``.sw`` files that form an application are put inside a
directory, and from the shell the user moves to that directory.

In order to have |Specware| process a spec (or morphism, etc.)
contained in a ``.sw`` file in the current directory, the user
provides the following command in the shell:

.. code-block:: specware

   proc <filename>#<specname>
   

The ``<filename>`` portion of the argument string is a place
holder for the file name (without the <".sw"> extension); the
``<specname>`` portion is a place holder for the spec (or
morphism, etc.) name as it appears inside the file.

The effect of the above command is to have |Specware| process the
indicated spec (or morphism, etc.) in the indicated file, recursively
processing other specs, morphisms, etc. that are referenced by the
indicated spec.

To have |Specware| process the spec of the word matching application,
the command is:

.. code-block:: specware

   proc MatchingSpecs#FindMatches
   

This has the effect of processing the spec named ``FindMatches`` in
file ``MatchingSpecs.sw``. Since this spec imports specs
``WordMatching`` and ``Matches``, these are processed first, and so
are the specs imported by them, recursively. Thus, all the specs in
``MatchingSpecs.sw`` are processed. ``FindMatches`` is the top-level
spec in the file.

|Specware| finds the specs ``WordMatching`` and ``Matches``,
imported by ``FindMatches``, because they are contained in the same
file. As it will be explained shortly, it is possible to refer from
one file to specs defined in different files.

  

.. COMMENT:  specware processing 

  

.. COMMENT:  specification 

Refinement
##########

Construction
============

We now refine the application specified above in order to obtain a
running program that implements the specified functionality. We do
that by defining the specs and morphisms below inside a file
``MatchingRefinements.sw``, in the same directory as
``MatchingSpecs.sw``.

In order to obtain an executable program, we need to choose a concrete
representation for the symbols composing words and messages. For
example, we can choose uppercase characters:

.. code-block:: specware

   Symbols = spec
     type Symbol = (Char | isUpperCase)
   end-spec
   

The built-in type ``Char`` is the type for characters. The built-in op
``isUpperCase`` is a predicate on characters that says whether a
character is an uppercase letter or not. The subtype construct 
"\ ``|``\ " is used to define the type ``Symbol`` as a subtype of
``Char``.

Note that the above spec has the same name (``Symbols``) as its
corresponding abstract spec. This is allowed and it is a feature of
|Specware|: ``.sw`` files define separate name spaces. The file
``MatchingSpecs.sw`` creates a name space, and the file
``MatchingRefinements.sw`` creates a separate name space. The full
name of the spec ``Symbols`` in ``MatchingSpecs.sw`` is
``MatchingSpecs#Symbols``, while the full name of the spec
``Symbols`` in ``MatchingRefinements.sw`` is
``MatchingRefinements#Symbols``. Indeed, when |Specware| is invoked
to process a spec (or morphism, etc.), the full name is supplied, as
in ``proc MatchingSpecs#FindMatches``.

The fact that spec ``MatchingRefinements#Symbols`` is a refinement of
``MatchingSpecs#Symbols`` is expressed by the following morphism:

.. code-block:: specware

   Symbols_Ref = morphism MatchingSpecs#Symbols ->
                          MatchingRefinements#Symbols {}
   

This text defines a morphism called ``Symbols_Ref``, with domain
``MatchingSpecs#Symbols`` and codomain ``MatchingRefinements#Symbols``
and where the type ``Symbol`` in ``MatchingSpecs#Symbols`` is mapped
to the type ``Symbol`` in ``MatchingRefinements#Symbols``.

The specs ``Words``, ``Messages``, and ``SymbolMatching`` (in
``MatchingSpecs.sw``) need not be refined, because they constructively
define their types and ops. But the op ``word_matches_at?`` in
``WordMatching`` needs to be refined. We do that by constructing a
spec that imports the same specs imported by ``WordMatching`` and that
defines op ``word_matches_at?`` in an executable way:

.. code-block:: specware

   WordMatching0 = spec
   
   import MatchingSpecs#Words
   import MatchingSpecs#Messages
   import MatchingSpecs#SymbolMatching
   
   op word_matches_aux?(wrd: Word, msg: Message
                          | length wrd <= length msg)
        : Bool =
     case wrd of [] -> true
               | wsym::wrd1 ->
                 let msym::msg1 = msg in
                 if symb_matches?(wsym,msym)
                   then word_matches_aux?(wrd1,msg1)
                   else false
   
   op word_matches_at?(wrd: Word, msg: Message, pos: Nat)
        : Bool =
     if pos + length wrd > length msg
       then false
       else word_matches_aux?(wrd, removePrefix(msg, pos))
   
   end-spec
   

Since the imported specs are not in the file
``MatchingRefinements.sw``, their full names are used after
``import``.

The definition of ``word_matches_at?`` makes use of an auxiliary op
``word_matches_aux?``, which takes as input a word and a message
such that the length of the word is not greater than that of the
message. This constraint is expressed as a subtype of the cartesian
product ``Word * Message``. Op ``word_matches_aux?`` returns a
boolean if the word matches the message, at the start of the message.
It is defined recursively, by pattern matching on the word. Note the
use of ``let`` to decompose the msg into the initial symbol and the
rest. This is always possible because of the subtype constraint on the
word and the message. So, ``word_matches_at?`` simply calls
``word_matches_aux?`` with the word and the tail of the message
obtained by eliminating the first ``pos`` symbols, by means of the
built-in op ``nthTail`` over lists.

The fact that ``WordMatching0`` is a refinement of
``MatchingSpecs#WordMatching`` is expressed by the following morphism:

.. code-block:: specware

   WordMatching_Ref0 = morphism MatchingSpecs#WordMatching ->
                                WordMatching0 {}
   

The refinement for word matching can be composed with the refinement
for symbols constructed earlier. This is achieved by means of
|Specware|'s substitution operator:

.. code-block:: specware

   WordMatching = WordMatching0[Symbols_Ref]
   

The resulting spec is like ``WordMatching0``, but in addition the
type ``Symbol`` is defined to consist of uppercase characters.

The fact that ``MatchingRefinements#WordMatching`` is a refinement of
``MatchingSpecs#WordMatching`` is expressed by the following morphism:

.. code-block:: specware

   WordMatching_Ref =
      morphism MatchingSpecs#WordMatching ->
               MatchingRefinements#WordMatching {}
   

Now we proceed to refine op ``find_matches``. We do that in two
steps, analogously to word matching above. First, we build a spec
``FindMatches0`` that imports the same specs imported by
``MatchingSpecs#FindMatches`` and that defines op ``find_matches`` in
an executable way:

.. code-block:: specware

   FindMatches0 = spec
   
   import MatchingSpecs#WordMatching
   import MatchingSpecs#Matches
   
   op find_matches_aux(msg: Message, wrd: Word, pos: Nat)
        : Option Nat =
     if pos + length wrd < length msg
       then None
       else if word_matches_at?(wrd,msg,pos)
              then Some pos
              else find_matches_aux(msg, wrd, pos + 1)
   
   op find_matches(msg: Message, wrds: List Word)
        : List Match =
     foldl (fn(mtchs,wrd) ->
              case find_matches_aux(msg,wrd,0)
                of Some pos ->
                   {word = wrd, position = pos} :: mtchs
                 | None -> mtchs)
       []  
       wrds
   
   end-spec
   

Op ``find_matches`` makes use of the auxiliary op
``find_matches_aux``, which takes as input a message ``msg``, a
word ``wrd``, and a position ``pos``. It returns either a natural
number (a position where the match starts) or ``None`` if there is no
match. Op ``find_matches_aux`` first checks if ``msg`` is long enough
to possibly contain a match for ``wrd`` starting at ``pos``. If that
is not the case, ``None`` is returned. Otherwise, ``word_matches_at?``
is called: if it returns ``true``, then the position ``pos`` is
returned (wrapped by ``Some``). Otherwise, ``find_matches_aux`` is
recursively called, incrementing the position by 1. So, when
``find_matches_aux`` is called with 0 as its third argument, it
iterates through the message to find the first match, if any. The
position of the first match is returned, otherwise ``None``.

The op ``find_matches`` iterates through the words of the list
constructing a list of matches. The iteration is performed by means of
the built-in op ``foldl`` for lists. For each word,
``find_matches_aux`` is called, with 0 as its third argument. Then, a
pattern matching on the result is done: if the result is a position, a
match is added to the output list; otherwise, the list is left
unmodified.

The following morphism expresses that ``FindMatches0`` is a refinement
of ``MatchingSpecs#FindMatches``:

.. code-block:: specware

   FindMatches_Ref0 = morphism MatchingSpecs#FindMatches ->
                               FindMatches0 {}
   

This refinement for ``MatchingSpecs#FindMatches`` can be composed with
the one for ``MatchingSpecs#WordMatching`` built earlier. The
composition is analogous to the one for
``MatchingSpecs#WordMatching``:

.. code-block:: specware

   FindMatches = FindMatches0[WordMatching_Ref]
   

The resulting spec includes the refinement for op ``find_matches`` as
well as the refinement for op ``word_matches_at?`` and for symbols.

The fact that ``MatchingRefinements#FindMatches`` is a refinement of
``MatchingSpecs#FindMatches`` is expressed by the following morphism:

.. code-block:: specware

   FindMatches_Ref =
     morphism MatchingSpecs#FindMatches ->
              MatchingRefinements#FindMatches {}
   

All the specs and morphisms of the file ``MatchingRefinements.sw`` can
be processed by means of the following command:

.. code-block:: specware

   proc MatchingRefinements#FindMatches_Ref
   

  

.. COMMENT:  construction 

Proof Obligations
=================

In general, a morphism has proof obligations associated to it: all the
axioms in the source spec must be mapped to theorems in the target
spec. These proof obligations are expressed in the form of a spec
obtained by extending the target spec of the morphism with the axioms
of the source spec (translated along the morphism) as conjectures. The
user can then attempt to prove these conjectures using theorem provers
linked to |Specware|.

Also specs have proof obligations associated to them. Some are part of
typechecking, e.g., if an expression of a type ``T`` is used as an
argument to a function whose domain is a subtype ``T|p`` of ``T``,
the expression must satisfy ``p``, in the context in which the
application occurs. Others arise from definitions via ``def``: the
equation must be uniquely define the op. The proof obligations
associated to a spec ensure that the spec satisfied certain expected
well-formedness properties, which is useful to validate the spec.

We collect the proof obligations of the specs and morphisms defined
above in a file ``MatchingObligations.sw``, in the same directory as
``MatchingSpecs.sw`` and ``MatchingRefinements.sw``. The file contains
the following definitions:

.. code-block:: specware

   %%% obligations from MatchingSpecs.sw:
   
   SymbolMatching_Oblig = 
     obligations MatchingSpecs#SymbolMatching
   
   WordMatching_Oblig =
     obligations MatchingSpecs#WordMatching
   
   %%% obligations from MatchingRefinements.sw:
   
   WordMatching0_Oblig =
     obligations MatchingRefinements#WordMatching0
   
   WordMatching_Ref0_Oblig =
     obligations MatchingRefinements#WordMatching_Ref0
   
   FindMatches0_Oblig =
     obligations MatchingRefinements#FindMatches0
   
   FindMatches_Ref0_Oblig =
     obligations MatchingRefinements#FindMatches_Ref0
   

``SymbolMatching_Oblig`` is a spec that expresses the proof
obligations associated to the spec ``SymbolMatching`` as conjectures.
Analogously for ``WordMatching_Oblig``, ``WordMatching0_Oblig``,
and ``FindMatches0_Oblig``. ``WordMatching_Ref0_Oblig`` and
``FindMatches_Ref0_Oblig`` are specs that express the proof
obligations of the associated morphisms as conjectures. |Specware|
provides the capability to display (i.e., print) any spec, morphism,
etc., via the ``show`` command. This command can be used to see the
proof obligations associated to the specs and morphisms, by displaying
the specs expressing such obligations: the conjectures are the
obligations.

Note that not all specs and morphisms from ``MatchingSpecs.sw`` and
``MatchingRefinements.sw`` are listed in ``MatchingObligations``.
Those that are not listed have really no proof obligations associated
to them. For example, inspection (via ``show``) of ``obligations
MatchingSpecs#Symbols`` would reveal no conjectures because the spec
is very simple (it just declared an abstract type). As another
example, the spec ``MatchingRefinements#WordMatching`` is built by
substituting ``MatchingSpecs#Symbols`` with
``MatchingRefinements#Symbols`` in ``WordMatching0``: thus, the
validity of the morphism ``WordMatching_Ref`` (i.e., that all axioms
in the source are theorems in the target) follows immediately from the
validity of the morphism ``WordMatching_Ref0``.

The proof obligations associated to the spec ``SymbolMatching`` can be
displayed by using the following command:

.. code-block:: specware

   show MatchingObligations#SymbolMatching_Oblig
   

The spec only contains one conjecture, arising from the typechecking
of the ``case`` expression used in the definition of
``symb_matches?``, namely that the branches cover all possible
cases, which is very easy to prove.

The spec ``MatchingSpecs#WordMatching`` has three proof obligations,
all arising from subtypes, e.g., that ``pos + i < length msg`` in the
context that (i.e., under the assumption that) ``pos + length wrd <=
length msg`` and ``i < length wrd``.

The morphism ``FindMatches_Ref0`` contains the
"main"  proof
obligation of the overall refinement, namely that the definitio of
``find_matches`` in ``MatchingRefinements#FindMatches0`` satisfies the axiom
in ``MatchingSpecs#FindMatches``.

.. TODO Add more detail here:

|Specware| provides the capability to invoke external theorem provers
in order to attempt proofs of conjectures. Currently, the only
available prover is Isabelle/HOL; more provers may be added in the
future.  The ``gen-obligs`` Specware shell command is used to create
the Isabelle/HOL theory file corresponding to a Specware unit (spec or
morphism).  Then, one uses Isabelle/HOL to complete the proof.  Proofs
for Isabelle/HOL can be inserted into Specware files using "proof Isa"
pragmas. See ``SpecwareIsabelleInterface.pdf`` for more information.


.. Concretely, this is carried
.. out by creating proof objects. Each proof object is associated with a
.. certain conjecture in a certain spec; it also indicates the prover to
.. use and some directives on how to perform the proof. Processing of the
.. proof object invokes the indicated prover with the given directives.

.. For example, the user can attempt to discharge the proof obligation
.. for ``MatchingSpecs#SymbolMatching`` by writing the following command
.. in a file named ``MatchingProofs.sw``, located in the same directory
.. as ``MatchingObligations.sw``:

.. .. code-block:: specware

..    p1A = prove symb_matches?_Obligation_exhaustive in
..          MatchingObligations#SymbolMatching_Oblig
   

.. At the shell, the user can issue this command to attempt the proof:

.. .. code-block:: specware

..    proc MatchingProofs#p1
   

.. The obligation is translated to the Snark theorem prover and
.. automatically proven based primarily on the knowledge of |Specware|'s
.. ``Option`` type that we automatically send to Snark.

 

.. COMMENT:  proof obligations 

Alternatives
============

The refinement for the word matching application developed above is
certainly not the only one possible.

For example, we could have refined symbols differently. We could have
refined them to be all letters (uppercase or lowercase) and numbers,
or to be natural numbers. It is worth noting that the refinement for
symbols is encapsulated in spec ``MatchingRefinements#Symbols``. If
we want to change the refinement for symbols, we just need to change
that spec, while the other specs remain unaltered.

As another example, we could have chosen a more efficient refinement
for op ``find_matches``, using some fast substring search algorithm.
In particular, while we have refined op ``word_matches_at?`` first,
and then composed its refinement with one for ``find_matches``, we
could have refined ``find_matches`` "directly", without using
``word_matches_at?``, so that it would have been unnecessary to
refine ``word_matches_at?``.

The latter example illustrates an important principle concerning
refinement. In general, it is not necessary to refine all ops present
in a spec. Only the ops that are meant to be used by an external
program need to be refined to be executable, and in turn the ops that
are used inside their executable definitions. Other ops serve only an
auxiliary role in specifying abstractly the ops that are meant to be
eventually refined.

Currently, |Specware| provides no support to indicate explicitly which
ops are meant to be "exported" by a spec. In future versions of the
system, some functionality like this may be included.

  

.. COMMENT:  alternatives 

  

.. COMMENT:  refinement 

Code Generation and Testing
###########################

Code Generation
===============

Now that our simple word matching application has been refined to be
executable, we can generate code from it. This is concretely achieved
by creating a (Lisp) program from a spec, indicating a file name where
the code is deposited as a side effect. The following command is given
in the shell:

.. code-block:: specware

   gen-lisp <specname> <targetfilename>
   

The above command first processes the named spec and then generates
Lisp code from it, writing the code into the indicated file. The file
is created if it does not exist; if it exists, it is overwritten.

For instance, we can generate Lisp code for the word matching
application by means of the following command:

.. code-block:: specware

   gen-lisp MatchingRefinements#FindMatches find-matches
   

Note that if the ``.lisp`` suffix is omitted, |Specware| adds it to
the file name.

After we generate the code, we can then try to run it by calling the
Lisp function produced from op ``find_matches``. Since messages and
words are represented as lists of characters (plus ``None`` for
messages), it would be slightly inconvenient to enter and read lists
of characters. It would be better to enter strings with letters and
``*``\ 's, as shown in the informal problem description at the
beginning of this chapter.

In order to do that, we define translations between strings and
messages and words, and we wrap ``find_matches`` in order to translate
from and to strings. We do that inside a spec called ``Test`` in a
file ``MatchingTest.sw`` in the same directory as the other ``.sw``
files:

.. code-block:: specware

   Test = spec
   
   import MatchingRefinements#FindMatches
   
   op word_char?(ch: Char): Bool = isUpperCase ch
   
   op msg_char?(ch: Char): Bool = isUpperCase ch || ch = #*
   
   type WordString = (String | forall? word_char?)
   
   type MessageString = (String | forall? msg_char?)
   
   op word2string(wrd: Word): WordString = implode wrd
   
   op string2word(wstr: WordString): Word = explode wstr
   
   op message2string(msg: Message): MessageString =
     implode(map (fn Some ch -> ch | None -> #*) msg)
   
   op string2message(mstr: MessageString): Message =
     map (fn ch -> if ch = #* then None else Some ch)
       (explode mstr)
   
   type MatchString = {word : WordString, position : Nat}
   
   op match2string(mtch: Match): MatchString =
     {word = word2string mtch.word, position = mtch.position}
   
   op test_find_matches(mstr: MessageString, wstrs: List WordString)
        : List MatchString =
     map match2string
       (find_matches(string2message mstr, map string2word wstrs))
   
   def implode l = foldl (fn (s,c) -> s ^ show c) "" l
   def explode s =
     if s = "" then []
       else s@0 :: explode(subFromTo(s,1,length s))
   
   end-spec
   

Since the translation is not defined on all strings, we introduce two
subtypes of the built-in type ``String``: the type ``WordString``
consists of all strings whose characters are uppercase letters; the
type ``MessageString`` consists of all strings whose characters are
uppercase letters or ``*``. The built-in op ``all`` over strings is
used to define the subtypes, using the ops (predicates) ``word_char?``
and ``msg_char?``.

The op ``word2string`` translates a word to a word string, by means of
the built-in op ``implode``. The op ``string2word`` performs the
opposite translation, using the built-in op ``explode``. The ops
``message2string`` and ``string2message`` translate between messages
and string messages. Besides the use of ``implode`` and ``explode``,
they need to map ``Some ch`` from/to ``ch`` (where ``ch`` is an
uppercase letter) and ``None`` from/to ``*``.

Since ``find_matches`` returns a match, i.e., a pair consisting of a
word and a position, we define a type ``MatchString`` consisting of a
word string and a position, together with an op ``match2string`` that
translates from a match to a string match.

Finally, we define an op ``test_find_matches`` to take a message
string and a list of word strings as input, and to return a list of
string matches as output. The message string and word strings are
first translated to a message and list of words, then ``find_matches``
is called, and then the resulting matches are translated to string
matches. Note that the op ``message2string`` is never used. In fact,
it could have been omitted.

Now, instead of generating code from
``MatchingRefinements#FindMatches``, we generate code from
``MatchingTest#Test``:

.. code-block:: specware

   gen-lisp MatchingTest#Test find-matches-test.lisp
   

 

.. COMMENT:  code gen 

Testing
=======

In order to test the generated Lisp code, we need to load the
generated Lisp file into a Lisp environment (provided with
|Specware|). We do that by means of the following command (this and
all the following commands must be given in the Lisp environment, not
the |Specware| shell):

.. code-block:: common-lisp

   ld find-matches-test
   

In Lisp, entities like functions, constants, etc. are defined inside
packages. When |Specware| generates code, it puts it inside a package
named ``sw-user``. This can be seen from the package declaration at
the beginning of file ``find-matches-test.lisp`` (note that Lisp is
case-insensitive).

So, in order to call the functions defined in that file (after it has
been loaded), it is necessary either to prepend the package name to
them, or to move to that package and then call them without package
qualification. To follow the first approach, we would write 
``L:(sw-user::test_find_matches-2 <arg1> <\arg2>)`` to call the
function. (The
"\ ``-2``\ "  appended to
the function name is for the two-argument version of the Lisp function; see
the Section on Arity and Currying Normalization in the User Manual.
Alternatively, we can supply a single argument by consing ``<arg1>`` and
``<arg2>``, thus: 
``(sw-user::test_find_matches (cons <arg1> <arg2>))``.)

To follow the second approach, we would first change package by means
of the Lisp command ``pa sw-user``, and then we can just write
``(test_find_matches-2 <arg1> <arg2>)`` to call the
function.

In order to test the program on the example input and output given at
the beginning of the chapter, we proceed as follows. First, we define
a variable containing the message:

.. code-block:: common-lisp

   (setq msg "**V*ALN**EC*E*S")
   

Then we define a variable containing the list of words:

.. code-block:: common-lisp

   (setq words '("CERAMIC" "CHESS" "DECREE" "FOOTMAN"
                 "INLET" "MOLOCH" "OCELOT" "PROFUSE"
                 "RESIDE" "REVEAL" "SECRET" "SODIUM"
                 "SPECIES" "VESTIGE" "WALNUT" "YOGURT"))
   

Finally, we call (assuming to be in package ``sw-user``):

.. code-block:: common-lisp

   (test_find_matches-2 msg words)
   

The following result is then displayed:

.. code-block:: common-lisp

   ((3 . "WALNUT") (7 . "SPECIES") (8 . "SECRET")
    (0 . "REVEAL") (8 . "DECREE") (10 . "CHESS"))
   

The result is a list of pairs, each of which represents a match.

  

.. COMMENT:  testing 

  

.. COMMENT:  code gen and testing 

