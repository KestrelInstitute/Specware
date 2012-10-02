This directory contains a proof checker for the Metaslang logic, written in
Metaslang. The Metaslang logic is formally defined in the document "The Logic
of Metaslang", by Alessandro Coglio, available at Specware4/DevDoc/logic.pdf.
Read that document first and refer to it while reading the .sw files in this
directory. The document is referred to as "LD" (for "Logic Document") in the
comments in the files.

External code that uses the proof checker should only import the top-level
spec Spec. All the other specs in this directory are auxiliary and should not
be directly referenced by external code. This restriction is meant to isolate
external code from certain changes in the proof checker, e.g. if a spec
imported by spec Spec were renamed. In other words, spec Spec is public, while
the other specs in this directory are private (to the proof checker).

External code that imports spec Spec should directly reference only some of
the types and ops available in spec Spec (i.e. introduced in the specs that
are directly or indirectly imported by spec Spec), but not others. The reason
is again to isolate external code from certain internal changes in the proof
checker. The types and ops that should not be directly referenced are private
(to the proof checker), while the other types and ops are public.

Whether a type or op is private or public is indicated by comments in the
specs in this directory. If a spec starts with the comment "% API public all",
then all the types and ops declared there are public. If a spec starts with
the comment "% API private all", then all the types and ops declared there are
private. If a spec starts with the comment "% API public default", then each
type or op declared there is public by default, unless it is accompanied by
the local comment "% API private". If a spec starts with the comment "% API
private default", then each type or op declared there is private by default,
unless it is accompanied by the local comment "% API public".

Besides types and ops, external code could also reference constructors. From
the user's point of view, a constructor works very much like an op. The
convention is that, as expected, a constructor is public iff its associated
sum type is public. This is why the previous paragraph only explicitly
mentions types and ops.

Spec Spec and the public types and ops available there constitute the API for
the proof checker. Currently Specware has no mechanisms to express and enforce
adherence to this API, but a well-intentioned user should find it easy to
adhere to this API.

None of the argument types of the public ops of the proof checker are
subtypes. If a public op had an argument type that is a subtype (e.g. a
non-empty finite sequence of expressions) then Specware's type-checking alone
does not guarantee that external code never calls that op with a value of the
supertype that does not belong to the subtype as argument (e.g. the empty
sequence of expressions); proof obligations need to be discharged to guarantee
that. However, users often do not discharge proof obligations. Thus, avoiding
subtypes for arguments of public ops makes the proof checker more robust,
forcing it to deal with values that would be outside the subtypes that would
otherwise be used, as opposed to the unpredictable behavior resulting from
violating a subtype.

All the types and ops that comprise the proof checker have the qualifier
MetaslangProofChecker (see spec Spec). This should avoid any conflicts with
types and ops in external code, which would presumably not have such a
qualifier.

Some ops in spec Spec are not executable. In order to run the proof checker
from external code that imports spec Spec, that external code should apply the
refinement encoded by morphism Refinement, also in this directory. The
refinement is applied by means of Specware's substitution operation. Thus,
morphism Refinement is public. All the other morphisms in this directory are
auxiliary and should not be referenced by external code; in other words, they
are private (to the proof checker). Morphism refinement is part of the API to
the proof checker.

The proof checker specs import libraries whose types and ops do not have the
qualifier MetaslangProofChecker (e.g. spec FiniteSequences). The substitution
of morphism Refinement into spec Spec refines some of those library specs
too. If the external code that uses the proof checker also includes those
libraries, then the refinement of the proof checker determines how those
libraries are refined; in other words, the external code cannot refine those
libraries in different ways from the proof checker. This is probably not a
problem in the near term.

The file dependencies.pdf graphically depicts the dependencies among the
Specware units in this directory. This file is generated from the file
dependencies.ppt.
