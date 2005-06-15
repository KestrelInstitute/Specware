This directory contains a proof checker for the Metaslang logic, written in
Metaslang. The Metaslang logic is formally defined in the document "The Logic
of Metaslang", by Alessandro Coglio, available at Specware4/DevDoc/logic.pdf.
Read that document first and refer to it while reading the .sw files in this
directory. The document is referred to as "LD" (for "Logic Document") in the
comments in the files.

The proof checker developed a few months ago is currently being revised to
reflect recent simplifying changes in the definition of the Metaslang logic in
LD. At this moment, all the old files have been removed from the CVS
repository but only some of the new files have been added. As a result, this
directory currently contains only part of the proof checker. The remaining new
files will be added as soon as they are available.

External code that uses (what is currently available of) the proof checker
should only import the top-level spec Spec. All other specs in this directory
are auxiliary and should not be directly referenced by external code. This
restriction is meant to isolate external code from certain changes in the
proof checker, e.g. if a spec imported by spec Spec were renamed. In other
words, spec Spec is public, while the other specs in this directory are
private (to the proof checker).

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
sum type is public. This is why we only explicitly consider types and ops.

Spec Spec and the public types and ops available there constitute the API for
the proof checker. Currently Specware has no mechanisms to express and enforce
adherence to this API, but a well-intentioned user should find it easy to
adhere to this API.

None of the argument types of the public ops of the proof checker are
subtypes. If a public op had an argument type that is a subtype (e.g. a
non-empty finite sequence of expressions) then Specware's type-checking alone
does not guarantee that external code never calls that op with the empty
sequence of expressions as argument; proof obligations need to be discharged
to guarantee that. However, users often do not discharge proof
obligations. Thus, avoiding subtypes for arguments of public ops makes the
proof checker more robust, forcing it to deal with values that would be
outside the subtypes that would otherwise be used, as opposed to the
unpredictable behavior resulting from violating a subtype.
