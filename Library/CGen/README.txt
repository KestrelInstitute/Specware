This library deals with two approaches to C code generation from
Specware specs.

Deep/ contains a deep embedding of (a subset of) C in Specware.  Using
it, refinement can be expressed as inclusion of predicates over C
programs. (A predicate might say something like "This C program must
have a function named foo, which, when executed, must produce
such-and-such result.")

Shallow/ contains a shallow embedding of (a subset of) C in Specware.
Metaslang operators and types corresponding to C language operations
and types are defined.  C code generation using this approach involves
first refining an arbitrary Metaslang spec into a new spec that is
expressed using only the operators and types that have direct
analogues in C (called the "C Target subset" of Metaslang) and then
straightforwardly translating the resulting spec into a C program
(essentially, just printing the Specware AST as a C program).

There is no All.sw file in this directory (CGen/) for testing,
because the Deep and Shallow models cannot both be imported due to
name clashes.  But see Deep/All.sw and Shallow/All.sw.
