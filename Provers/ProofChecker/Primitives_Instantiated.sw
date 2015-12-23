(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaslangProofChecker qualifying
spec

  % API public all

  import Libs  % systematically imported

  (* This spec instantiates the primitive names introduced in spec Primitives.
  This instantiation is necessary to make the proof checker usable by external
  code, e.g. in order to translate from the Specware internal abstract syntax
  into the proof checker abstract syntax.

  The primitive names are simply instantiated to strings. Actually, operations
  include fixity information, which has no semantic significance but is useful
  for printing out expressions in a more readable way.

  Note that any string is allowed, even if it has with non-printable and
  white-space characters. This has no impact on the semantics but can affect
  the readability of syntactic entities when they are printed out. We assume,
  for printing purposes, that only "reasonable" strings are used. As explained
  in README.txt, we avoid subtypes for arguments of publicly accessible ops
  and constructors; otherwise, we could have defined a subtype of "reasonable"
  strings. *)

  type Fixity =
    | prefix
    | infix

  type TypeName     = String
  type Operation    = String * Fixity
  type TypeVariable = String
  type UserVariable = String
  type UserField    = String
  type AxiomName    = String
  type LemmaName    = String

endspec
