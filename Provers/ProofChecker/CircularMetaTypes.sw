spec

  (* Types depend on expressions, which depends on types and patterns, which
  depend on types. These mutual dependencies manifest in the definitions of
  the (meta) types for such syntactic entities circularly referencing the
  (meta) types. In addition, it is convenient to define abbreviations for
  sequences of types, expressions, and other entities, due to their
  pervasiveness. So, to avoid repetitions, it makes sense to declare all these
  circular meta types in this spec. Some are also defined here, while those
  for types, expressions, and patterns are defined in their own specs for
  better modularity. *)

  import Primitives

  type Type
  type Expression
  type Pattern

  type BoundVar = Variable * Type

  type Fields = FSeq Field


endspec
