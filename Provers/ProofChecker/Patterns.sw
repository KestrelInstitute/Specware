spec

  import Names

  (* Since patterns are defined in terms of types, we declare a (meta) type
  for types, which are defined in spec `Types'. When this spec and spec
  `Types' are imported together, union semantics ensures that the type
  declared here is the same defined there. *)

  type Type

  (* Unlike LD, we do not require the fields of a record pattern to be
  distinct. Such a requirement is imposed in the inference rules. This keeps
  the syntax simpler.

  Another difference with LD is that here embedding patterns are decorated by
  types, not necessarily sum types. The inference rules require the decorating
  type of an embedding pattern to be a sum type. *)

  % useful notion (frequently used):
  type TypedVar = Name * Type

  type Pattern =
    | variable  TypedVar
    | embedding Type * Name * Pattern
    | record    FSeq (Name * Pattern)
    | alias     TypedVar * Pattern

endspec
