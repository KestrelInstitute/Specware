spec

  import Names

  (* Since types are defined in terms of expressions, we declare a type for
  expressions, which is defined in spec `Expressions'. When this spec and spec
  `Expressions' are imported together, union semantics ensures that the type
  declared here is the same defined there. *)

  type Expression

  (* Unlike LD, me model product types directly, instead of viewing them as
  abbreviations of record types with particular names set aside for the
  fields. In fact, unlike LD, names are not required to include projection
  names.

  Another difference with LD is that we do not require fields of record types
  and constructors of sum types to be distinct and we do not require their
  number to match the number of types. We incorporate such requirements into
  the inference rules for well-formedness of types, thus keeping the syntax
  simpler.

  A third difference is that here we explicitly model components of sum types
  that have no type (using `Option'), as opposed to implicitly assuming the
  empty record type as in LD. *)

  type NaryTypeConstruct =
    | instance Name
    | record   FSeq Name
    | product

  type SubOrQuotientTypeConstruct =
    | sub
    | quotien(*t*)

  type Type =
    | boolean
    | variable Name
    | arrow    Type * Type
    | sum      FSeqNE Name * FSeqNE (Option Type)
    | nary     NaryTypeConstruct * FSeq Type
    | subQuot  SubOrQuotientTypeConstruct * Type * Expression

endspec
