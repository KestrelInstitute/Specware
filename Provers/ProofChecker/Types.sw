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
  and constructors of sum types to be distinct in the syntax. We
  incorporate such a requirement into the inference rules for well-typedness,
  thus keeping the syntax simpler.

  A third difference is that here we model explicitly components of sum types
  that have no type (using `Option'), as opposed to implicitly assuming the
  empty record type as in LD. *)

  type Type =
    | boolean
    | variable     Name
    | instance     Name * FSeq Type
    | arrow        Type * Type
    | record       FSeq (Name * Type)
    | product      FSeq Type
    | sum          FSeqNE (Name * Option Type)
    | sub          Type * Expression
    | quotien(*t*) Type * Expression

endspec
