spec

  import Primitives

  (* Since types are defined in terms of expressions, we declare a (meta) type
  for expressions, which is defined in spec `Expressions'. When this spec and
  spec `Expressions' are imported together, union semantics ensures that the
  type declared here is the same defined there. *)

  type Expression

  (* Unlike LD, we model product types directly; see explanation in spec
  `Primitives'.

  Another difference with LD is that we do not impose certain requirements
  (e.g. that the fields of a record type must be distinct) in the syntax. We
  incorporate such requirements in the inference rules, thus keeping the
  syntax simpler.

  A third difference is that here we explicitly model components of sum types
  that have no type (using `Option'), as opposed to implicitly assuming the
  empty record type as in LD. *)

  type NaryTypeConstruct =
    | instance TypeName
    | record   FSeq Field
    | product

  type SubOrQuotientTypeConstruct =
    | sub
    | quotien(*t*)

  type Type =
    | boolean
    | variable TypeVariable
    | arrow    Type * Type
    | sum      FSeqNE Constructor * FSeqNE (Option Type)
    | nary     NaryTypeConstruct * FSeq Type
    | subQuot  SubOrQuotientTypeConstruct * Type * Expression

endspec
