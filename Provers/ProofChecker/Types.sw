spec

  import Libs/FiniteSequences

  import Names

  (* Since types are defined in terms of expressions, we declare a type for
  expressions, which is defined in spec `Expressions'. When this spec and spec
  `Expressions' are imported together, union semantics ensures that the type
  declared here is the same defined there. *)

  type Expression

  (* Unlike LD, me model product types directly, instead of viewing them as
  abbreviations of record types with particular names set aside for the
  fields. In fact, unlike LD, names are not required to include projection
  names. *)

  type VariableType = Name

  type InstanceType = {typ  : Name,
                       args : FSeq Type}

  type ArrowType = {dom : Type,
                    cod : Type}

  type RecordTypeComponent = {field : Name,
                              typ   : Type}

  type RecordType = {comps : FSeq RecordTypeComponent |
                     (let fields = map (project field, comps) in
                      noRepetitions? fields)}

  type SumTypeComponent = {constr : Name, % constr(uctor)
                           typ    : Type}

  type ProductType = {comps : FSeq Type | length comps >= 2}

  type SumType = {comps : FSeqNE SumTypeComponent |
                  (let constrs = map (project constr, comps) in
                  noRepetitions? constrs)}

  type SubType = {base : Type,
                  pred : Expression}

  type QuotientType = {base : Type,
                       pred : Expression}

  type Type =
    | booleanType
    | var  VariableType
    | inst InstanceType
    | arr  ArrowType
    | rec  RecordType
    | prod ProductType
    | sum  SumType
    | sub  SubType
    | quot QuotientType

endspec
