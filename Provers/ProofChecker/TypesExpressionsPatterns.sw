spec

  import Names

  type Type
  type Expression
  type Pattern

  type Type =
    | bool
    | var      Name
    | instance Name * List Type
    | arrow    Type * Type
    | record   List (Name * Type)
    | product  List Type
    | sum      List (Name * Type)
    | sub      Type * Expression
    | quotien  Type * Expression

  type Expression =
    | var

  type Pattern =
    | var

endspec
