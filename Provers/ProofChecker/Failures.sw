spec

  import PrimitivesWithAbbreviations, Positions

  type Failure =
    | noExtraTypeVars
    | noTypeDecl

  type MayFail a =
    | OK a
    | Fail Failure


endspec
