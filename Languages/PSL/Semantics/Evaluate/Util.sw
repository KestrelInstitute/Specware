spec {
  import /Languages/MetaSlang/AbstractSyntax/AnnTerm
  import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
  import ../Environment

  op unQualified : String -> QualifiedId
  def unQualified name = Qualified (UnQualified,name)

  op evaluatePSpecElems :
           PSpec Position
        -> List (PSpecElem Position)
        -> Env (PSpec Position * TimeStamp * URI_Dependency)

  op elaborateSpec : PosSpec -> SpecCalc.Env Spec
  def elaborateSpec spc =
    case elaboratePosSpec (spc, "internal") of
      | Ok pos_spec -> return (convertPosSpecToSpec pos_spec)
      | Error msg   -> raise  (OldTypeCheck msg)
}
