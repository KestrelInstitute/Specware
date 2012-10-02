  op foldOverVariables : fa(b) (b -> OpInfo -> b) -> b -> ModeSpec -> b
  def foldOverVariables f unit obj =
    let def g (qual,id,opInfo,x) = 
      let qualId = Qualified (qual,id) in
        if QualifiedId.member? (variables obj) qualId then
          f x opInfo
        else
          x in
    foldriAQualifierMap g unit obj.spc.ops

  op elaborate : ModeSpec -> SpecCalc.Env ModeSpec
  def elaborate obj =
    case elaboratePosSpec (obj.spc, "internal") of
      | Spec elabSpc -> return {spc = convertPosSpecToSpec elabSpc, variables = obj.variables}
      | Errors errors -> raise (TypeCheckErrors errors)

