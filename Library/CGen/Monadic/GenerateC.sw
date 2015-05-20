GenerateC qualifying spec
  import C_DSL, /Languages/MetaSlang/Transformations/Script

  op generateC_RuleNames: QualifiedIds =
    map (fn id -> Qualified("C_DSL", id))

      ["VAR_correct", "ICONST_correct", "STAR_correct", "PLUS_correct",
       "MINUS_correct", "NOT_correct", "NEG_correct", "MUL_correct",
       "DIV_correct", "REM_correct", "ADD_correct", "SUB_correct",
       "SHL_correct", "SHR_correct", "LT_correct", "GT_correct", "LE_correct",
       "GE_correct", "EQ_correct", "NE_correct", "AND_correct", "XOR_correct",
       "IOR_correct", "LAND_correct", "LOR_correct", "SUBSCRIPT_correct",
       "LVAR_correct", "ADDR_correct", "LSTAR_correct", "LSUBSCRIPT_correct",
       "ASSIGN_correct", "IFTHENELSE_correct", "WHILE_correct", "BLOCK_correct",
       "BLOCK_helper_correct1", "BLOCK_helper_correct2",
       "BLOCK_helper_correct3", "FUNCTION_correct"]

  op MSTermTransform.generateC (spc: Spec) (path_term: PathTerm) (qid: TransOpName) (options: RewriteOptions): MSTerm * Proof =
    rewrite spc path_term qid
      (map Strengthen generateC_RuleNames)
      (options << {allowUnboundVars? = true})

end-spec

