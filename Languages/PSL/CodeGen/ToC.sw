SpecCalc qualifying spec {
  import Convert
  import ../../MetaSlang/CodeGen/C/ToC

  op pSpecToC : PSpec -> Spec -> CSpec
  def pSpecToC pSpec base =
    let cSpec = emptyCSpec in
    let cSpec = generateCTypes cSpec (subtractSpec pSpec.dynamicSpec base) in
    let cSpec = generateCVars cSpec (subtractSpec pSpec.dynamicSpec base) in
    let cSpec = generateCFunctions cSpec (subtractSpec pSpec.dynamicSpec base) in
    let cSpec = foldMap generateCProcedure cSpec pSpec.procedures in
    let _ = writeLine (PrettyPrint.toString (format (80, ppCSpec cSpec))) in
    cSpec

  op generateCProcedure : CSpec -> QualifiedId -> Procedure -> CSpec
  def generateCProcedure cSpec name {parameters,returnInfo,staticSpec,dynamicSpec,code} =
    let varDecls =
      map (fn argName ->
         (case findTheOp (dynamicSpec, Qualified (UnQualified, argName)) of
            | None -> fail ("arg " ^ argName ^ " not in dynamic spec")
            | Some (names,fixity,(tyVars,srt),optTerm) -> (argName, sortToCType srt))) parameters in
    let returnType =
      case returnInfo of
        | None -> Void 
        | Some {returnName,returnSort} ->
            (case findTheOp (dynamicSpec, Qualified (UnQualified,returnName)) of
              | None -> fail ("return " ^ returnName ^ " not in dynamic spec")
              | Some (names,fixity,(tyVars,srt),optTerm) -> sortToCType srt) in
    let procStmt = graphToC (convertBSpec code dynamicSpec) in
    addFuncDefn cSpec (showQualifiedId name) varDecls returnType procStmt

  op nodeContent : Node -> NodeContent
  def nodeContent (index,content,predecessors) = content

  op graphToC : Struct.Graph -> Stmt
  def graphToC graph =
    let def consume first last =
          if first = last then
            Nop
          else
            case nodeContent (nth (graph, first)) of
              | Block {statements, next} -> 
                  let stmts = map statementToC statements in
                  reduceStmt stmts (consume next last) 

              | Return term -> Return (termToCExp term)

              | IfThen {condition, trueBranch, continue} ->
                  let stmt = IfThen (termToCExp condition, consume trueBranch continue) in
                  let rest = consume continue last in
                  reduceStmt [stmt] rest

              | IfThenElse {condition, trueBranch, falseBranch, continue} ->
                  let trueStmt = consume trueBranch continue in
                  let falseStmt = consume falseBranch continue in
                  let ifStmt = If (termToCExp condition, trueStmt, falseStmt) in
                  let rest = consume continue last in
                  reduceStmt [ifStmt] rest

              | Loop {condition, preTest?, body, endLoop, continue} ->
                  let bodyStmt = consume body first in
                  let whileStmt = While (termToCExp condition, bodyStmt) in
                  let rest = consume continue last in
                  reduceStmt [whileStmt] rest

        def reduceStmt stmts s2 =
          case s2 of
            | Block ([],moreStmts) -> Block ([],stmts ++ moreStmts)
            | Nop -> Block ([],stmts)
            | _ -> Block ([],stmts ++ [s2])

        def statementToC stat =
          case stat of
            | Assign term -> termToCStmt term
            | Proc term -> termToCStmt term
            | Return term -> termToCStmt term
    in
      consume 0 ((length graph) - 1)
}
