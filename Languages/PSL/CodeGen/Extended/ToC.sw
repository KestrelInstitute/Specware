SpecCalc qualifying spec {
  import Convert
  %import ../../MetaSlang/CodeGen/C/ToC
  import ../../../MetaSlang/CodeGen/C/CG
  %import ../../MetaSlang/CodeGen/CodeGenTransforms
  import /Languages/PSL/Semantics/Evaluate/Specs/Op/Legacy
  import ../CGenUtils

  % sort Spec.Spec = ASpec Position

  op oscarToC : Oscar.Spec -> Spec.Spec -> Option String -> Env CSpec
  def oscarToC oscSpec base opt_name =
    let oscSpec = mapOscarSpec (fn(spc) -> (identifyIntSorts (subtractSpec spc base))) oscSpec in
    %let _ = writeLine("initial envSpec="^(printSpec (specOf oscSpec.modeSpec))) in
    let missing = foldlSpecsOscarSpec (fn(spc,missing) ->
				       let spc = transformSpecForCodeGen base spc in
				       mergeSpecs(spc,missing)
				      ) emptySpec oscSpec in
    %let _ = writeLine("missing from base: "^(printSpec missing)) in
    %let oscSpec = mapOscarSpec (fn(spc) -> transformSpecForCodeGen base spc) oscSpec in
    let cSpec = emptyCSpec("") in
    %let envSpec = specOf oscSpec.modeSpec in
    %let _ = writeLine("envSpec="^printSpec(envSpec)) in
    %let envSpec = subtractSpec (specOf oscSpec.modeSpec) base in
    %let cSpec = generateCSpecFromTransformedSpec envSpec in
    {
      %envSpec <- return (subtractSpec (specOf oscSpec.modeSpec) base);
      %print("envSpec="^(printSpec envSpec));
      %oscSpec <- return (mapOscarSpec (fn(spc) -> mergeSpecs(spc,envSpec)) oscSpec);
      oscSpec <- return (mapOscarSpec (fn(spc) -> transformSpecForCodeGen base spc) oscSpec);
      envSpec <- return (specOf oscSpec.modeSpec);
      %print("envSpec="^(printSpec envSpec));
      cSpec <- generateCSpecFromTransformedSpecEnv envSpec;
      cSpec <- return {
		       name                  = case opt_name of 
						 | Some name -> name
						 | _ -> "oscar_cgenout",
		       includes              = cSpec.includes,
		       defines	             = cSpec.defines,
		       constDefns            = cSpec.constDefns,
		       vars                  = cSpec.vars,
		       fns                   = cSpec.fns,
		       axioms                = cSpec.axioms,
		       structUnionTypeDefns  = cSpec.structUnionTypeDefns,
		       varDefns              = cSpec.varDefns,
		       fnDefns               = cSpec.fnDefns
		      };
      cSpec <- ProcMapEnv.fold (generateCProcedure envSpec) cSpec oscSpec.procedures;
      cSpec <- ProcMapEnv.fold delFnDeclForProc cSpec oscSpec.procedures;
      cSpec <- return(CG.postProcessCSpec cSpec);
      printToFileEnv(cSpec,Some cSpec.name);
      %(fail "success"; % useful during development; forces re-elaboration of any example spec
       return cSpec
      %)
    }

  (**
   * removes the "internal" entries from the mode spec and keeps the ones that have to be
   * add to the cspec.
   *)

  op cleanupModeSpec: Spec.Spec * List Op.Ref -> Spec.Spec
  def cleanupModeSpec(spc,parameters) =
    let
      def filterOut(q,id) =
	if member(Qualified(q,id),parameters) then true
	else
	  let expl = explode(id) in
	  if hd(rev(expl)) = #' then true
	    else q = "#return#"
    in
    let srts = foldriAQualifierMap
               (fn(q,id,sinfo,map) ->
		if filterOut(q,id) then map
		else insertAQualifierMap(map,q,id,sinfo)
	       ) emptyASortMap spc.sorts
    in
    let ops = foldriAQualifierMap
               (fn(q,id,sinfo,map) ->
		if filterOut(q,id) then map
		else insertAQualifierMap(map,q,id,sinfo)
	       ) emptyAOpMap spc.ops
    in
    let spc = setSorts(spc,srts) in
    let spc = setOps(spc,ops) in
    let spc = setProperties(spc,[]) in
    spc

  op delFnDeclForProc : CSpec -> Id.Id -> Procedure -> Env CSpec
  def delFnDeclForProc cspc procId procedure =
    return (delFn(cspc,showQualifiedId procId))

  op generateCProcedure : Spec.Spec -> CSpec -> Id.Id -> Procedure -> Env CSpec
  def generateCProcedure envSpec cspc procId (procedure as {parameters,varsInScope,returnInfo,modeSpec,bSpec}) =
    let mmspc = mergeModeSpecs procedure in
    let mmspc = cleanupModeSpec(mmspc,parameters) in
    let newqids = getDeclaredQualifiedIds(subtractSpec mmspc envSpec) in
    let newqids = filter (fn(qid) -> ~(builtinSortOp qid)) newqids in
    %let _ = writeLine("new decls in proc "^(printQualifiedId procId)^(foldl(fn(Qualified(q,id),s) -> s^"\n  "^(q^"."^id)) ": [" newqids)^"]") in
    %let _ = writeLine("proc "^(printQualifiedId procId)^", merged mode-spec="^(printSpec mmspc)) in
    let filter = (fn(qid) -> member(qid,newqids)) in
    %let _ = printCSpecToFile(cSpec,"/tmp/cSpecInGenerateProcedure.c") in
    let mcspc = generateCSpecFromTransformedSpecIncrFilter cspc mmspc filter in
    %let _ = printCSpecToFile(mcspc,"/tmp/mcspcInGenerateProcedure.c") in
    let cspc = mergeCSpecs([cspc,mcspc]) in
    let initSpec = Mode.modeSpec (initial bSpec) in
    let varDecls =
      List.map (fn argRef ->
		let spc = specOf initSpec in
		let (names,fxty,(tyVars,srt),_) = Op.deref (spc, argRef) in
		let (cspc,ctype) = sortToCType cspc spc srt in
		(OpRef.show argRef, ctype))
                parameters
    in
    let (cspc,returnType) =
      case returnInfo of
        | None -> (cspc,Void)
        | Some retRef ->
	    let spc = specOf initSpec in
            let (names,fixity,(tyVars,srt),_) = Op.deref (spc, retRef) in
	    sortToCType cspc spc srt
    in
    let def handler id procedure except =
      case except of
        | SpecError (pos, msg) -> {
             print ("convertOscarSpec exception:" ^ msg ^ "\n");
             procDoc <- ProcEnv.pp id procedure;
             print (ppFormat procDoc);
             print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      % print (";;            procedure: " ^ (Id.show procId) ^ "\n");
      graph <- catch (convertBSpec bSpec) (handler procId procedure);
      graph <- catch (structGraph graph) (handler procId procedure);
      %print(printGraph(graph));
      (cspc,procStmt) <- return (graphToC cspc envSpec graph);
      return (addFnDefnOverwrite(cspc,(showQualifiedId procId,varDecls,returnType,procStmt)))
    }

  op nodeContent : Node -> NodeContent
  def nodeContent (index,content,predecessors) = content
\end{spec}

The following is meant to take a structured graph, as generated by convertBSpec into
a C abstract syntax tree. As far as I know, this does not handle breaks and continues
with a loop or out of a conditional.

\begin{spec}
  op graphToC : CSpec -> Spec.Spec -> Struct.Graph -> CSpec * Stmt
  def graphToC cspc envSpec graph =
    let def consume cspc first last =
      if first = ~1 then
        (cspc,ReturnVoid)
      else if first = last then
        (cspc,Nop)
      else
        % let _ = writeLine ("first = " ^ (Nat.toString first) ^ " last = " ^ (Nat.toString last)) in
          case nodeContent (nth (graph, first)) of

            | Block {statements, next} -> 
                let (cspc,stmts) = List.foldl (fn(statement,(cspc,stmts)) ->
					       let (cspc,stmt) = statementToC cspc statement in
					       (cspc,concat(stmts,[stmt]))
					      ) (cspc,[]) statements in
		let (cspc,rest) = consume cspc next last in
                (cspc,reduceStmt stmts rest)

            | Return (spc,term) -> termToCStmtNew cspc spc term true % Return (termToCExp term)

            | IfThen {condition, trueBranch, cont} ->
		let (spc,condition) = condition in
		let (cspc,block,cexp) = termToCExp cspc spc condition in
		let (cspc,trueExp) = consume cspc trueBranch cont in
                let stmt = IfThen (cexp,trueExp) in
		let stmt = prependBlockStmt(block,stmt) in
                let (cspc,rest) = consume cspc cont last in
                (cspc,reduceStmt [stmt] rest)

            | IfThenElse {condition, trueBranch, falseBranch, cont} ->
		let (spc,condition) = condition in
		let (cspc,block,condExp) = termToCExp cspc spc condition in
                let (cspc,trueStmt) = consume cspc trueBranch cont in
                let (cspc,falseStmt) = consume cspc falseBranch cont in
                let ifStmt = If (condExp, trueStmt, falseStmt) in
		let stmt = prependBlockStmt(block,ifStmt) in
                let (cspc,rest) = consume cspc cont last in
                (cspc,reduceStmt [stmt] rest)

            | Loop {condition, preTest?, body, cont} ->
		let (spc,condition) = condition in
                let (cspc,bodyStmt) = consume cspc body first in
		let (cspc,block,condExp) = termToCExp cspc spc condition in
                let whileStmt = While (condExp, bodyStmt) in
		let stmt = prependBlockStmt(block,whileStmt) in
                let (cspc,rest) = consume cspc cont last in
                (cspc,reduceStmt [stmt] rest)

            | Branch {condition, trueBranch, falseBranch} ->
		let (spc,condition) = condition in
                let _ = writeLine ("ignoring branch") in
                (cspc,Nop)

      def reduceStmt (stmts:Stmts) s2 =
        case s2 of
          | Block ([],moreStmts) -> Block ([],stmts ++ moreStmts)
          | Nop -> Block ([],stmts)
          | _ -> Block ([],stmts ++ [s2])

      def statementToC cspc stat =
        case stat of
          | Assign (spc,term) -> termToCStmtNew cspc spc term false
          | Proc   (spc,term) -> termToCStmtNew cspc spc term false
          | Return (spc,term) -> termToCStmtNew cspc spc term false
    in
      if graph = [] then
        (cspc,Nop)
      else
        consume cspc 0 (length graph)

  op termToCStmtNew : CSpec -> Spec.Spec -> MS.Term -> Boolean -> CSpec * CStmt
  def termToCStmtNew cspc spc term final? =
    let (cspc,block,stmt) =
    case term of
      | Apply (Fun (Equals,srt,_), Record ([("1",lhs), ("2",rhs)],_), _) ->
          (case (lhs, final?) of
            | (Fun (Op (Qualified (_,"ignore'"),fxty),srt,pos), _) -> 
	      let (cspc,block,cexp) = termToCExp cspc spc rhs in
	      (cspc,block,Exp cexp)
            | (Fun (Op (Qualified ("#return#",variable),fxty),srt,pos), true) ->
 	      let (cspc,block,cexp) = termToCExp cspc spc rhs in
	      (cspc,block,Return cexp)
            | _ ->
              (case rhs of
                | Apply(Apply (Apply (Fun (Op (Qualified (_,"update"),fxty),_,pos), Fun (Op (Qualified (_,"active"),fxty),srt,_),  _), idx,_),expr,_) ->
		  let (cspc,ctype) = sortToCType cspc spc srt in
		  let (cspc,block,cexp1) = termToCExp cspc spc idx in
		  let (cspc,block,cexp2) = termToCExpB cspc spc block expr in
		  (cspc,block,Exp (Binary(Set,ArrayRef (Var ("active",ctype),cexp1),cexp2)))
                | Apply (Fun (Op (Qualified (_,"update"),fxty),srt,pos), Record ([("1",Fun (Op (Qualified (_,"env"),fxty),_,_)), ("2",Fun (Nat n,_,_)), ("3",expr)],_), _) ->
		  let (cspc,ctype) = sortToCType cspc spc srt in
		  let (cspc,block,cexp) = termToCExp cspc spc expr in
		  (cspc,block,
		   if n = 0 then
		     Exp (Binary(Set,Unary(Contents,Var ("sp",ctype)),cexp))
		   else
		     Exp (Binary(Set,Unary(Contents,
					   Binary(Add,Var ("sp",ctype), Const (Int (true,n)))),cexp)))
                | _ ->
		  let (cspc,block,cexp1) = termToCExp cspc spc lhs in
		  let (cspc,block,cexp2) = termToCExpB cspc spc block rhs in
		  (cspc,block,Exp (Binary(Set,cexp1, cexp2)))))
      | Apply (Fun (Op (procId,fxty),procSort,pos),(Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)),pos) ->
          % let (Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)) = callArg in
          (case returnTerm of
            | Record ([],_) ->
	      let (cspc,block,cexp) = termToCExp cspc spc (Apply (Fun (Op (procId,fxty),procSort,pos),argTerm,pos)) in
	      (cspc,block,Exp cexp)
            | Fun (Op (Qualified ("#return#",variable),fxty),srt,pos) ->
	      let (cspc,block,cexp) = termToCExp cspc spc (Apply (Fun (Op (procId,fxty),procSort,pos),argTerm,pos)) in
	      (cspc,block,Return cexp)
            | _ ->
	      let (cspc,block,cexp1) = termToCExp cspc spc returnTerm in
	      let (cspc,block,cexp2) = termToCExpB cspc spc block (Apply (Fun (Op (procId,fxty),procSort,pos),argTerm,pos)) in
	      (cspc,block,Exp (Binary(Set,cexp1,cexp2)))
	     )
      | _ -> % let _ = writeLine ("termToCStmt: ignoring term: " ^ (printTerm term)) in
         (cspc,([],[]),Nop)
    in
    (cspc,prependBlockStmt(block,stmt))

}
\end{spec}

Note that the second argument to "consume" above is an index greater
beyond the end of the array. This is deliberate. We could used
infinity. We will not get there as we must encounter a Return first. The
point is that the "consume" function will continue up to but not including
the "last" node.
