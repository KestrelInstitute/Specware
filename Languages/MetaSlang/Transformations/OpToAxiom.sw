Prover qualifying spec
 import ../Specs/Environment
 import ../Specs/SubtractSpec
 import CurryUtils
 import ArityNormalize
 import Simplify
 import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
 import /Languages/SpecCalculus/Semantics/Evaluate/UnitId


  op proverNatSort: () -> Sort

  def proverNatSort() =
    let baseProverSpec = run getBaseProverSpec in
    let optSrt = findTheSort(baseProverSpec, Qualified("PrInteger","ProverNat")) in
    let Some info = optSrt in
    firstSortDefInnerSort info 

  op getBaseProverSpec : Env Spec
  def getBaseProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverBaseUnitId <- pathToRelativeUID "/Library/ProverBase/Top";
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     return (subtractSpec baseProverSpec baseSpec)
    }

  op treatNatSpecially?: Boolean = true

  op simpleFun?(f: Fun): Boolean =
    case f of
      | Not -> true
      | And -> true
      | Or -> true
      | Implies -> true
      | Iff -> true
      | Equals -> true
      | NotEquals -> true
      | _ -> false

  op simpleBody?(bod: MS.Term): Boolean =
    simpleTerm bod
      || (case bod of
            | Record(fields,_) ->
              forall? (fn (_,t) -> simpleTerm t) fields
            | Apply(Fun(f,_,_),arg,_) ->
              simpleBody? arg
            | _ -> false)

  op unfoldSizeThreshold: Nat = 16

  op maybeUnfoldSubTypePred(spc: Spec, predFn: MS.Term): MS.Term =
    case predFn of
      | Fun(Op(qid,_),ty,_) ->
        (case findTheOp(spc, qid) of
           | None -> predFn
           | Some opinfo ->
             (let (tvs,ty1,defn) = unpackFirstOpDef opinfo in
                case defn of
                  | Lambda([(VarPat _, _, bod)],_)
                      | simpleBody? bod && termSize bod < unfoldSizeThreshold ->
                    (case typeMatch(ty1,inferType(spc,defn),spc,true) of
                       | Some subst ->  % Should match!
                         instantiateTyVarsInTerm(defn, subst)
                       | None -> predFn)
                  | _ -> predFn))
      | _ -> predFn

  op srtPred: Spec * Sort * MS.Term -> MS.Term

  %% compute the predicate constraining srt to its ultimate supersort
  def srtPred(spc, srt, tm) =
    % let _ = writeLine ("TPB: "^printTerm tm^": "^printSort srt) in
    let def topPredBaseSrt(srt) =
         case srt of
	   | Base(Qualified("Nat","Nat"),_,_) | treatNatSpecially? -> topPredBaseSrt(proverNatSort())
	   | Base (qid, _, _) ->
             let uf_srt = unfoldBase(spc, srt) in
             if uf_srt = srt
               then (Some qid, mkTrue())
               else topPredBaseSrt uf_srt
	   | Boolean _        -> (None,     mkTrue())
	   | Subsort (supSrt, predFn, _) ->
             let (supBaseSrt, supPred) = topPredBaseSrt(supSrt) in
             let predFn = maybeUnfoldSubTypePred (spc, predFn) in
             % let _ = writeLine("Unfold? "^printTerm predFn) in
             let pred = (simplify spc (mkApply(predFn, tm))) in
             % let _ = writeLine("--> "^printTerm pred) in
	     (case supBaseSrt of
		| Some qid -> (Some qid, Utilities.mkAnd(supPred, pred))
	        | _ -> (None, Utilities.mkAnd(supPred, pred))) 
           | _ -> (None, mkTrue()) in
    let (topBaseQId, topPred) = topPredBaseSrt(srt) in
    % let _ = writeLine (printTerm topPred^"  "^anyToString topBaseQId) in
    case topBaseQId of
      | Some topBaseQId ->
        let optSrt = findTheSort(spc, topBaseQId) in
        (case optSrt of
           | Some info ->               % sjw: I think this case is superceded by unfoldBase above
             (case sortInfoDefs info of
                | [dfn] ->
                  let newSrt = sortInnerSort dfn in
                  Utilities.mkAnd (topPred, srtPred (spc, newSrt, tm))
                | _ -> topPred)
           | _ -> topPred)
      | _ -> topPred

  op opSubsortAxiom: Spec * QualifiedId * Sort -> MS.Term

  def opSubsortAxiom(spc, opname, srt) =
    (case (curryShapeNum(spc, srt), sortArity(spc, srt))
       of (1,None) ->     %let _ = debug("noArity") in 
	 opSubsortNoArityAxiom(spc, opname, srt)
	| (1, Some(_,arity)) -> %let _ = debug("noCurry") in 
	 opSubsortNoCurryAxiom(spc, opname, srt, arity)
	| (curryN, None) -> %let _ = debug("CurryNoArity") in 
	 opSubsortCurryNoArityAxiom(spc, opname, srt)
	| (curryN, Some (_, arity)) -> %let _ = debug("Curry") in 
	 opSubsortCurryAxiom()
	| _ -> %let _ = debug("Last") in
	 opSubsortNoArityAxiom(spc, opname, srt))

  op opSubsortNoArityAxiom: Spec * QualifiedId * Sort -> MS.Term

  def opSubsortNoArityAxiom(spc, opname as Qualified (qual, name), srt) =
    case srt of
      | Arrow(dom, rng, _) ->
       let domVar = ("dom_" ^ name, dom) in
       let domVarTerm = mkVar(domVar) in
       let domPred = srtPred(spc, dom, domVarTerm) in
       let rangeTerm = mkApply(mkOp(opname, srt), domVarTerm) in
       let rangePred = srtPred(spc, rng, rangeTerm) in
       let impl = Utilities.mkSimpImplies(domPred, rangePred) in
       %let fmla = mkBind(Forall, [domVar], impl) in
       let fmla = mkBind(Forall, [domVar], rangePred) in
       fmla
      | _ ->
       let rangeTerm = mkOp(opname, srt) in
       let srtPred = srtPred(spc, srt, rangeTerm) in
       srtPred

  op opSubsortNoCurryAxiom: Spec * QualifiedId * Sort * Nat -> MS.Term

  def opSubsortNoCurryAxiom(spc, opname as Qualified (qual, name), srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    let domVars = map (fn (id: Id, srt:Sort) -> ("dom_" ^ name ^ "_" ^ id, srt))
                              fields in
	    let domVarTerms = map (fn (var) -> mkVar(var)) domVars in
	    let domPreds = map (fn (varTerm) -> srtPred(spc, termSort(varTerm), varTerm))
	                       domVarTerms in
	    let domPred = Utilities.mkSimpConj(domPreds) in
	    let rangeTerm = mkAppl(mkOp(opname, srt), domVarTerms) in
	    let rangePred = srtPred(spc, rng, rangeTerm) in
	    let impl = Utilities.mkSimpImplies(domPred, rangePred) in
	    let fmla = mkBind(Forall, domVars, impl) in
	    let fmla = mkBind(Forall, domVars, rangePred) in
  	      fmla
	  | _ ->
	    let domVar = ("dom_" ^ name, dom) in
	    let domVarTerm = mkVar(domVar) in
	    let domPred = srtPred(spc, dom, domVarTerm) in
	    let rangeTerm = mkApply(mkOp(opname, srt), domVarTerm) in
	    let rangePred = srtPred(spc, rng, rangeTerm) in
	    let impl = Utilities.mkSimpImplies(domPred, rangePred) in
	    %let fmla = mkBind(Forall, [domVar], impl) in
	    let fmla = mkBind(Forall, [domVar], rangePred) in
  	      fmla

  op opSubsortCurryNoArityAxiom: Spec * QualifiedId * Sort -> MS.Term

  def opSubsortCurryNoArityAxiom(spc, qname, srt) =
    opSubsortNoArityAxiom(spc, qname, srt)

  op opSubsortCurryAxiom: () -> MS.Term

  def opSubsortCurryAxiom() =
    mkTrue()

endspec
