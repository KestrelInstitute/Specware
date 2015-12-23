(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Prover qualifying spec

import ../Specs/Environment
import ../Specs/SubtractSpec

import /Languages/MetaSlang/Transformations/Simplify
import /Languages/MetaSlang/Transformations/CurryUtils

import /Languages/MetaSlang/CodeGen/Generic/ArityNormalize

import /Languages/SpecCalculus/Semantics/Evaluate/UnitId/Utilities
import /Languages/SpecCalculus/Semantics/Evaluate/UnitId


  op proverNatType: () -> MSType

  def proverNatType() =
    let baseProverSpec = run getBaseProverSpec in
    let optSrt = findTheType(baseProverSpec, Qualified("PrInteger","ProverNat")) in
    let Some info = optSrt in
    firstTypeDefInnerType info 

  op getBaseProverSpec : Env Spec
  def getBaseProverSpec = 
    {
     (optBaseUnitId,baseSpec) <- getBase;
     proverBaseUnitId <- pathToRelativeUID "/Library/ProverBase/Top";
     (Spec baseProverSpec,_,_) <- SpecCalc.evaluateUID (Internal "ProverBase") proverBaseUnitId;
     return (subtractSpec baseProverSpec baseSpec)
    }

  op treatNatSpecially?: Bool = true

  op simpleFun?(f: MSFun): Bool =
    case f of
      | Not -> true
      | And -> true
      | Or -> true
      | Implies -> true
      | Iff -> true
      | Equals -> true
      | NotEquals -> true
      | _ -> false

  op simpleBody?(bod: MSTerm): Bool =
    simpleTerm bod
      || (case bod of
            | Record(fields,_) ->
              forall? (fn (_,t) -> simpleTerm t) fields
            | Apply(Fun(f,_,_),arg,_) ->
              simpleBody? arg
            | _ -> false)

  op unfoldSizeThreshold: Nat = 16

  op maybeUnfoldSubTypePred(spc: Spec, predFn: MSTerm): MSTerm =
    case predFn of
      | Fun(Op(qid,_),ty,_) ->
        (case findTheOp(spc, qid) of
           | None -> predFn
           | Some opinfo ->
             (let (tvs,ty1,defn) = unpackFirstOpDef opinfo in
                case defn of
                  | Lambda([(VarPat _, _, bod)],_)
                      | simpleBody? bod && termSize bod < unfoldSizeThreshold ->
                    (case typeMatch(ty1, ty,spc,true,true) of
                       | Some subst ->  % Should match!
                         % let _ = writeLine(show qid^": Matching "^printType ty^" with "^printType ty1) in
                         instantiateTyVarsInTerm(defn, subst)
                       | None -> predFn)
                  | _ -> predFn))
      | _ -> predFn

  op srtPred: Spec * MSType * MSTerm -> MSTerm

  %% compute the predicate constraining srt to its ultimate supertype
  def srtPred(spc, srt, tm) =
    % let _ = writeLine ("TPB: "^printTerm tm^": "^printType srt) in
    let def topPredBaseSrt(srt) =
         case srt of
	   | Base(Qualified("Nat","Nat"),_,_) | treatNatSpecially? -> topPredBaseSrt(proverNatType())
	   | Base (qid, _, _) ->
             let uf_srt = unfoldBase(spc, srt) in
             if uf_srt = srt
               then (Some qid, mkTrue())
               else topPredBaseSrt uf_srt
	   | Boolean _        -> (None,     mkTrue())
	   | Subtype (supSrt, predFn, _) ->
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
        let optSrt = findTheType(spc, topBaseQId) in
        (case optSrt of
           | Some info ->               % sjw: I think this case is superceded by unfoldBase above
             (case typeInfoDefs info of
                | [dfn] ->
                  let newSrt = typeInnerType dfn in
                  Utilities.mkAnd (topPred, srtPred (spc, newSrt, tm))
                | _ -> topPred)
           | _ -> topPred)
      | _ -> topPred

  op opSubtypeAxiom: Spec * QualifiedId * MSType -> MSTerm

  def opSubtypeAxiom(spc, opname, srt) =
    (case (curryShapeNum(spc, srt), typeArity(spc, srt))
       of (1,None) ->     %let _ = debug("noArity") in 
	 opSubtypeNoArityAxiom(spc, opname, srt)
	| (1, Some(_,arity)) -> %let _ = debug("noCurry") in 
	 opSubtypeNoCurryAxiom(spc, opname, srt, arity)
	| (curryN, None) -> %let _ = debug("CurryNoArity") in 
	 opSubtypeCurryNoArityAxiom(spc, opname, srt)
	| (curryN, Some (_, arity)) -> %let _ = debug("Curry") in 
	 opSubtypeCurryAxiom()
	| _ -> %let _ = debug("Last") in
	 opSubtypeNoArityAxiom(spc, opname, srt))

  op opSubtypeNoArityAxiom: Spec * QualifiedId * MSType -> MSTerm

  def opSubtypeNoArityAxiom(spc, opname as Qualified (qual, name), srt) =
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

  op opSubtypeNoCurryAxiom: Spec * QualifiedId * MSType * Nat -> MSTerm

  def opSubtypeNoCurryAxiom(spc, opname as Qualified (qual, name), srt, arity) =
    case arrowOpt(spc, srt) of
      Some (dom, rng) ->
	case productOpt(spc, dom) of
	  | Some fields -> 
	    let domVars = map (fn (id: Id, typ:MSType) -> ("dom_" ^ name ^ "_" ^ id, typ))
                              fields in
	    let domVarTerms = map (fn (var) -> mkVar(var)) domVars in
	    let domPreds = map (fn (varTerm) -> srtPred(spc, termType(varTerm), varTerm))
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

  op opSubtypeCurryNoArityAxiom: Spec * QualifiedId * MSType -> MSTerm

  def opSubtypeCurryNoArityAxiom(spc, qname, srt) =
    opSubtypeNoArityAxiom(spc, qname, srt)

  op opSubtypeCurryAxiom: () -> MSTerm

  def opSubtypeCurryAxiom() =
    mkTrue()

endspec
