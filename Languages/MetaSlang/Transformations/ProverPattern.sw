(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

Prover qualifying spec

  import /Languages/MetaSlang/Specs/MSTerm
  import /Languages/MetaSlang/Transformations/DistinctVariable
  import /Library/Legacy/DataStructures/ListPair
  import /Library/Legacy/DataStructures/SplaySet
  import Simplify

  op wildCounter: Ref Nat
  def wildCounter = Ref 0

  op initWildCounter: () -> ()
  def initWildCounter () =
    wildCounter := 0

  op useWildCounter: () -> Nat
  def useWildCounter () =
    let res = !wildCounter in
    let _ = wildCounter := res+1 in
    res

  op mkDeComposedEquality: Spec * MSType * MSTerm * MSTerm -> MSTerm
  def mkDeComposedEquality(spc, srt, t1, t2) =
    case (t1, t2) of
      | (Record(args1, _), Record(args2, _)) ->
         let srtList = case srt of
			 | Product (idSrtList, _) -> map (fn (_, srt) -> srt) idSrtList
	                 | _ -> map (fn (_, term) -> inferType(spc, term)) args1 in
         ListPair.foldl ((fn (res, (srt, (_, a1)), (_, a2)) ->
		   let argEq = mkDeComposedEquality(spc, srt, a1, a2) in
		   Utilities.mkAnd(argEq, res)))
	       trueTerm (zip(srtList, args1), args2)
       | (Var (("Wild__Var", _), _), _) -> mkTrue()
       | (_, Var (("Wild__Var", _), _)) -> mkTrue()
       | _ -> mkEquality(srt, t1, t2)

  op mkWildVar: MSType -> MSTerm
  def mkWildVar(srt) =
    let wildCount = useWildCounter() in
    Var(("Wild__Var_"^natToString(wildCount), srt), noPos)

  type CondTerm = MSVars * MSTerm * MSTerm
  type CondTerms = List(CondTerm)

  op printCondTerm: CondTerm -> String

  def printCondTerm(condTerm) =
    let (vars, cond, term) = condTerm in
    let fmla = condTermToFmla(condTerm) in
    "CT: "^printTerm(fmla)

  op condTermToFmlaWithPos: CondTerm * Position -> MSTerm
  def condTermToFmlaWithPos(condTerm, pos) =
    let fmla = condTermToFmla(condTerm) in
    withAnnT(fmla, pos)

  op condTermToFmla: CondTerm -> MSTerm
  def condTermToFmla(condTerm) =
    let (vars, cond, term) = condTerm in
    let body = mkSimpImplies(cond, term) in
    let res = case vars of
                | Nil -> body
                | _ -> mkBind(Forall, vars, body) in
    res

  op removePatternTop: Spec * MSTerm -> MSTerms
  def removePatternTop(spc, term) =
    % let _ = writeLine("PP: "^printTerm(term)) in
    let pos = termAnn(term) in
    let _ = initWildCounter() in
    let condTerms = removePatternTerm(spc, term) in
    let res = map (fn(ct) -> simplify spc (condTermToFmlaWithPos(ct, pos))) condTerms in
    % let _ = map (fn (r) -> writeLine("PPRes: "^printTerm(r))) res in
    let res = filter (fn t -> case t of Fun(Bool true,_,_) -> false | _ -> true) res in
    res

  op generalCrossProduct: [a, b, c] (List (List a)) * (List(a) -> List (b)) * (a * b -> b) * (b -> c) -> List c
  def [a, b, c] generalCrossProduct(listOfList, initialFun, interimFun, finalFun) =
    let def recurseDownOldCrossList(elem:a, crossList:List(b)) =
          case crossList of
	    | Nil -> []
	    | hdCrossList::tlCrossList ->
	      let newHdCrossElem:b = interimFun(elem, hdCrossList:b) in
	      let newTlCrossList = recurseDownOldCrossList(elem, tlCrossList) in
	      newHdCrossElem :: newTlCrossList in
    let def addCrossProduct(list:List(a), crossList) =
          case list of
	    | Nil -> []
	    | hdElem::tlList ->
	      let tlCrossList = addCrossProduct(tlList, crossList) in
	      let newCrossList = recurseDownOldCrossList(hdElem, crossList) in
	      newCrossList++tlCrossList in
    let def generateCrossRec(lists) =
          case lists of
	    | Nil -> []
	    | [list] -> initialFun(list)
	    | hdList::restLists ->
	      let restRes = generateCrossRec(restLists) in
	      addCrossProduct(hdList, restRes) in
    map finalFun (generateCrossRec(listOfList))

  op generateCrossTerms: List(CondTerms) * (MSTerms -> MSTerm) -> CondTerms
(*
  def generateCrossTerms(condTermsList, leafFunction) =
    let def recurseDownOldCrossTerms(condTerm as (vars, cond, term), condCrossTerms) =
          case condCrossTerms of
	    | Nil -> []
	    | (hdVars, hdCond, hdTerms)::tlCondCrossTerms ->
	      let newHdCondCrossTerm = (vars++hdVars, Utilities.mkAnd(cond, hdCond), cons(term, hdTerms)) in
	      let newTlCondCrossTerms = recurseDownOldCrossTerms(condTerm, tlCondCrossTerms) in
	      cons(newHdCondCrossTerm, newTlCondCrossTerms) in
    let def addCrossTerms(condTerms, condCrossTerms) =
          case condTerms of
	    | Nil -> []
	    | hdCondTerm::tlCondTerms ->
	      let tlCondCrossTerms = addCrossTerms(tlCondTerms, condCrossTerms) in
	      let newCondCrossTerms = recurseDownOldCrossTerms(hdCondTerm, condCrossTerms) in
	      newCondCrossTerms++tlCondCrossTerms in
    let def generateCrossRec(condTermsList) =
          case condTermsList of
	    | Nil -> []
	    | [condTerms] -> map (fn (vars, cond, term) -> (vars, cond, [term])) condTerms
	    | condTerms::condTermsRest ->
	      let condTermsRestCrossTerms = generateCrossRec(condTermsRest) in
	      addCrossTerms(condTerms, condTermsRestCrossTerms) in
    let def mkFinalCondTerms(finishedCondTerms):CondTerm =
          let (varsDone, condDone, termsDone) = finishedCondTerms in
	  let finalTerm = leafFunction termsDone in
	  (varsDone, condDone, finalTerm) in
    map mkFinalCondTerms (generateCrossRec(condTermsList))
*)

    def generateCrossTerms(condTermsList, leafFunction) =
      let def initialFun(condTerms:CondTerms) = map (fn (vars, cond, term) -> (vars, cond, [term])) condTerms in
      let def interimFun(condTerm:CondTerm, condCrossTerm: MSVars * MSTerm * MSTerms) =
            let (vars, cond, term) = condTerm in
	    let (dnVars, dnCond, dnTerms) = condCrossTerm in
	    (vars++dnVars, Utilities.mkAnd(cond, dnCond), term :: dnTerms) in
      let def finalFun(condCrossTerms) =
            let (varsDone, condDone, termsDone) = condCrossTerms in
	    let finalTerm = leafFunction termsDone in
	    (varsDone, condDone, finalTerm) in
      generalCrossProduct(condTermsList, initialFun, interimFun, finalFun)
(*
  def generateCases(condTermsList, leafFunction) =
    let def generateCasesPair(condTerms:CondTerms, condTermsDone:List(List(Var)*Term*List(Term))):List(List(Var)*Term*List(Term)) =
          case condTerms of
	    | Nil -> condTermsDone
	    | hdCondTerm::restCondTerms -> 
	        let (varList, cond, term) = hdCondTerm:CondTerm in
		let restCondTermsDone = generateCasesPair(restCondTerms, condTermsDone) in
		let hdCondTerms:List(List(Var)*Term*List(Term)) =
		   map (fn(varsDone:List(Var), condDone:Term, termsDone:List(Term))
                          -> (varList++varsDone, Utilities.mkAnd(cond, condDone), cons(term, termsDone)))
                       condTermsDone in
		hdCondTerms++restCondTermsDone in
    let def generateCasesRec(condTermsList:List(CondTerms)) =
          case condTermsList of
	    | Nil -> []
	    | [[(vars:List(Var), cond:Term, term:Term)]] -> [(vars, cond, [term])]
	    | condTerms::condTermsRest ->
	       let condTermsDone = generateCasesRec(condTermsRest) in
               generateCasesPair(condTerms, condTermsDone) in
    let def mkFinalCondTerms(finishedCondTerms):CondTerm =
          let (varsDone:List(Var), condDone:Term, termsDone:List(Term)) = finishedCondTerms in
	  let finalTerm:Term = leafFunction termsDone in
	  (varsDone, condDone, finalTerm) in
    map mkFinalCondTerms (generateCasesRec(condTermsList))
*)
(*
    case condTermsList of
      | Nil -> []
      | [condTerms] -> condTerms
      | hdCondTerms::tlCondTerms-> mkFinalCondTerms(generateCasesRec(hdCondTerms, generateCases(tlCondTerms)))
*)
  op removePatternTerm: Spec * MSTerm -> CondTerms

  def removePatternTerm(spc, term) =
    if caseTerm?(term) then removePatternCase(spc, renameShadowedVars term) else
    case term of
      | Apply(_) -> removePatternApply(spc, term)
      | Record(_) -> removePatternRecord(spc, term)
      | Bind (_) -> removePatternBind(spc, term)
      | The (_) -> removePatternThe(spc, term)
      | Let(_) -> removePatternLet(spc, term)
      | LetRec(_) -> removePatternLetRec(term)
      | Var(_) -> removePatternVar(term)
      | Fun(_) -> removePatternFun(term)
      | Lambda(_) -> removePatternLambda(term)
      | IfThenElse(_) -> removePatternIfThenElse(spc, term)
      | TypedTerm(_) -> removePatternTypedTerm(term)
      | Seq(trmlst,_) -> removePatternSeq(spc, trmlst)
      | Pi(_,t,_) -> removePatternTerm(spc, t)

def removePatternCase(spc, term) =
  let caseTerm = caseTerm(term) in
  let caseTermSrt = inferType(spc, caseTerm) in
  let caseTermCondTerms = removePatternTerm(spc, caseTerm) in
  let cases = caseCases(term) in
  let casesDisjoint? = disjointMatches cases in
  let def mkPatCond(patTerms, caseTerm) =
        case patTerms of
	  | [patTerm] -> mkDeComposedEquality(spc, caseTermSrt, patTerm, caseTerm)
	  | hdPatTerm::tlPatTerms -> let tlPatCond = mkPatCond(tlPatTerms, caseTerm) in
	                             let hdCond = mkDeComposedEquality(spc, caseTermSrt, hdPatTerm, caseTerm) in
	                             Utilities.mkAnd(hdCond, tlPatCond) in
  let def recurseDownBodyCondTerms(hdCaseVars, caseCond, bodyCTs) =
        case bodyCTs of
	  | Nil -> []
	  | (hdBodyVars, hdBodyCond, hdBody)::tlBodyCTs ->
	    let tlCondTerms = recurseDownBodyCondTerms(hdCaseVars, caseCond, tlBodyCTs) in
	    let newCondTerm = (hdCaseVars++hdBodyVars, Utilities.mkAnd(hdBodyCond, caseCond), hdBody):CondTerm in
	    %let _ = writeLine("hdBody = "^printTerm(hdBody)) in
	    newCondTerm :: tlCondTerms in
  let def combinePatTermsBodyCondTermsCaseCondTerms(patTerms, patVars:MSVars, caseCTs, bodyCTs, negPrevCases) =
        case caseCTs of
	  | Nil -> []
	  | (hdCaseVars, hdCaseCond, hdCaseTerm)::tlCaseCTs ->
	    let patCond = mkPatCond(patTerms, caseTerm) in
	    let caseCond = if casesDisjoint?
	                    then Utilities.mkAnd(hdCaseCond, patCond)
			    else Utilities.mkAnd(negPrevCases, Utilities.mkAnd(hdCaseCond, patCond)) in
	    let hdCondTerms = recurseDownBodyCondTerms(hdCaseVars++patVars, caseCond, bodyCTs) in
	    let tlCondTerms = combinePatTermsBodyCondTermsCaseCondTerms
	                        (patTerms, patVars, bodyCTs, tlCaseCTs, negPrevCases)
	    in
	    hdCondTerms++tlCondTerms in
  let def removePatternCaseCase((pat, _(* cond *), body), negPrevCases) = 
        let bodyCondTerms = removePatternTerm(spc, body) in
	let patTerms = patternToTerms(pat) in
	let patVars = foldl(fn(res,term) -> freeVars(term)++res) [] patTerms in
	%let _ = writeLine("CaseCase: "^printPattern(pat)^", "^printTerm(cond)^", "^printTerm(body)) in
	let res = combinePatTermsBodyCondTermsCaseCondTerms
	            (patTerms, patVars, caseTermCondTerms, bodyCondTerms, negPrevCases)
	in
	%let _ = map (fn (ct) -> writeLine("CaseCaseRes: "^printCondTerm(ct))) res in
	res in
  let def removePatternCaseCases(cases, negPrevCases) =
        case cases of
	  | [] -> []
	  | (hdCase as (pat,_,_))::tlCases ->
	    let hdCaseCondTerms = removePatternCaseCase(hdCase, negPrevCases) in
	    let patTerms = patternToTerms(pat) in
	    let patCond = mkPatCond(patTerms, caseTerm) in
	    let negNewCases = if casesDisjoint? then negPrevCases
	                       else Utilities.mkAnd(negPrevCases, mkNot(patCond)) in
	    let tlCaseCondTerms = removePatternCaseCases(tlCases, negNewCases) in
	    hdCaseCondTerms++tlCaseCondTerms in
  let res = removePatternCaseCases(cases, mkTrue()) in
  %let res = foldl (fn (resCondTerms,singleCase) -> removePatternCaseCase(singleCase)++resCondTerms) [] cases in
  %let _ = writeLine("RemovePatternCase: "^printTerm(term)) in
  %let _ = writeLine(natToString(length(cases))^ " cases.") in
  %let _ = map (fn (ct) -> writeLine(printCondTerm(ct))) res in
  res

  op removePatternApply: Spec * MSTerm -> CondTerms
  def removePatternApply(spc, term as Apply(t1, t2, b)) =
    let res1 = removePatternTerm(spc, t1) in
    let res2 = removePatternTerm(spc, t2) in
    let def mkLeafCase(funCase:CondTerm, argCase:CondTerm) =
          let (funVars, funCond, funTerm) = funCase in
          let (argVars, argCond, argTerm) = argCase in
          let newVars = funVars++argVars in
          let newCond = Utilities.mkAnd(funCond, argCond) in
          let newTerm = mkApply(funTerm, argTerm) in
	  (newVars, newCond, newTerm) in
    let def generateCasesArg(funCase:CondTerm, argCases:CondTerms) =
          case argCases of
	    | Nil -> [funCase]
	    | [argCase] -> [mkLeafCase(funCase, argCase)]
	    | hdArgCase::restArgCases -> Cons(mkLeafCase(funCase, hdArgCase), generateCasesArg(funCase, restArgCases)) in
    let def generateCasesFun(funCases, argCases) =
          case funCases of
	    | [funCase] -> generateCasesArg(funCase, argCases)
	    | hdFunCase::restFunCases -> generateCasesArg(hdFunCase, generateCasesFun(restFunCases, argCases)) in
    generateCasesFun(res1, res2)

  op removePatternRecord: Spec * MSTerm -> CondTerms

  def removePatternRecord(spc, term as Record(fields, b)) =
    let condFieldTermsList = map (fn (id, term) -> removePatternTerm(spc, term)) fields in
    let fieldIds = map (fn(id, term) -> id) fields in
    let def mkLeafCase(terms:MSTerms) =
          mkRecord(zip(fieldIds, terms)) in
    generateCrossTerms(condFieldTermsList, mkLeafCase)

(*  op findNewVar: MSVar * MSVars -> MSVar

  def findNewVar(var, vars) =
    let ids = map (fn (id, srt) -> id) vars in
    let (id, srt) = var in
    let def findNewIdRec(id, ids, num) =
          if member(id, ids) then findNewIdRec(mkNewId(id, num), ids, num+1) else id in
    let newId = findNewIdRec(id, ids, 1) in
 *)

  op insertNewVar: MSVar * MSVars -> MSVars
  def insertNewVar(v, l) =
    case l of
      | [] -> [v]
      | v1::l1 ->
          if equalVar?(v, v1) then
            l
          else
            Cons (v1, insertNewVar (v, l1))

  op varUnion: MSVars * MSVars -> MSVars
  def varUnion(vl1, vl2) = foldl (fn (l,v) -> insertNewVar(v,l)) vl1 vl2

  op removePatternBind: Spec * MSTerm -> CondTerms
  def removePatternBind(spc, term as Bind (binder, bndVars, body, b)) =
    let printT = printTerm(term) in
    %let _ = if printT = "fa(n : NN) p n = fa(n1 : NN) (~(lte(n1, n)) => lte(n, n1))"
    %           then debug("rpb!")
    %        else () in
    let bodyConds = removePatternTerm(spc, body) in
    let def mkLeafCase(condTerm) =
          let (newVars, newCond, newBody) = condTerm in
	  %let r = (varUnion(bndVars,newVars), newCond, newBody) in
	  let r = (newVars, mkTrue(), mkBind(binder, bndVars, mkSimpImplies(newCond, newBody))) in
	  %let _ = debug("rpb") in
	  r in
    let res = map (fn (condTerm) -> mkLeafCase(condTerm)) bodyConds in
    %let _ = writeLine("RemovePatternBind: "^printTerm(term)) in
    %let _ = map (fn (ct) -> writeLine(printCondTerm(ct))) res in
    res

  op removePatternThe: Spec * MSTerm -> CondTerms
  def removePatternThe(spc, term as The (var, body, b)) =
    let bodyConds = removePatternTerm (spc, body) in
    let def mkLeafCase(condTerm) =
          let (newVars, newCond, newBody) = condTerm in
	  let r = (newVars, mkTrue(), mkThe(var, mkSimpImplies(newCond, newBody))) in
	  r in
    let res = map (fn (condTerm) -> mkLeafCase(condTerm)) bodyConds in
    res

  op patternToTerms: MSPattern -> MSTerms
  def patternToTerms(pat) =
    case pat of
      | AliasPat(_) -> aliasPatternToTerms(pat)
      | VarPat(var0, b) -> [mkVar(var0)]
      | EmbedPat(_) -> embedPatternToTerms(pat)
      | RecordPat(_) -> recordPatternToTerms(pat)
      | StringPat(string, b) -> [mkString(string)]
      | BoolPat(bool, b) -> [mkBool(bool)]
      | CharPat(char, b) -> [mkChar(char)]
      | NatPat(nat, b) -> [mkNat(nat)]
      | WildPat(srt, _) -> [mkWildVar(srt)]
      | QuotientPat(p,_,_,_)  -> patternToTerms p
      | RestrictedPat(p,_,_) -> patternToTerms p
      | _ -> fail("pattern not supported")

  op aliasPatternToTerms: MSPattern -> MSTerms
  def aliasPatternToTerms(pat as AliasPat(pat1, pat2, b)) =
    let terms1 = patternToTerms(pat1) in
    let terms2 = patternToTerms(pat2) in
    terms1++terms2

  op embedPatternToTerms: MSPattern -> MSTerms
  def embedPatternToTerms(pat as EmbedPat(id, optPat, srt, b)) =
    case optPat of
      | None -> [mkEmbed0(id, srt)]
      | Some(pat) -> let argTerms = patternToTerms(pat) in
                       map (fn (argTerm) ->
			    let domType = termType argTerm in
			    mkApply(mkEmbed1(id, Arrow(domType,srt,b)), argTerm))
		         argTerms

  op crossProduct: [a, b] List a * List b -> List (a*b)
  def crossProduct(l1, l2) =
    case l1 of
      | Nil -> []
      | hd1::tl1 -> let tlRes = crossProduct(tl1, l2) in
                    let hdRes = map (fn (e2) -> (hd1, e2)) l2 in
		    hdRes++tlRes

  op crossProductList: [a] List(List a) -> List(List a)
  def [a] crossProductList(ll) =
    let def crossProductTwoList(l1:(List a), l2) =
          case l1 of
	    | Nil -> []
	    | hd1::tl1 -> let tlRes = crossProductTwoList(tl1, l2) in
                          let hdRes = map (fn (e2) -> hd1 :: e2) l2 in
			    hdRes++tlRes in
    case ll of
      | [last] -> map (fn (e) -> [e]) last
      | hdL::tlL -> let tlRes = crossProductList(tlL) in
                   let res = crossProductTwoList(hdL, tlRes) in
		   res

  op idTermListToListIdTerm: Id*MSTerms -> List(Id * MSTerm)
  def idTermListToListIdTerm(id, terms) =
    map (fn (term) -> (id, term)) terms

  op idPatternListToListListIdTerm: List(Id*MSPattern) -> List(List(Id*MSTerm))
  def idPatternListToListListIdTerm(idPatList) =
    case idPatList of
      | Nil -> []
      | (hdId, hdPat)::tlIdPatList ->
        let tlRes = idPatternListToListListIdTerm(tlIdPatList) in
	let patTerms = patternToTerms(hdPat) in
	let hdListIdTerm = idTermListToListIdTerm(hdId, patTerms) in
	hdListIdTerm :: tlRes
  
  op recordPatternToTerms: MSPattern -> MSTerms
  def recordPatternToTerms(pat as RecordPat(fieldPats:List(Id*MSPattern), b)) =
    let recordFieldsList = idPatternListToListListIdTerm(fieldPats) in
    let def crossFieldProduct(recordFieldsList) = crossProductList(recordFieldsList) in
    let recordFieldsCross = crossFieldProduct(recordFieldsList) in
    map (fn (fields) -> mkRecord(fields)) recordFieldsCross

  op removePatternLet: Spec * MSTerm -> CondTerms
  def removePatternLet(spc, term as Let(patternTermList, body, b)) =
    let newBodyCondTerms = removePatternTerm(spc, body) in
    let def patternTermsToVarsConds(patTerms, term, srt) =
          case patTerms of
	  %  | Nil -> []
	    | [patTerm] -> (freeVars(patTerm), mkDeComposedEquality(spc, srt, patTerm, term))
	    | hdPatTerm::tlPatTerms -> 
	      let hdVars = freeVars(hdPatTerm) in
	      let hdCond = mkDeComposedEquality(spc, srt, hdPatTerm, term) in
	      let (tlVars, tlCond) = patternTermsToVarsConds(tlPatTerms, term, srt) in
	      (hdVars++tlVars, Utilities.mkAnd(hdCond, tlCond)) in
    let def patternAndTermToVarsConds(pat, term) =
          let srt = inferType(spc, term) in
	  let patTerms = patternToTerms(pat) in
	  patternTermsToVarsConds(patTerms, term, srt) in
    let def varsCondRecurse(vars, cond) =
          let condTermsForCond = removePatternTerm(spc, cond) in
	  map (fn (vs, c, t) -> (vars++vs, Utilities.mkAnd(c, t))) condTermsForCond in
    let def patternTermListToVarsConds(patternTermList) =
          %let _ = debug("patternTermList") in
	  let varsCondsList = map (fn (pat, term) -> varsCondRecurse(patternAndTermToVarsConds(pat, term))) patternTermList in
	  let def initialFun(x) = x in
	  let def interimFun(varsCond1, varsCond2) =
	        let (vars1, cond1) = varsCond1 in
	        let (vars2, cond2) = varsCond2 in
		(vars1++vars2, Utilities.mkAnd(cond1, cond2)) in
	  let def finalFun(x) = x in
	  generalCrossProduct(varsCondsList, initialFun, interimFun, finalFun) in
    let def crossLetTerms(patVarsConds, bodyCondTerms) =
	  case patVarsConds of
	    | Nil -> []
	    | (hdVars, hdCond)::tlPatVarsConds -> 
	      let hdCondTerms = map (fn (vars, cond, term) -> (hdVars++vars, Utilities.mkAnd(hdCond, cond), term)) bodyCondTerms in
	      let tlCondTerms = crossLetTerms(tlPatVarsConds, bodyCondTerms) in
	      hdCondTerms++tlCondTerms in
    let patVarsConds = patternTermListToVarsConds(patternTermList) in
    let res =  crossLetTerms(patVarsConds, newBodyCondTerms) in
    %let _ = writeLine("removePatternLet: "^printTerm(term)) in
    res

  op removePatternVar: MSTerm -> CondTerms
  def removePatternVar(term) = [([], mkTrue(), term)]

  op removePatternFun: MSTerm -> CondTerms
  def removePatternFun(term) = [([], mkTrue(), term)]

  op removePatternLambda: MSTerm -> CondTerms
  def removePatternLambda(term) = [([], mkTrue(), term)]

  op removePatternIfThenElse: Spec * MSTerm -> CondTerms
  def removePatternIfThenElse(spc, term as IfThenElse(condTerm, thenTerm, elseTerm, b)) =
    let condCondTerms = removePatternTerm(spc, condTerm) in
    let thenCondTerms = removePatternTerm(spc, thenTerm) in
    let elseCondTerms = removePatternTerm(spc, elseTerm) in
    let def recurseDownBranchCondTerms(branchVars, branchCond, branchCondTerms) =
          case branchCondTerms of
	    | Nil -> []
	    | (hdVars, hdCond, hdTerm)::tlBranchCondTerms ->
	      let tlRes = recurseDownBranchCondTerms(branchVars, branchCond, tlBranchCondTerms) in
	      let hdRes = (branchVars++hdVars, Utilities.mkAnd(branchCond, hdCond), hdTerm) in
	      hdRes :: tlRes in
    let def recurseDownCondCondTerms(condCondTerms, thenCondTerms, elseCondTerms) =
          case condCondTerms of
	    | Nil -> []
	    | (hdCondVars, hdCondCond, hdCondTerm):: tlCondCondTerms ->
	      let tlRes = recurseDownCondCondTerms(tlCondCondTerms, thenCondTerms, elseCondTerms) in
	      let thenCond = Utilities.mkAnd(hdCondCond, hdCondTerm) in
	      let elseCond = Utilities.mkAnd(hdCondCond, mkNot(hdCondTerm)) in
	      let thenRes = recurseDownBranchCondTerms(hdCondVars, thenCond, thenCondTerms) in
	      let elseRes = recurseDownBranchCondTerms(hdCondVars, elseCond, elseCondTerms) in
	      thenRes++elseRes++tlRes in
     recurseDownCondCondTerms(condCondTerms, thenCondTerms, elseCondTerms)

  op removePatternTypedTerm: MSTerm -> CondTerms
  def removePatternTypedTerm(term) = [([], mkTrue(), term)]

  op removePatternSeq: Spec * MSTerms -> CondTerms
  def removePatternSeq(spc, trmlst) =
    let lastTerm = last(trmlst) in
    removePatternTerm(spc, lastTerm)

  op removePatternLetRec: MSTerm -> CondTerms
  def removePatternLetRec(term) = [([], mkTrue(), term)]

(*  op removePattern: Spec -> Spec
  def removePattern spc =
    let usedNames = StringSet.fromList(qualifierIds spc.ops) in
    setOps (spc, 
            mapOpInfos (fn info -> 
			let pos = termAnn info.dfn in
			let (old_decls, old_defs) = opInfoDeclsAndDefs info in
			let new_axioms =
			    axiomFromOpDefTop(spc, q, id, info)
			    foldl
			    (fn dfn ->
			     let pos = termAnn dfn in
			     let (tvs, srt, term) = unpackFirstTerm dfn in
			     let usedNames = addLocalVars (term, usedNames) in
			     let tm = 
			     normalizeArityTopLevel (spc, [], usedNames,
						     etaExpand (spc, usedNames, srt, term))
			     in
			       maybePiTerm (tvs, TypedTerm (tm, srt, pos)))
			        old_defs
			in
			let new_dfn = maybeAndTerm (old_decls ++ new_defs, pos) in
			info << {dfn = new_dfn})
	               spc.ops)
*)
(****
         | WildPat  _ -> result
 (* These cases do not appear after pattern match compilation, 
   but are listed for independence of possible pattern matching *)
        | AliasPat(p1,p2) -> 
          insertPattern(p1,insertPattern(p2,result))
        | EmbedPat(_,Some p,_) -> insertPattern(p,result)
        | QuotientPat(p,t) -> insertPattern(p,result)
        | _ -> result

 ****)


endspec
