%JGen qualifying
spec

import /Languages/MetaSlang/Specs/Utilities
import /Languages/MetaSlang/Specs/Environment
import /Languages/SpecCalculus/Semantics/Environment
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AccessSpec % sortIsDefinedInSpec?
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
%import /Languages/SpecCalculus/Semantics/Evaluate/Spec

sort Term = MS.Term
%sort Env a = SpecCalc.Env a

sort Op = QualifiedId

sort Type = Sort
%sort BaseType = (Sort | baseType?)

sort OpDef = Op * List Sort * Sort * List Var * Term
% the Boolean flag is used to distinguish the case of a function with no arguments
% from a constant: if the flag is true, then it's a constant
sort OpDef2 = Op * List Sort * Sort * List Var * Term * Boolean (* constant or function *)

op unSupported: Op -> String
def unSupported x =
  let msg = "\nWarning: unsupported op: " ^ (printQualifiedId x) ^ "\n" in
  let _ = toScreen msg in
  msg

(**
 * a base type wrt. code generation are the builtin base types Boolean,Nat,Integer,Char,String
 * and also those types that do *not* have a definition in the spec, i.e. those which
 * are just declared.
 * TODO:  v3:p1 says base types are exactly Boolean, Int, Char  -- resolve this
 *)
op baseType?: Spec * Sort -> Boolean
def baseType? (spc, typ) =
  %let _ = writeLine("baseType? "^(printSort typ)^"...") in
  %% TODO: is this a complete set?  See basicQualifiers
  boolSort?    typ ||   % v3:p1 
  integerSort? typ ||   % v3:p1 
  natSort?     typ ||   % v3:p1 says NO  -- TODO: resolve this
  stringSort?  typ ||   % v3:p1 says NO  -- TODO: resolve this
  charSort?    typ ||   % v3:p1 
  (case typ of
     | Base _ -> ~ (sortIsDefinedInSpec? (spc, typ))  % v3:p1 says NO -- TODO: resolve this
     | _ -> false)

 op builtinBaseType?: Sort -> Boolean
def builtinBaseType? typ =
  boolSort?    typ || % v3:p1 
  integerSort? typ || % v3:p1 
  natSort?     typ || % v3:p1 says NO  -- TODO: resolve this
  stringSort?  typ || % v3:p1 says NO  -- TODO: resolve this
  charSort?    typ    % v3:p1 

 op baseTypeAlias?: Spec * Sort -> Boolean
def baseTypeAlias? (spc, srt) =
  if baseType? (spc, srt) then 
    true
  else
    let usrt = unfoldBase (spc, srt) in
    case usrt of
      | Subsort  (srt,_,_) -> baseTypeAlias? (spc, srt)
      | Quotient (srt,_,_) -> baseTypeAlias? (spc, srt)
      | _ -> baseType?(spc,usrt)

 op builtinBaseTypeId?: Id -> Boolean  
def builtinBaseTypeId? id =
  %% TODO: is this a complete set?  See basicQualifiers
  id = "Boolean" || % v3:p1 
  id = "Integer" || % v3:p1 
  id = "Nat"     || % v3:p1 says NO  -- TODO: resolve this
  id = "String"  || % v3:p1 says NO  -- TODO: resolve this
  id = "Char"       % v3:p1 

 op baseTypeId?: Spec * Id -> Boolean
def baseTypeId? (spc, id) =
  id = "Boolean" || % v3:p1 
  id = "Integer" || % v3:p1 
  id = "Nat"     || % v3:p1 says NO  -- TODO: resolve this
  id = "String"  || % v3:p1 says NO  -- TODO: resolve this
  id = "Char"    || % v3:p1 
  ~ (sortIdIsDefinedInSpec? (spc, id)) % v3:p1 says NO: resolve this

op userType?: Spec * Sort -> Boolean

(**
 * extended the definition of userType? to check not only that it is not a base type, 
 * but also that it is the name of a type, as opposed to being a complex type such as arrow type
 *
 * TODO: v3:p2 says "Each user-defined type has a definition that is a type product, sum, restriction, or quotient."
 * So if srt expands to a base sort, v3 says it is not a user type.
 * Note that this would have at least the effect of shifting more methods into Primitive.java
 * I'm not sure what other effects there might be.
 * 
 *)
def userType?(spc,srt) =
  % let srt = unfoldBase (spc, srt) in  % v3:p2 would imply this -- TODO: resolve this
  if baseType?(spc,srt) then false
  else
    (case srt of
       | Base(qid,_,_) -> true
       %| Subsort(srt,_,_) -> userType?(srt)
       %| Quotient(srt,_,_) -> userType?(srt)
       | _ -> false
      )

def notAUserType?(spc,srt) = ~(userType?(spc,srt))

(**
 * implementation of the ut function as defined in v3:p38 (but see notes above for baseType? and userType?)
 * returns the first user type occuring in the type srt from left to right, where the constituent of
 * each srt is also considered in case srt is an arrow type
 *)
op ut: Spec * Sort -> Option Sort
def ut(spc,srt) =
  ut_internal (fn(s) -> userType?(spc,s)) srt

op ut_internal: (Sort -> Boolean) -> Sort -> Option Sort
def ut_internal isUserType? srt =
  let
    def utlist0(srts) =
      case srts of
	| [] -> None
	| srt::srts -> 
	  (case ut_internal isUserType? srt of
	     | Some s -> Some s
	     | None -> utlist0(srts)
	    )
  in
  if isUserType?(srt) then Some srt
  else
    let domsrts = srtDom(srt) in
    case utlist0(domsrts) of
      | Some s -> Some s
      | None -> 
        (case srt of
	   | Arrow(_,rng,_) -> ut_internal isUserType? rng
	   | _ -> None
	  )

op utlist: Spec * List Sort -> Option Sort
def utlist(spc,srts) = 
  utlist_internal (fn(srt) -> userType?(spc,srt)) srts

op utlist_internal: (Sort -> Boolean) -> List Sort -> Option Sort
def utlist_internal isUserType? srts =
  case srts of
    | [] -> None
    | srt::srts ->
      (case ut_internal isUserType? srt of
	 | Some s -> Some s
	 | None -> utlist_internal isUserType? srts
	)


(** 
 * returns whether or not the given sort is "flat" meaning that it
 * is a simple identifier, not an arrow sort, for instance.
 *)
op flatType?: Sort -> Boolean
def flatType?(srt) =
  case srt of
    | Base(qid,_,_) -> true
    | _ -> false

op baseVar?: Spec * Var -> Boolean
op userVar?: Spec * Var -> Boolean

def baseVar?(spc,variable) =
  let (id, srt) = variable in
  baseType?(spc,srt)

def userVar?(spc,variable) =
  ~ (baseVar?(spc,variable))

(**
  * disabled this op def, the new srtId op is in ToJavaBase; it also handles other kinds of types.
  *)
op srtId_v2: Sort -> Id 
def srtId_v2(srt as Base (Qualified (q, id), _, _)) = id

op mkNewOp: Op * Nat -> Op

def mkNewOp(oper, k) =
  let Qualified (qual, id) = oper in
  mkQualifiedId(qual, id ^ natToString(k))

op mkNewVar: Op * Nat * Sort -> Var

def mkNewVar(oper, k, t) =
  let Qualified (qual, id) = oper in
  (id ^ natToString(k), t)

op caseTerm?: Term -> Boolean

def caseTerm?(term) =
  case term of
    | Apply (Lambda (match, _), trm, _) -> true
    | _ -> false

op caseTerm: (Term | caseTerm?) -> Term

def caseTerm(term) =
  let Apply (Lambda (match, _), trm, _) = term in
    trm

op caseCases: (Term | caseTerm?) -> Match
def caseCases(trm) =
  let  Apply (Lambda (match, _), trm, _) = trm in
    match

op recordFieldsToTerms: List (Id * Term) -> List Term

def recordFieldsToTerms(fields) : List Term =
  case fields of 
    | [] -> []
    | (id,term)::fields -> cons(term, recordFieldsToTerms(fields))

op applyArgsToTerms: Term -> List Term

def applyArgsToTerms(args) =
  case args of
    | Record (fields,_) -> recordFieldsToTerms(fields)
    | term -> [term]

(**
 * this is the reverse of "applyArgsToTerms": it takes a term and a list of terms and
 * exchanges the terms in argTerm by the terms in args. If argTerm is not a Record, then
 * args must be a one-elementary list of terms, otherwise, the #elems in the Record fields
 * and the #elems in the args list must be the same.
 *) 
op exchangeArgTerms: Term * List Term -> Term
def exchangeArgTerms(argTerm,args) =
  case argTerm of
    | Record(fields,b) ->
      let zip = zip(fields,args) in
      let fields = map (fn((id,_),t) -> (id,t)) zip in
      Record(fields,b)
    | _ -> (case args of
	      | [t] -> t
	      | _ -> argTerm % should not happen
	   )

op opDom: Spec * Op -> List Sort
op opRange: Spec * Op -> Sort

def opDom (spc, oper) =
  let infos = findAllOps (spc, oper) in
  case infos of
    | info ::_ -> 
      let srt = firstOpDefInnerSort info in
      srtDom srt
    | _ -> 
      let _ = unSupported oper in 
      []

def opRange (spc, oper) =
  let infos = findAllOps (spc, oper) in
  case infos of
    | info ::_ -> 
      let srt = firstOpDefInnerSort info in
      srtRange srt
    | _ -> 
      let _ = unSupported oper in 
      boolSort

op srtDom: Sort -> List Sort
op srtRange: Sort -> Sort

def srtDom(srt) =
  let def domSrtDom(dom) =
       (case dom of
	  | Product (fields,    _) -> map (fn (_,srt) -> srt) fields
	  | Subsort (subSrt, _, _) -> domSrtDom subSrt
	  | _ -> [dom]) 
  in
  case srt of
    | Arrow (dom, rng, _) ->
      (let argSorts = domSrtDom dom in
       argSorts)
    | Pi (_, s, _) -> srtDom s
    | _ -> []

op srtDomKeepSubsorts: Sort -> List Sort
def srtDomKeepSubsorts srt =
  let def domSrtDom dom =
       (case dom of
	  | Product (fields, _) -> map (fn (_,srt) -> srt) fields
	  %| Subsort (subSrt, _, _) -> domSrtDom(subSrt)
	  | _ -> [dom]) in
  case srt of
    | Arrow (dom, rng, _) ->
      (let argSorts = domSrtDom(dom) in
       argSorts)
    | Pi (_, s, _) -> srtDomKeepSubsorts s
    | _ -> []

def srtRange srt =
  case srt of
    | Arrow (dom, rng, _) -> rng
    | Pi (_, s, _) -> srtRange s
    | _ -> srt

op srtDomPreds: Sort -> List (Option Term)
def srtDomPreds srt =
  %let _ = writeLine("srtDomPreds "^printSort(srt)) in
  let def srtPred (srt) : Option Term =
        case srt of
	  | Subsort(_,pred,_) -> 
	    %let _ = writeLine("collecting restriction term "^printTerm(pred)) in
	    Some pred
	  | _ -> None
  in
    case srt of
      | Arrow (Product (fields,_),_,_) -> map (fn(_,srt) -> srtPred(srt)) fields
      | Arrow (srt, _, _) -> [srtPred(srt)]
      | Pi (_, s, _) -> srtDomPreds s
      | _ -> []

op patternNameOpt : Pattern       -> Option Id
op patternNamesOpt: Pattern       -> Option (List Id)

def patternNameOpt (pattern) = 
  case pattern of
    | VarPat((id,_),_) -> Some id 
    | _ -> None

def patternNamesOpt (pattern) = 
  case pattern of
    | VarPat((id,_),_) -> Some [id]
    | RecordPat(fields,_) ->
      List.foldl (fn ((_,p), namesOpt) ->
		  case namesOpt of
		    | Some names ->
		      (case patternNameOpt(p) of
			 | Some name -> Some (names ++ [name])
			 | _ -> None)
		    | _-> None)
                 (Some ([])) 
		 fields
     | _ -> None

op opDelta: Spec * Op -> List Var * Term

def opDelta(spc, oper) =
  let opDom = opDom(spc, oper) in
  let opRng = opRange(spc, oper) in
  let infos = findAllOps(spc, oper) in
  case infos of
    | info::_ ->
      (case opInfoDefs info of
	 | [dfn] ->
	   (let (tvs, srt, tm) = unpackTerm dfn in
	    case tm of
	      | Lambda ([(pat, cond, body)],_) ->
	        let argNames = patternNamesOpt pat in
		(case argNames of
		   | Some argNames ->
		     let numArgs = length argNames in
		     let arity   = length opDom    in
		     if arity = numArgs then
		       let newArgs = map (fn(id, srt) -> (id,srt)) (argNames, opDom) in
		       (newArgs, body)
		     else
		       let _ = unSupported(oper) in ([], mkFalse())
		   | _ -> let _ = unSupported(oper) in ([], mkFalse()))
	      | _ -> ([], tm))
	 | _ -> let _ = unSupported oper in ([], mkFalse()))
    | _ -> let _ = unSupported oper in ([], mkFalse())


% srtTermDelta defines the delta function in Alessandros document.
% (See Sec. 1.5 of DevDoc/java-codegen/v3.pdf)
% It takes a Lambda term and its sort and
% returns the list of arguments and the lambda body.
op srtTermDelta : Sort * Term -> List Var * Term
def srtTermDelta(srt,term) = srtTermDelta_internal(srt,term,false)

op srtTermDelta_internal: Sort * Term * Boolean-> List Var * Term
def srtTermDelta_internal(srt, term, fail?) =
  let opDom = srtDom(srt) in
  let opRng = srtRange(srt) in
  let
    def arityMismatchError(pat,args1,term,args2) = 
      "unsupported: pattern "^printPattern(pat)^" has "^Integer.toString(args1)^" args, but "
      ^printTerm(term)^" has "^Integer.toString(args2)^" args."
  in
  case term of
    | Lambda ([(pat, cond, body)],_) ->
    let argNames = patternNamesOpt(pat) in
    let arity = length(opDom) in
    (case argNames of
       | Some argNames ->
         (let numArgs = length argNames in
	  if arity = numArgs
	    then 
	      let newArgs = map (fn(id, srt) -> (id,srt)) (argNames, opDom) in
	      (newArgs, body)
	  else
	    if fail? then
	      fail(arityMismatchError(pat,numArgs,term,arity))
	    else ([],term)
	 )
       | _ -> 
	 if fail? then
	   fail(arityMismatchError(pat,0,term,arity))
	 else ([],term)
     )
    | _ -> ([], term)

op liftCaseTopCase: Op * (Term | caseTerm?) * Nat -> Term * Nat * List OpDef

def liftCaseTopCase(oper, body, k) =
  let b = termAnn(body) in
  let caseTerm = caseTerm(body) in
  let cases = caseCases(body) in
  let caseBodys = map (fn (pat, cond, patBody) -> patBody) cases in
  let (newCaseBodys, newK, newOds) = liftCases(oper, caseBodys, k) in
  let newCases = ListPair.map (fn ((pat, cond, _), (newPatBody)) -> (pat, cond, newPatBody)) (cases, newCaseBodys) in
  let newTerm = mkApply(Lambda (newCases, b), caseTerm) in
  let newTerm = withAnnT(newTerm,b) in
  (newTerm, newK, newOds)
  

op liftCase: Op * Term * Nat -> Term * Nat * List OpDef
op liftCaseCase: Op * (Term | caseTerm?) * Nat -> Term * Nat * List OpDef
op liftCaseApply: Op * Term * Nat -> Term * Nat * List OpDef
op liftCaseRecord: Op * Term * Nat -> Term * Nat * List OpDef
op liftCaseIfThenElse: Op * Term * Nat -> Term * Nat * List OpDef
op liftCaseLet: Op * Term * Nat -> Term * Nat * List OpDef

def liftCase(oper, term, k) =
  if caseTerm?(term) then liftCaseCase(oper, term, k) else
  case term of
    | Var _ -> (term, k, [])
    | Fun _ -> (term, k, [])
    | Apply (opTerm, argsTerm, _) -> liftCaseApply(oper, term, k)
    | Record _ -> liftCaseRecord(oper, term, k)
    | IfThenElse _ -> liftCaseIfThenElse(oper, term, k)
    | Let _ -> liftCaseLet(oper, term, k)
    | _ -> let _ = unSupported(oper) in (term, k, [])

def liftCaseApply(oper, term as Apply (opTerm, argsTerm, _), k) =
  let args = applyArgsToTerms(argsTerm) in
  let (newArgs, newK, newOds) = liftCases(oper, args, k) in
  (withAnnT(mkApplication(opTerm, newArgs),termAnn(term)), newK, newOds)


def liftCaseRecord(oper, term as Record (fields,_), k) =
  let recordTerms = recordFieldsToTerms(fields) in
  let (newTerms, newK, newOds) = liftCases(oper, recordTerms, k) in
  let newFields = map (fn ((id, _), newTerm) -> (id, newTerm)) (fields, newTerms) in
    (withAnnT(mkRecord(newFields),termAnn(term)), newK, newOds)

def liftCaseIfThenElse(oper, term as IfThenElse(t1, t2, t3, _), k) =
  let args = [t1, t2, t3] in
  let ([newT1, newT2, newT3], newK, newOds) = liftCases(oper, args, k) in
    (withAnnT(MS.mkIfThenElse(newT1, newT2, newT3),termAnn(term)), newK, newOds)

def liftCaseLet(oper, term as Let (letBindings, letBody, _), k) =
  case letBindings of
    | [(VarPat (v, _), letTerm)] ->
    let args = [letTerm, letBody] in
    let ([newLetTerm, newLetBody], newK, newOds) = liftCases(oper, args, k) in
    (withAnnT(mkLet([(mkVarPat(v), newLetTerm)], newLetBody),termAnn(term)), newK, newOds)
    | _ -> let _ = unSupported(oper) in (term, k, [])

def liftCaseCase(oper, term, k) =
  let b = termAnn(term) in
  let ttermSort = termSort(term) in
  let caseTerm = caseTerm(term) in
  let caseTermSort = termSort(caseTerm) in
  let (newCaseTerm, newK, newOds1) = liftCase(oper, caseTerm, k+1) in
  let cases = caseCases(term) in
  let caseBodys = map (fn (pat, cond, patBody) -> patBody) cases in
  let (newCaseBodys, finalK, newOds2) = liftCases(oper, caseBodys, newK) in
  let newCases = ListPair.map (fn ((pat, cond, _), (newPatBody)) -> (pat, cond, newPatBody)) (cases, newCaseBodys) in
  let freeVarsCases = List.foldr (fn (match,vs) -> vs ++ freeVarsMatch match) [] newCases in
  let freeVars = uniqueSort (fn ((id1, _), (id2, _)) -> compare(id1, id2)) freeVarsCases in
  let freeVarsSorts = map (fn(id, srt) -> srt) freeVars in
  let newOp = mkNewOp(oper, k) in
  let newOpSrt = withAnnS(mkArrow(mkProduct(cons(caseTermSort, freeVarsSorts)), ttermSort),b) in
  let newVar = mkNewVar(oper, k, caseTermSort) in
  let newOpTerm = withAnnT(mkApply(Lambda (newCases, b), mkVar(newVar)),b) in
  let newOpDef = (newOp, cons(caseTermSort,freeVarsSorts), ttermSort, cons(newVar, freeVars), newOpTerm) in
  let newTerm = withAnnT(mkApplication(mkOp(newOp, newOpSrt), cons(newCaseTerm, map mkVar freeVars)),b) in
  (newTerm, finalK, newOds1++newOds2++[newOpDef])
  
op liftCases: Op * List Term * Nat -> List Term * Nat * List OpDef

def liftCases(oper, terms, k) =
  case terms of
    | [] -> ([], k, [])
    | term::terms ->
    let (newTerm, newK, newOds) = liftCase(oper, term, k) in
    let (restTerms, restK, restOds) = liftCases(oper, terms, newK) in
    (cons(newTerm, restTerms), restK, newOds++restOds)

op lift: Spec * Op * (List Var * Term) -> Term * List OpDef

def lift(spc,oper, (formals, body)) =
  let firstUserVar = find (fn(v) -> userVar?(spc,v)) formals in
  case firstUserVar of
    | Some firstUserVar ->
    if caseTerm?(body)
      then
	case caseTerm(body) of
	  | Var (variable, _) ->
	  if equalVar?(variable, firstUserVar)
	    then 
	      let (newBody, newK, newOds) = liftCaseTopCase(oper, body, 1) in
	      (newBody, newOds)
	  else
	    let (newBody, newK, newOds) = liftCase(oper, body, 1) in
	    (newBody, newOds)
	  | _ -> let (newBody, newK, newOds) = liftCase(oper, body, 1)in
	    (newBody, newOds)
    else
      let (newBody, newK, newOds) = liftCase(oper, body, 1)in
      (newBody, newOds)
    | _ -> let (newBody, newK, newOds) = liftCase(oper, body, 1)in
      (newBody, newOds)

op liftPattern: Spec -> Spec

def liftPattern spc =
  let newOpDefs = foldriAQualifierMap 
                    (fn (q, id, info, result) ->
		     case opInfoDefs info of
		       | [dfn] ->
		         let (tvs, srt, term) = unpackTerm dfn in
			 let origOp = mkQualifiedId (q, id) in
			 let (origOpVars, origOpBody) = srtTermDelta (srt, term) in
			 let (newTerm, newOds) = lift(spc,origOp, (origOpVars, origOpBody)) in
			 let (origOpNewVars, origOpNewTerm) = srtTermDelta(srt, newTerm) in
			 let isConstantOp? = case srt of Arrow _ -> false | _ -> true in
			 let origOpNewDef = (origOp, srtDom(srt), srtRange(srt), origOpVars, newTerm) in
			 cons (origOpNewDef, newOds++result)
		       | _ -> result)
		    []
		    spc.ops 
  in
  let result = initialSpecInCat in % if we started instead with emptySpec, might we omit some built-in defs?
  let result = setSorts (result, spc.sorts) in
  let result = foldr addOpToSpec result newOpDefs in
   result

op addOpToSpec: OpDef * Spec -> Spec
def addOpToSpec((oper:Op, dom:(List Sort), rng:Sort, formals:List Var, body:Term), spc:Spec) =
  addOpToSpec2((oper,dom,rng,formals,body,false),spc)
   
op addOpToSpec2: OpDef2 * Spec -> Spec
def addOpToSpec2((oper as Qualified(q,id), dom:(List Sort), rng:Sort, formals:List Var, body:Term, isConstantOp?: Boolean), spc:Spec) =
  if basicQualifiedId? oper then
    spc
  else
  let srt = case dom of 
	      | [] -> if isConstantOp? then rng else mkArrow(mkProduct([]),rng)
	      | [dom] -> withAnnS(mkArrow(dom, rng),sortAnn(dom))
	      | _ -> mkArrow(mkProduct(dom), rng)
  in
  let varPatterns = map mkVarPat formals in
  let term = case varPatterns of
               | [] -> if isConstantOp? then body else mkLambda(mkTuplePat(varPatterns),body)
               | _ -> mkLambda(mkTuplePat(varPatterns), body)
  in
  %let (f, t) = srtTermDelta(srt, term) in
  %let _ = writeLine(";; addOpToSpec2: "^id^", bodyTerm=\n"^(printTerm body)) in
  run (addOp (oper, srt, term, spc))
   
def addOp (oper, srt, term, spc) : SpecCalc.Env Spec =
  let b = termAnn(term) in
  addOp [oper] Nonfix (SortedTerm (term, srt, noPos)) spc b
endspec
