MSToFM qualifying spec

  import FourierMotzkin
  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/Specs/StandardSpec
  import /Library/Structures/Data/Maps/SimpleAsSTHarray
  import /Languages/MetaSlang/Transformations/OpToAxiom


  sort BoolBinOp =
    | And
    | Or
    | Implies
    | Equiv

  sort BoolUnOp =
    | Not

  sort FMTerm =
    | Poly FM.Poly
    | Ineq FM.Ineq
    | BoolBinOp BoolBinOp * FMTerm * FMTerm
    | BoolUnOp BoolUnOp * FMTerm
    | UnSupported

  op printFMTerm: FMTerm -> String
  def printFMTerm(tm) =
    case tm of
      | Poly (p) -> printPoly(p)
      | Ineq (i) -> printIneq(i)
      | BoolBinOp (And, t1, t2) -> printFMTerm(t1)^" & "^printFMTerm(t2)
      | _ -> "UnSupported"

  sort TransMap = Map.Map(MS.Term, FMTerm)

  sort Context = {map: TransMap,
		  varCounter: Nat}

  op emptyToFMContext: Context
  def emptyToFMContext = {map = MapSTHashtable.emptyMap, varCounter = 0}


  op proveMSProb: Spec * List Property * Property -> Boolean
  def proveMSProb(spc, hyps, conc) =
    let context = emptyToFMContext in
    let (fmHyps, context) = toFMProperties(context, spc, hyps) in
    let (fmConc, context) = toFMProperty(context, spc, conc) in
    proveFMProb(fmHyps, fmConc)

  op proveFMProb: List FMTerm * FMTerm -> Boolean
  def proveFMProb(hyps, conc) =
    case conc of
      | BoolBinOp(And, fmTerm1, fmTerm2) -> 
      let res1 = proveFMProb(hyps, fmTerm1) in
      if res1 then proveFMProb(hyps, fmTerm2) else false
      | _ ->
	let hyps = mapPartial (fn (Ineq ineq)  -> Some ineq
                                  | _ -> None) hyps in
	let negConcs = case conc of
			 | Ineq conc -> [negateIneq(conc)]
                         | _ -> [] in
	FMRefute?(negConcs++hyps)

  def fmBoolOps = ["&", "or", "~", "=>", "<=>"]

  op fmInterp?: Fun -> Boolean
  def fmInterp?(f) =
    case f of
      | Op (Qualified (q, id), _) ->
      (case (q, id) of
	 | ("Nat",     "<=") -> true
	 | ("Integer", "<=") -> true
	 | ("Nat",     ">=") -> true
	 | ("Integer", ">=") -> true
	 | ("Nat",     "~") -> true
	 | ("Integer", "~") -> true
	 | ("Nat",     "-") -> true
	 | ("Integer", "-") -> true
	 | ("Nat",     "*") -> true
	 | ("Integer", "*") -> true
	 | _ -> false)
       | Not     -> true
       | And     -> true
       | Or      -> true
       | Implies -> true
       | Iff     -> true
       | _ -> false

  op fmInterpFun: Fun -> ((List FMTerm) -> FMTerm)
  def fmInterpFun(f) =
    case f of
      | Op (Qualified (q, id), _) ->
      (case (q, id) of
	 | ("Nat",     "<=") -> (fn ([a1, a2]) -> fmLtEq(a1, a2))
	 | ("Integer", "<=") -> (fn ([a1, a2]) -> fmLtEq(a1, a2))
	 | ("Nat",     ">=") -> (fn ([a1, a2]) -> fmGtEq(a1, a2))
	 | ("Integer", ">=") -> (fn ([a1, a2]) -> fmGtEq(a1, a2))
	 | ("Nat",     "~") -> (fn ([a]) -> fmUMinus(a))
	 | ("Integer", "~") -> (fn ([a]) -> fmUMinus(a))
	 | ("Nat",     "-") -> (fn ([a1, a2]) -> fmMinus(a1, a2))
	 | ("Integer", "-") -> (fn ([a1, a2]) -> fmMinus(a1, a2))
	 | ("Nat",     "+") -> (fn ([a1, a2]) -> fmPlus(a1, a2))
	 | ("Integer", "+") -> (fn ([a1, a2]) -> fmPlus(a1, a2))
	 | ("Nat",     "*") -> (fn ([a1, a2]) -> fmTimes(a1, a2))
	 | ("Integer", "*") -> (fn ([a1, a2]) -> fmTimes(a1, a2)))
       | Not     -> (fn ([a]) -> fmNot(a))
       | And     -> (fn ([a1, a2]) -> fmConjunct(a1, a2))
       | Or      -> (fn ([a1, a2]) -> fmDisjunct(a1, a2))
       | Implies -> (fn ([a1, a2]) -> fmImpl(a1, a2))
       | Iff     -> (fn ([a1, a2]) -> fmEquiv(a1, a2))

  op fmNot: FMTerm -> FMTerm
  def fmNot(tm) =
    case tm of
      | BoolUnOp (Not, tm) -> tm
      | BoolBinOp _ -> BoolUnOp (Not, tm)
      | Ineq (ineq) -> Ineq (negateIneq(ineq))


  op fmConjunct: FMTerm * FMTerm -> FMTerm
  def fmConjunct(t1, t2) =
    BoolBinOp (And, t1, t2)

  op fmDisjunct: FMTerm * FMTerm -> FMTerm
  def fmDisjunct(t1, t2) =
    BoolBinOp (Or, t1, t2)

  op fmImpl: FMTerm * FMTerm -> FMTerm
  def fmImpl(t1, t2) =
    BoolBinOp (Implies, t1, t2)

  op fmEquiv: FMTerm * FMTerm -> FMTerm
  def fmEquiv(t1, t2) =
    BoolBinOp (Equiv, t1, t2)

  op fmLtEq: FMTerm * FMTerm -> FMTerm
  def fmLtEq(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(LtEq, p))

  op fmGtEq: FMTerm * FMTerm -> FMTerm
  def fmGtEq(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(GtEq, p))

  op fmUMinus: FMTerm -> FMTerm
  def fmUMinus(t) =
    case t of
      | Poly(p) -> Poly (negateSum(p))
      | _ -> UnSupported

  op fmMinus: FMTerm * FMTerm -> FMTerm
  def fmMinus(t1, t2) =
    case (t1, t2) of
      | (Poly(p1), Poly(p2)) -> Poly (polyMinusPoly(p1, p2))
      | _ -> UnSupported

  op fmPlus: FMTerm * FMTerm -> FMTerm
  def fmPlus(t1, t2) =
    case (t1, t2) of
      | (Poly(p1), Poly(p2)) -> Poly (polyPlusPoly(p1, p2))
      | _ -> UnSupported

  op fmTimes: FMTerm * FMTerm -> FMTerm
  def fmTimes(t1, t2) =
    case (t1, t2) of
      | (Poly (p1), Poly(p2)) ->
      if constantPoly?(p1) then Poly (constantPolyTimesPoly(p1, p2))
      else if constantPoly?(p2) then Poly (constantPolyTimesPoly(p2, p1))
	   else  UnSupported
      | _ -> UnSupported

  op reduceFMInterpOp: Fun * List FMTerm -> FMTerm 
  def reduceFMInterpOp(f, args) =
    let interpFun = fmInterpFun(f) in
    interpFun args

  op toFMProperty: Context * Spec * Property -> FMTerm * Context
  def toFMProperty(context, spc, prop as (ptype, name, tyvars, fmla)) =
    let (fmTerm, newContext) = toFMTerm(context, spc, fmla) in
    let _ = writeLine("fmTransIn:") in
    let _ = writeLine(printTerm(fmla)) in
    let _ = writeLine("fmTransOut:") in
    let _ = writeLine(printFMTerm(fmTerm)) in
    (fmTerm, newContext)

  op toFMProperties: Context * Spec * List Property -> List FMTerm * Context
  def toFMProperties(context, spc, props) =
    case props of
      | [] -> ([], context)
      | p::restProps ->
      let (fmTerm, context) = toFMProperty(context, spc, p) in
      let (restFMTerms, context) = toFMProperties(context, spc, restProps) in
      (Cons(fmTerm, restFMTerms), context)

  op toFMTerm: Context * Spec * MS.Term -> FMTerm * Context
  def toFMTerm(context, sp, term) =
    case term of 
      | Bind(Forall, bndVars, term, _) ->
	let fmBndList = fmBndVars(sp, bndVars) in
	let bndVarsPred:MS.Term = (foldl (fn ((var:Id, srt), res) -> Utilities.mkAnd(srtPred(sp, srt, mkVar((var, srt))), res)) (mkTrue()) (bndVars:(List MS.Var))):MS.Term in
	let newTerm = Utilities.mkSimpImplies(bndVarsPred, term) in
	let (fmFmla, newContext) = toFMTerm(context, sp, newTerm) in
	(fmFmla, newContext)
      | Apply(Fun(f, srt, _), arg, _) -> toFMTermApp(context, sp, term, f, srt, arg)
%      | Fun ((Bool true), Boolean, _) -> fmTrue
%      | Fun ((Bool false), Boolean, _) -> fmFalse
      | Fun (Nat (n) ,_,_) -> (Poly (mkConstantPoly(n)), context)
      | Fun(f, srt, _) -> toFMTermConstant(context, sp, term, f)
      | Var (v, _) -> toFMVar(context, sp, v)
      | _ -> let (newVar, newContext) = toNewFMVar(term, context) in (newVar, newContext)


  op toFMTermApp:  Context * Spec * MS.Term * Fun * Sort * MS.Term -> FMTerm * Context
  def toFMTermApp(cntxt, spc, term, f, srt, arg) =
    let args = case arg of
                 | Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    if fmInterp?(f)
      then 
	let (fmArgs, cntxt) = toFMTerms(spc, args, cntxt) in
	(reduceFMInterpOp(f, fmArgs), cntxt)
    else 
      case args of 
	| [] -> toFMTermConstant(cntxt, spc, term, f)
	| _ -> let (newVar, newContext) = toNewFMVar(term, cntxt) in (newVar, newContext)

  op toFMVar:  Context * Spec * MS.Var -> FMTerm * Context
  def toFMVar (context, spc, var as (v, s)) =
    (Poly (mkPoly1(mkMonom(1, v))), context)

  op fmBndVars: Spec * List MS.Var -> List FMTerm
  def fmBndVars(sp, vars) =
    let fmVarList = map (fn (v, s) -> Poly (mkPoly1(mkMonom(1, v)))) vars in
      fmVarList

  op toFMTermConstant: Context * Spec * MS.Term * Fun -> FMTerm * Context
  def toFMTermConstant(cntxt, spc, term, f) =
    let resTerm = 
    case f of
      | Op (qid, _) -> Poly (mkPoly1(mkMonom(1, printQualifiedId(qid)^"$C")))
      | _ -> UnSupported in
    let map = MapSTHashtable.update(cntxt.map, term, resTerm) in
    let context = {map = map, varCounter = cntxt.varCounter} in
    (resTerm, context)
	

  op toNewFMVar: MS.Term * Context -> FMTerm * Context
  def toNewFMVar(term, context) =
    let (newVar, context) = mkNewFMVar(context) in
    let resTerm = Poly (mkPoly1(mkMonom(1, newVar))) in
    let map = MapSTHashtable.update(context.map, term, resTerm) in
    let context = {map = map, varCounter = context.varCounter} in
    (resTerm, context)

  def mkNewFMVar(context) =
    let varCounter = context.varCounter in
    let newVar = "fmVar_"^natToString(varCounter) in
    let context = {map = context.map, varCounter = varCounter+1} in
    (newVar, context)


  op toFMTerms: Spec * List MS.Term * Context -> (List FMTerm) * Context
  def toFMTerms(spc, terms, context) =
    case terms of
      | [] -> ([], context)
      | t::restTerms ->
      let (fmTerm, context) = toFMTerm(context, spc, t) in
      let (restFMTerms, context) = toFMTerms(spc, restTerms, context) in
      (Cons(fmTerm, restFMTerms), context)


endspec