(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MSToFM qualifying spec

  import FourierMotzkin
  import translate /Library/Structures/Data/Maps/SimpleAsAlist by {MapL._ +-> FMMap._}
  %import FMMap#FMMap
  import /Languages/MetaSlang/Specs/Utilities
  import /Languages/MetaSlang/Specs/StandardSpec
  %import /Library/Structures/Data/Maps/SimpleAsSTHarray
  %import /Library/Structures/Data/Maps/SimpleAsAlist
  %import /Library/Structures/Data/Maps/Polymorphic/AsLists
  import /Languages/MetaSlang/Transformations/OpToAxiom


  type BoolBinOp =
    | And
    | Or
    | Xor
    | Implies
    | Equiv

  type BoolUnOp =
    | Not

  type FMTerm =
    | Poly FM.Poly
    | Ineq FM.Ineq
    | IfThenElse FMTerm * FMTerm * FMTerm
    | BoolBinOp BoolBinOp * FMTerm * FMTerm
    | BoolUnOp BoolUnOp * FMTerm
    | LitBool Bool
    | UnSupported

  op zero: FMTerm
  def zero = Poly zeroPoly
  
  op printFMTerm: FMTerm -> String
  def printFMTerm(tm) =
    case tm of
      | Poly (p) -> printPoly(p)
      | Ineq (i) -> printIneq(i)
      | BoolBinOp (And,     t1, t2) -> printFMTerm(t1)^" && "^printFMTerm(t2)
      | BoolBinOp (Implies, t1, t2) -> printFMTerm(t1)^" => "^printFMTerm(t2)
      | BoolBinOp (Xor,     t1, t2) -> printFMTerm(t1)^" ^^ "^printFMTerm(t2)
      | BoolBinOp (Or,      t1, t2) -> printFMTerm(t1)^" || "^printFMTerm(t2)
      | BoolBinOp (Equiv,   t1, t2) -> printFMTerm(t1)^" <=> "^printFMTerm(t2)
      | _ -> (fail "UnSupported")

  op fmTrue: FMTerm
  def fmTrue = LitBool (true)

  op fmFalse: FMTerm
  def fmFalse = LitBool (false)
  
  type TransMap = FMMap.Map(MSTerm, FMTerm)

  type RevTransMap = FMMap.Map(FMTerm, MSTerm)

  type Context = {map: TransMap,
		  revMap: RevTransMap,
		  varCounter: Nat}

  op emptyToFMContext: Context
  def emptyToFMContext = {map = FMMap.emptyMap, revMap = FMMap.emptyMap, varCounter = 0}


  op proveMSProb: Spec * List Property * Property -> Bool
  def proveMSProb(spc, hyps, conc) =
    let context = emptyToFMContext in
    let (fmHyps, context) = toFMProperties(context, spc, hyps) in
    let (fmConc, context) = toFMProperty(context, spc, conc) in
    proveFMProb(fmHyps, fmConc)

(*
  op proveFMProb: List FMTerm * FMTerm -> Bool
  def proveFMProb(hyps, conc) =
    case conc of
      | BoolBinOp (Implies, fmTerm1, fmTerm2) ->
      let hyps = cons(fmTerm1, hyps) in
      let conc = fmTerm2 in
      proveFMProb(hyps, conc)
      | BoolBinOp(And, fmTerm1, fmTerm2) -> 
      let res1 = proveFMProb(hyps, fmTerm1) in
      if res1 then proveFMProb(hyps, fmTerm2) else false
      | _ ->
	let hyps = flattenHyps(hyps) in
	let negConcs = case conc of
			 | Ineq conc -> [negateIneq(conc)]
                         | _ -> [] in
	FMRefute?(negConcs++hyps)
*)

  op proveFMProb: List FMTerm * FMTerm -> Bool
  def proveFMProb(hyps, conc) =
    case conc of
      | BoolBinOp (Implies, fmTerm1, fmTerm2) ->
      let hyps = fmTerm1 :: hyps in
      let conc = fmTerm2 in
      proveFMProb(hyps, conc)

      | BoolBinOp (Or, fmTerm1, fmTerm2) ->
      let hyps = [fmNot(fmTerm1), fmNot(fmTerm2)]++hyps in
      let conc = LitBool false in
      proveFMProb(hyps, conc)

      | BoolBinOp(And, fmTerm1, fmTerm2) -> 
      let res1 = proveFMProb(hyps, fmTerm1) in
      if res1 then proveFMProb(hyps, fmTerm2) else false

      | BoolBinOp(Xor, fmTerm1, fmTerm2) ->
      let res1 = proveFMProb(hyps++[fmTerm1], fmNot(fmTerm2)) in
      if res1 then proveFMProb(hyps++[fmNot(fmTerm1)], fmTerm2) else false

      | BoolBinOp(Equiv, fmTerm1, fmTerm2) ->
      let res1 = proveFMProb(hyps++[fmTerm1], fmTerm2) in
      if res1 then proveFMProb(hyps++[fmTerm2], fmTerm1) else false

      | IfThenElse(cond, fmTerm1, fmTerm2) ->
      let res1 = proveFMProb(hyps++[cond], fmTerm1) in
      if res1 then proveFMProb(hyps++[fmNot(cond)], fmTerm2) else false

      | Ineq (Neq, poly) -> proveFMProb(hyps++[fmNot(conc)], LitBool false)

      | _ ->
	let hypsDisjunct = flattenAndSplitHyps(hyps) in
	let negConcs = case conc of
	                 | LitBool true -> [falseIneq]
			 | Ineq conc -> [negateIneq(conc)]
                         | _ -> [] in
	forall? (fn (hyps) -> FMRefuteTop?(negConcs++hyps)) hypsDisjunct

  op FMRefuteTop?: List Ineq -> Bool
  def FMRefuteTop?(ineqSet) =
    FMRefute?(ineqSet) = None

  op flattenAndSplitHyps: List FMTerm -> List (List FM.Ineq)
  def flattenAndSplitHyps(hyps) =
    case hyps of
      | [] -> [[]]
      | (LitBool true)::rest -> flattenAndSplitHyps(rest)
      | (LitBool false)::rest -> [[falseIneq]]
      | (BoolBinOp (Or, t1, t2))::rest -> flattenAndSplitHyps(t1 :: rest) ++ flattenAndSplitHyps(t2 :: rest)
      | (BoolBinOp (Implies, t1, t2))::rest -> flattenAndSplitHyps(Cons(BoolBinOp(Or, fmNot(t1), t2), rest))
      | (BoolBinOp (And, t1, t2))::rest -> flattenAndSplitHyps([t1, t2]++rest)
      | (BoolUnOp (Not, (BoolBinOp (Or, t1, t2))))::rest ->
        flattenAndSplitHyps(Cons(BoolBinOp (And, fmNot(t1), fmNot(t2)), rest))
      | (BoolUnOp (Not, Ineq (ineq)))::rest -> map (fn (hyps) -> Cons(negateIneq(ineq), hyps)) (flattenAndSplitHyps(rest))
      | (BoolBinOp(Xor, fmTerm1, fmTerm2))::rest ->
	let imp1 = BoolBinOp (Implies, fmTerm1, fmNot(fmTerm2)) in
	let imp2 = BoolBinOp (Implies, fmNot(fmTerm1), fmTerm2) in
	flattenAndSplitHyps(Cons(BoolBinOp (And, imp1, imp2), rest))
      | (BoolBinOp(Equiv, fmTerm1, fmTerm2))::rest ->
	let imp1 = BoolBinOp (Implies, fmTerm1, fmTerm2) in
	let imp2 = BoolBinOp (Implies, fmTerm2, fmTerm1) in
	flattenAndSplitHyps(Cons(BoolBinOp (And, imp1, imp2), rest))
      | (IfThenElse(cond, fmTerm1, fmTerm2))::rest ->
	let imp1 = BoolBinOp (Implies, cond, fmTerm1) in
	let imp2 = BoolBinOp (Implies, fmNot(cond), fmTerm2) in
	flattenAndSplitHyps(Cons(BoolBinOp (And, imp1, imp2), rest))
      | (Ineq (Eq, poly))::rest -> flattenAndSplitHyps([Ineq (mkNormIneq(GtEq, poly)), Ineq (mkNormIneq(LtEq, poly))]++rest)
      | (Ineq (ineq))::rest -> 
	if trueIneq? (ineq)
	  then flattenAndSplitHyps(rest)
	else map (fn (hyps) -> ineq :: hyps) (flattenAndSplitHyps(rest))
      | _::rest -> flattenAndSplitHyps(rest)

(*  op flattenHyps: List FMTerm -> List FM.Ineq
  def flattenHyps(hyps) =
    case hyps of
      | [] -> []
      | (BoolBinOp (And, t1, t2))::rest -> flattenHyps([t1, t2])++flattenHyps(rest)
      | (BoolUnOp (Not, (BoolBinOp (Or, t1, t2))))::rest ->
        flattenHyps(Cons(BoolBinOp (And, fmNot(t1), fmNot(t2)), rest))
      | (BoolUnOp (Not, Ineq (ineq)))::rest -> cons(negateIneq(ineq), flattenHyps(rest))
      | (Ineq (ineq))::rest -> cons(ineq, flattenHyps(rest))
      | _::rest -> flattenHyps(rest)
*)

  def fmBoolOps = ["&&", "||", "~", "=>", "<=>"]

  op fmInterp?: MSTerm -> Bool
  def fmInterp?(term) =
    case term of
      | Apply(Fun(f, srt, _), arg, _) ->
        (case f of
	   | Not -> fmInterp?(arg)
	   | _ -> fmInterpFun?(f))
      | _ -> false

  op fmInterpFun?: MSFun -> Bool
  def fmInterpFun?(f) =
    case f of
      | Op (Qualified (q, id), _) ->
      (case (q, id) of
	 | ("Nat",     "<=") -> true
	 | ("Integer", "<=") -> true
	 | ("Nat",     "<") -> true
	 | ("Integer", "<") -> true
	 | ("Nat",     ">=") -> true
	 | ("Integer", ">=") -> true
	 | ("Nat",     ">") -> true
	 | ("Integer", ">") -> true
	 | ("Nat",     "~") -> true
	 | ("Integer", "~") -> true
	 | ("Nat",     "-") -> true
	 | ("Integer", "-") -> true
	 | ("Nat",     "*") -> true
	 | ("Integer", "*") -> true
	 | ("Nat",     "+") -> true
	 | ("Integer", "+") -> true
	 | ("Nat",    "succ") -> true
	 | ("Integer","succ") -> true
	 | ("Integer", "natural?") -> true
	 | ("Nat", "natural?") -> true
	 | _ -> false)
       | Not     -> true
       | And     -> true
       | Or      -> true
       | Implies -> true
       | Iff     -> true
       | Equals  -> true
       | NotEquals  -> true
       | _ -> false

  op fmInterpFun: MSFun -> ((List FMTerm) -> FMTerm)
  def fmInterpFun(f) =
    case f of
      | Op (Qualified (q, id), _) ->
      (case (q, id) of
	 | ("Nat",     "<=")       -> (fn ([a1, a2]) -> fmLtEq(a1, a2))
	 | ("Integer", "<=")       -> (fn ([a1, a2]) -> fmLtEq(a1, a2))
	 | ("Nat",     "<")        -> (fn ([a1, a2]) -> fmLt(a1, a2))
	 | ("Integer", "<")        -> (fn ([a1, a2]) -> fmLt(a1, a2))
	 | ("Nat",     ">=")       -> (fn ([a1, a2]) -> fmGtEq(a1, a2))
	 | ("Integer", ">=")       -> (fn ([a1, a2]) -> fmGtEq(a1, a2))
	 | ("Nat",     ">")        -> (fn ([a1, a2]) -> fmGt(a1, a2))
	 | ("Integer", ">")        -> (fn ([a1, a2]) -> fmGt(a1, a2))
	 | ("Nat",     "~")        -> (fn ([a])      -> fmUMinus(a))
	 | ("Integer", "~")        -> (fn ([a])      -> fmUMinus(a))
	 | ("Nat",     "-")        -> (fn ([a1, a2]) -> fmMinus(a1, a2))
	 | ("Integer", "-")        -> (fn ([a1, a2]) -> fmMinus(a1, a2))
	 | ("Nat",     "+")        -> (fn ([a1, a2]) -> fmPlus(a1, a2))
	 | ("Integer", "+")        -> (fn ([a1, a2]) -> fmPlus(a1, a2))
	 | ("Nat",     "succ")     -> (fn ([a1])     -> fmPlus(a1, Poly onePoly))
	 | ("Integer", "succ")     -> (fn ([a1])     -> fmPlus(a1, Poly onePoly))
	 | ("Nat",     "*")        -> (fn ([a1, a2]) -> fmTimes(a1, a2))
	 | ("Integer", "*")        -> (fn ([a1, a2]) -> fmTimes(a1, a2))
	 | ("Integer", "natural?") -> (fn ([a])      -> fmNatural(a))
	 | ("Nat",     "natural?") -> (fn ([a])      -> fmNatural(a)))
       | Not       -> (fn ([a])      -> fmNot(a))
       | And       -> (fn ([a1, a2]) -> fmConjunct(a1, a2))
       | Or        -> (fn ([a1, a2]) -> fmDisjunct(a1, a2))
       | Implies   -> (fn ([a1, a2]) -> fmImpl(a1, a2))
       | Iff       -> (fn ([a1, a2]) -> fmEquiv(a1, a2))
       | Equals    -> (fn ([a1, a2]) -> fmEquals(a1, a2))
       | NotEquals -> (fn ([a1, a2]) -> fmNotEquals(a1, a2))

  op fmNot: FMTerm -> FMTerm
  def fmNot(tm) =
    case tm of
      | BoolUnOp (Not, tm) -> tm
      | BoolBinOp _ -> BoolUnOp (Not, tm)
      | Ineq (ineq) -> Ineq (negateIneq(ineq))
      | LitBool (x) -> LitBool (~ x)
      | _ -> BoolUnOp (Not, tm)

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

  op fmEquals: FMTerm * FMTerm -> FMTerm
  def fmEquals(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(Eq, p))
      | (LitBool true, t2) -> fmEquals(t2, Poly zeroPoly)
      | (t1, LitBool true) -> fmEquals(t1, Poly zeroPoly)
      | (LitBool false, t2) -> fmNot(fmEquals(t2, Poly zeroPoly))
      | (t1, LitBool false) -> fmNot(fmEquals(t1, Poly zeroPoly))
      | _ -> UnSupported

  op fmNotEquals: FMTerm * FMTerm -> FMTerm
  def fmNotEquals(t1, t2) =
    fmNot(fmEquals(t1, t2))

  op fmLtEq: FMTerm * FMTerm -> FMTerm
  def fmLtEq(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(LtEq, p))

  op fmLt: FMTerm * FMTerm -> FMTerm
  def fmLt(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(Lt, p))

  op fmGtEq: FMTerm * FMTerm -> FMTerm
  def fmGtEq(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(GtEq, p))

  op fmGt: FMTerm * FMTerm -> FMTerm
  def fmGt(t1, t2) =
    case (t1, t2) of
      | (Poly p1, Poly p2) ->
      let p = polyMinusPoly(p1, p2) in
      Ineq (mkNormIneq(Gt, p))

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

  op fmNatural: FMTerm -> FMTerm
  def fmNatural(t1) =
    fmGtEq(t1, zero)
  
  op reduceFMInterpOp: MSFun * List FMTerm -> FMTerm 
  def reduceFMInterpOp(f, args) =
    let interpFun = fmInterpFun(f) in
    interpFun args

  op toFMProperty: Context * Spec * Property -> FMTerm * Context
  def toFMProperty(context, spc, prop as (ptype, name, tyvars, fmla, _)) =
    let (fmTerm, newContext) = toFMTermTop(context, spc, fmla) in
%     let _ = writeLine("fmTransIn:") in
%     let _ = writeLine(printTerm(fmla)) in
%     let _ = writeLine("fmTransOut:") in
%     let _ = writeLine(printFMTerm(fmTerm)) in
%     let _ = debug("toFMProp") in
    (fmTerm, newContext)

  op toFMProperties: Context * Spec * List Property -> List FMTerm * Context
  def toFMProperties(context, spc, props) =
    case props of
      | [] -> ([], context)
      | p::restProps ->
      let (fmTerm, context) = toFMProperty(context, spc, p) in
      let (restFMTerms, context) = toFMProperties(context, spc, restProps) in
      (Cons(fmTerm, restFMTerms), context)

  op toFMTermTop: Context * Spec * MSTerm -> FMTerm * Context
  def toFMTermTop(context, sp, term) =
    case term of 
      | Bind(Forall, bndVars, term, _) ->
	let fmBndList = fmBndVars bndVars in
	let bndVarsPred : MSTerm = 
            (foldl (fn (res, (var:Id, srt)) -> 
                      Utilities.mkAnd(srtPred(sp, srt, mkVar((var, srt))), 
                                      res)) 
                   (mkTrue())
                   (bndVars: MSVars)) : MSTerm 
        in
	let newTerm = Utilities.mkSimpImplies(bndVarsPred, term) in
	let (fmFmla, newContext) = toFMTerm(context, sp, newTerm) in
	(fmFmla, newContext)
      | _ -> toFMTerm(context, sp, term)


  op toFMTerm: Context * Spec * MSTerm -> FMTerm * Context
  def toFMTerm(context, sp, term) =
    let term = cleanTerm(term) in
    let found = FMMap.apply(context.map, term) in
    case found of
      | Some fmTerm -> (fmTerm, context)
      | _ -> 
    let (resTerm, newContext) =
    case term of 
      (* | Bind(Forall, bndVars, term, _) ->
	let fmBndList = fmBndVars bndVars in
	let bndVarsPred:MSTerm = (foldl (fn (res, (var:Id, srt)) -> Utilities.mkAnd(srtPred(sp, srt, mkVar((var, srt))), res)) (mkTrue()) (bndVars: MSVars)):MSTerm in
	let newTerm = Utilities.mkSimpImplies(bndVarsPred, term) in
	let (fmFmla, newContext) = toFMTerm(context, sp, newTerm) in
	(fmFmla, newContext)
	*)
      | Apply(Fun(f, srt, _), arg, _) ->
	let (resTerm, newContext) = toFMTermApp(context, sp, term, f, srt, arg) in
	(resTerm, newContext)
      | Fun ((Bool true), Boolean(_), _) -> (fmTrue, context)
      | Fun ((Bool false), Boolean(_), _) -> (fmFalse, context)
      | Fun (Nat (n) ,_,_) -> (Poly (mkConstantPoly(intToRat(n))), context)
      | Fun(f, srt, _) -> toFMTermConstant(context, term, f)
      | Var (v, _) -> toFMVar(context, sp, v)
      | _ -> let (newVar, newContext) = toNewFMVar(term, context) in (newVar, newContext) in
    let map = FMMap.update(newContext.map, term, resTerm) in
    let revMap = FMMap.update(newContext.revMap, resTerm, term) in
    let newContext = {map = map, revMap = revMap, varCounter = newContext.varCounter} in
    %let _ = writeLine("Entering toFMTerm with: "^printTerm(term)) in
    %let _ = writeLine("Length of new Map: "^natToString(length(map))) in
    (* let _ = case FMMap.apply(newContext.map, term) of
              | Some f -> writeLine("Found in new context."^printFMTerm(f))
              | _ -> fail("Not found in new context.") in
    let _ = writeLine("Exiting toFMTerm with: "^printFMTerm(resTerm)) in
     *)
    (resTerm, newContext)

  op toFMTermApp:  Context * Spec * MSTerm * MSFun * MSType * MSTerm -> FMTerm * Context
  def toFMTermApp(cntxt, spc, term, f, _, arg) =
    let args = case arg of
                 | Record(flds,_) -> map(fn (_, term) -> term) flds
	         | _ -> [arg] in
    if fmInterp?(term)
      then 
	let (fmArgs, cntxt) = toFMTerms(spc, args, cntxt) in
	let reducedTerm = reduceFMInterpOp(f, fmArgs) in
	case reducedTerm of
	  | UnSupported -> toNewFMVar(term, cntxt)
	  | _ -> (reducedTerm, cntxt)
    else 
      let (resPoly, context) =
        case args of 
	  | [] -> toFMTermConstant(cntxt, term, f)
	  | _ -> let (newVar, newContext) = toNewFMVar(term, cntxt) in (newVar, newContext) in
      if termType(term) = boolType
	then (fmEquals(resPoly, fmTrue), context)
      else (resPoly, context)


  op toFMVar:  Context * Spec * MSVar -> FMTerm * Context
  def toFMVar (context, spc, var as (v, s)) =
    (Poly (mkPoly1(mkMonom(one, v))), context)

  op fmBndVars: MSVars -> List FMTerm
  def fmBndVars vars =
    let fmVarList = map (fn (v, s) -> Poly (mkPoly1(mkMonom(one, v)))) vars in
      fmVarList

  op toFMTermConstant: Context * MSTerm * MSFun -> FMTerm * Context
  def toFMTermConstant(cntxt, term, f) =
    let resTerm = 
    case f of
      | Op (qid, _) -> Poly (mkPoly1(mkMonom(one, printQualifiedId(qid)^"$C")))
      | _ -> UnSupported in
    let map = FMMap.update(cntxt.map, term, resTerm) in
    let revMap = FMMap.update(cntxt.revMap, resTerm, term) in
    let context = {map = map, revMap = revMap, varCounter = cntxt.varCounter} in
    (resTerm, context)

  op toNewFMVar: MSTerm * Context -> FMTerm * Context
  def toNewFMVar(term, context) =
    %let _ = fail(printTerm(term)) in
    let (newVar, context) = mkNewFMVar(context) in
    let resTerm = Poly (mkPoly1(mkMonom(one, newVar))) in
    let map = FMMap.update(context.map, term, resTerm) in
    let revMap = FMMap.update((context.revMap), resTerm, term) in
    let context = {map = map, revMap = revMap, varCounter = context.varCounter} in
    (resTerm, context)

  op mkNewFMVar: Context -> FM.Var * Context
  def mkNewFMVar(context) =
    let varCounter = context.varCounter in
    let newVar = "fmVar_"^natToString(varCounter) in
    let context = {map = context.map, revMap = context.revMap, varCounter = varCounter+1} in
    (newVar, context)

  op toFMTerms: Spec * MSTerms * Context -> (List FMTerm) * Context
  def toFMTerms(spc, terms, context) =
    case terms of
      | [] -> ([], context)
      | t::restTerms ->
      let (fmTerm, context) = toFMTerm(context, spc, t) in
      let (restFMTerms, context) = toFMTerms(spc, restTerms, context) in
      (Cons(fmTerm, restFMTerms), context)

  op fromFMTerm: Spec * FMTerm * Context -> MSTerm
  def fromFMTerm(spc, fmtm, context) =
    case fmtm of
      | Poly poly -> fromFMTermPoly(spc, poly, context)
      | Ineq ineq -> fromFMTermIneq(spc, ineq, context)
      | BoolBinOp(bbop, t1, t2) -> fromFMTermBoolBinOp(spc, bbop, t1, t2, context)
      | BoolUnOp(buop, t1) -> fromFMTermBoolUnOp(spc, buop, t1, context)

  op fromFMTermPoly: Spec * FM.Poly * Context -> MSTerm
  def fromFMTermPoly(spc, p, context) =
    if zeroPoly?(p) then mkNat(0)
    else case p of
      | [tm] -> fromFMTermTerm(tm, context)
      | hdTm::rp -> mkAddition(fromFMTermTerm(hdTm, context),
			       fromFMTermPoly(spc, rp, context))

  op mkAddition: MSTerm * MSTerm -> MSTerm
  def mkAddition(t1, t2) =
    let addOp = mkInfixOp(mkQualifiedId("Integer", "+"), Infix (Left, 25),
			  mkArrow(mkProduct([intType, intType]), intType)) in
    mkApplication(addOp, [t1, t2])

  op fromFMTermIneq: Spec * FM.Ineq * Context -> MSTerm
  def fromFMTermIneq(spc, ineq, context) =
    let def compToQid(comp) =
          case comp of
	    | Gt   -> mkQualifiedId("Integer",">")
	    | Lt   -> mkQualifiedId("Integer","<")
	    | GtEq -> mkQualifiedId("Integer",">=")
	    | LtEq -> mkQualifiedId("Integer","<=")
	    | Eq   -> mkQualifiedId("Integer","=")
	    | Neq  -> mkQualifiedId("Integer","~=")
    in
    let def fromFMComp(comp) =
          let srt = mkArrow(mkProduct([intType, intType]), boolType) in
          mkInfixOp(compToQid(comp), Infix (Left, 20), srt) in
    let (comp, p) = ineq in
    let MSP = fromFMTermPoly(spc, p, context) in
    let compOp = fromFMComp(comp) in
    mkApply(compOp, MSP)

  op fromFMTermTerm: FM.Term * Context -> MSTerm
  def fromFMTermTerm(tm, context) =
    case tm of
      | Constant coef -> mkInt(ratToInt(coef))
      | Monom (coef, var) ->
        if coef = one then fromFMTermVar(var, context)
	else
	  let coefTerm = mkInt(ratToInt(coef)) in
	  let varTerm = fromFMTermVar(var, context) in
	  mkMult(coefTerm, varTerm)

op fromFMTermVar: FM.Var * Context -> MSTerm
  def fromFMTermVar(var, context) =
    let revMap = context.revMap in
    case FMMap.apply(revMap, Poly (mkPoly1(mkMonom(one, var)))) of
      | Some MSTerm -> MSTerm
      | _ -> fail("Shouldnt happen.")

  op mkMult: MSTerm * MSTerm -> MSTerm
  def mkMult(t1, t2) =
    let multOp = mkInfixOp(mkQualifiedId("Integer", "*"), Infix (Left, 27),
			   mkArrow(mkProduct([intType, intType]), intType)) in
    mkApplication(multOp, [t1, t2])
  
  op fromFMTermBoolBinOp: Spec * BoolBinOp * FMTerm * FMTerm * Context -> MSTerm
  def fromFMTermBoolBinOp(spc, bop, t1, t2, context) =
    let msT1 = fromFMTerm(spc, t1, context) in
    let msT2 = fromFMTerm(spc, t2, context) in
    case bop of
      | And -> Utilities.mkAnd(msT1, msT2)
      | Or -> Utilities.mkOr(msT1, msT2)
      | Implies -> mkSimpImplies(msT1, msT2)
      | Equiv -> mkSimpIff(msT1, msT2)

  op fromFMTermBoolUnOp: Spec * BoolUnOp * FMTerm * Context -> MSTerm
  def fromFMTermBoolUnOp(spc, uop, t1, context) =
    let msT1 = fromFMTerm(spc, t1, context) in
    case uop of
      | Not -> negateTerm(msT1)

  op simpTerm: Spec -> MSTerm -> MSTerm
  def simpTerm spc term =
    let context = emptyToFMContext in
    case term of
      | Apply _ ->
        let (fmTerm, context) = toFMTerm(context, spc, term) in
	let res = fromFMTerm(spc, fmTerm, context) in
	let _ = if fmInterp?(term) then writeLine("FMSimpEnter: "^printTerm(term)) else () in
	let _ = if fmInterp?(term) then writeLine("FMSimpReturn: "^printTerm(res)) else () in
	let _ = if fmInterp?(term) then writeLine("") else () in
	res
      | _ -> term

  op simpSpecFMTerm: Spec -> Spec
  def simpSpecFMTerm(spc) =
    mapSpec (simpTerm spc, fn s -> s, fn p -> p) spc

  op cleanTerm: MSTerm -> MSTerm
  def cleanTerm(t) =
    mapTerm (remPosT, remPosS, remPosP) t

  op remPosT: MSTerm -> MSTerm
  def remPosT(t) =
    withAnnT(t, noPos)

  op remPosS: MSType -> MSType
  def remPosS(s) =
    withAnnS(s, noPos)

  op remPosP: MSPattern -> MSPattern
  def remPosP(p) =
    withAnnP(p, noPos)

endspec
