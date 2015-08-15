%%% Simple interpreter for MetaSlang. Assume type-correct term. If it evaluate a term
%%% it just returns the term.

MSInterpreter qualifying
spec
  import ../Specs/Environment
  import ../Specs/Utilities
  import /Languages/Lisp/Suppress

  type Subst = List (Id * MSIValue)

  type MSIValue =
    | Int         Int
    | Char        Char
    | String      String
    | Bool        Bool
    | RecordVal   Subst
    | Constructor QualifiedId * MSIValue * MSType
    | Constant    QualifiedId * MSType
    | QuotientVal MSIValue * MSIValue	* QualifiedId	% closure * element * type id
    | ChooseClosure MSIValue * MSType * QualifiedId
    | Closure     MSMatch * Subst
    | RecClosure  MSMatch * Subst * List Id
    | Unevaluated MSTerm

  op equalValue?(v1: MSIValue, v2: MSIValue): Option Bool =
    case (v1,v2) of
      | (Int n1, Int n2) -> Some(n1 = n2)
      | (Char ch1, Char ch2) -> Some(ch1 = ch2)
      | (String str1, String str2) -> Some(str1 = str2)
      | (Bool b1, Bool b2) -> Some(b1 = b2)
      | (RecordVal sb1, RecordVal sb2) ->
        if length sb1 = length sb2
          then
            foldl (fn (val, ((id1,v1),(id2,v2))) ->
                    case val of
                      | None -> None
                      | Some false -> val
                      | _ ->
                   if id1 = id2 then equalValue?(v1, v2) else Some false)
              (Some true)  (zip(sb1,sb2))
        else Some false
      | (Constructor(id1,v1,_), Constructor(id2,v2,_)) ->
        if id1 = id2 then equalValue?(v1,v2) else None
      | (Constant(id1,_), Constant(id2,_)) -> Some(id1 = id2)
      | (Unevaluated(t1),Unevaluated(t2)) -> if equalTermAlpha?(t1,t2) then Some true else None
      | (Closure(match1, sb1),  Closure(match2, sb2)) ->
        if equalMatch_alpha? [] (match1, match2) true && sb1 = sb2
          then Some true else None
      %% Should have special cases for QuotientVal ChooseClosure Closure RecClosure
      | _ -> if v1 = v2 then Some true else None

  op  unevaluated?: MSIValue -> Bool
  def unevaluated? x = embed? Unevaluated x

  op  emptySubst: Subst
  def emptySubst = []

  op lookup: Subst * Id -> Option MSIValue
  def lookup(sbst,v) =
    case sbst of
      | [] -> None
      | (vi,vali)::rsbst ->
	if vi = v then Some vali else lookup(rsbst,v)

  op  addToSubst: Subst * Id * MSIValue -> Subst
  def addToSubst(sb,v,t) = Cons((v,t),sb)

%%% --------------------
  op  eval: MSTerm * Spec -> MSIValue
  def eval(t,spc) = evalRec(t,emptySubst,spc,0,traceEval?)

  op evalFullyReducibleSubTerms(t: MSTerm,spc: Spec): MSTerm =
    mapSubTerms (fn st ->
                 if ~(constantTerm? st)
                   then
                     let v = eval(st,spc) in
                     if fullyReduced? v
                       then valueToTerm v
                       else st
                   else st)
      t

  op partialEval(t: MSTerm,spc: Spec): MSTerm =
    valueToTerm(eval(t,spc))

  op  traceEval?: Bool
  def traceEval? = false

  op doneTraceOps: Ids = []
  op dontTraceQualifiers: Ids = []

  op  traceable?: MSTerm -> Bool
  def traceable? t =
    case t of
      %| Var _ -> false
      | Fun _ -> false
      | Lambda _ -> false
      | Record (("1", _)::_,_) -> false
      | Apply(Lambda _, _, _) -> false
      | Apply(Fun(Embed(nm,_),_,_), _, _) -> false
      | Apply(Fun(Op(qid as Qualified(q, id), _), ty, _), _, _) ->
        ~(id in? doneTraceOps || q in? dontTraceQualifiers)
      | _ -> true

  op  preTrace: MSTerm * Nat * Bool -> ()
  def preTrace(t,depth,trace?) =
    if traceEval? && trace? && traceable? t then
      let _ = toScreen (blanks depth) in
      case t of
	| Var _ ->
	  let _ = printTermToTerminal t in
	  let _ = toScreen ": " in
	  ()
	| _ ->
	  let _ = toScreen ((show depth)^"< ") in
	  let _ = printTermToTerminal t in
	  let _ = toScreen newline in
	  ()
    else ()
    
  op  postTrace: MSTerm * MSIValue * Nat * Bool -> ()
  def postTrace(t,val,depth,trace?) =
    if traceEval? && trace? && traceable? t then
      case t of
	| Var _ ->
	  let _ = printMSIValue (val,false) in
	  let _ = toScreen newline in
	  ()
	| _ ->
	  let _ = toScreen (blanks depth) in
	  let _ = toScreen ((show depth)^"> ") in
	  let _ = printMSIValue (val,false) in
	  let _ = toScreen newline in
	  ()
    else ()

  op traceWithinFns: List String = []
  op noTraceWithinFns: List String = ["length", "in?", "**", "***", "reverse"]
  
  op fnMember?(f: MSTerm, fns: List String): Bool =
    fns ~= [] &&
    (case f of
      | Fun(Op(qid as Qualified(spName,opName),_),_,_) ->
        opName in? fns || printQualifiedId qid in? fns
      | Apply(f, _, _) -> fnMember?(f, fns)
      | _ -> false)

  op  evalRec: MSTerm * Subst * Spec * Nat * Bool -> MSIValue
  def evalRec(t,sb,spc,depth,trace?) =
    let _ = preTrace(t,depth,trace?) in
    let depth = if traceable? t then depth else depth -1 in
    let val = 
	case t of
	  | Var((v,_),_) ->
	    (case lookup(sb,v) of
	      | Some e -> e
	      | None -> Unevaluated t)
	  | Fun(fun,ty,_) -> evalFun(fun,t,ty,sb,spc,depth,trace?)
	  | Apply(Fun(Op(Qualified("System","time"),_),_,_),y,_) -> timeEvalRec(y,sb,spc,depth+1,trace?)
	  | Apply(x,y,_) ->
	    if nonStrict? x
	      then evalApplyNonStrict(x,y,sb,spc,depth,trace?)
	      else
                let trace_fn? = if trace? then ~(fnMember?(x, noTraceWithinFns))
                                 else fnMember?(x, traceWithinFns)
                in
                evalApply(evalRec(x,sb,spc,depth+1,trace?),
                          evalRec(y,sb,spc,depth+1,trace?),
                          sb,spc,depth,trace_fn?)
	  | Record(fields,a) ->
	    RecordVal(map (fn(lbl,e) -> (lbl,evalRec(e,sb,spc,depth+1,trace?))) fields)
	  | IfThenElse(P,M,N,a) ->
	    (case evalRec(P,sb,spc,depth+1,trace?) of
	      | Bool true  -> evalRec(M,sb,spc,depth+1,trace?)
	      | Bool false -> evalRec(N,sb,spc,depth+1,trace?)
	      | Unevaluated nP -> Unevaluated (IfThenElse(nP,M,N,a))
	      | _ -> Unevaluated t)
	  | Lambda(match,_) -> Closure(match, sb)
	  | Seq(tms,_) -> (map (fn s -> evalRec(s,sb,spc,depth+1,trace?)) tms) @ (length tms - 1)
	  | Let(decls, body, a) ->
	    (let rdecls = map (fn (pat,e) -> (pat,evalRec(e,sb,spc,depth+1,trace?))) decls in
	     case foldl (fn (ssb,(pat,e)) ->
			  case ssb of
			    | Some sbr ->
			      %% The e are evaluated in the outer environment (sb not sbr)
			      (case patternMatch(pat,e,sbr,true,spc,depth,trace?) of
				 | Match S -> Some S
				 | _ -> None)
			    | None -> None)
		   (Some sb) rdecls
	       of Some newsb -> maybeMkLetOrSubst(evalRec(body,newsb,spc,depth+1,trace?),newsb,sb)
		| None -> Unevaluated (Let(map (fn (pat,e) -> (pat,valueToTerm e)) rdecls, body, a)))
	  | LetRec(decls, body, _) ->
	    let ids = reverse(map (fn ((v,_),_) -> v) decls) in
	    (case foldl (fn (ssb,((v,_),e)) ->
			 case ssb of
			   | Some nsb ->
			     Some(addToSubst(nsb,v,
					     case evalRec(e,sb,spc,depth+1,trace?) of
					       | Closure(m,sbc) ->
						 RecClosure(m,sb,ids)
					       | v -> v))
			   | None -> ssb)
		   (Some sb) decls
	       of Some sb ->
		  (case evalRec(body,sb,spc,depth+1,trace?) of
		     | Unevaluated t1 ->
		       if exists? (fn (id,_) -> id in? ids) (freeVars t)
		        then Unevaluated(mkLetRec(decls,t1))
			else Unevaluated t1
		     | v -> v)
		| None -> Unevaluated t)

	  % ? | Bind()
	  | _ -> Unevaluated t
    in
    let _ = postTrace(t,val,depth,trace?) in
    val

 
  op  evalFun: MSFun * MSTerm * MSType * Subst * Spec * Nat * Bool -> MSIValue
  def evalFun(fun,t,ty,sb,spc,depth,trace?) =
    case fun of
      | Op (qid, _) ->
        (case findTheOpInterp (spc, qid) of
	   | Some info ->
             %% Being suppressed is used here as a proxy for "has a non-constructive definition"
	     (if constructorOfType? spc qid ty
                then Constant(qid,ty)
              else if definedOpInfo? info && ~(avoidExpanding? qid) then
		let (_,_,tm) = unpackFirstOpDef info in
                if existsSubTerm (embed? The) tm
                  then Unevaluated t
                else evalRec (tm, sb, spc, depth+1,trace?)
	      else
		case qid of 
		  | Qualified ("Integer", "zero") -> Int 0
		  | _ -> Unevaluated t)
	   | _ -> 
	     case qid of 
	       | Qualified ("Integer", "zero") -> Int 0
	       | _ -> Unevaluated t)
      | Nat    n -> Int    n
      | Char   c -> Char   c
      | String s -> String s
      | Bool   b -> Bool   b
      | Embed (qid, false) -> Constant(qid,ty)
      | _ -> Unevaluated t

  op  nonStrict?: MSTerm -> Bool
  def nonStrict? t =
    case t of
      | Fun(f,_,_)  -> f in?[And,Or,Implies]
      | _ -> false

  op  evalApplyNonStrict: MSTerm * MSTerm * Subst * Spec * Nat * Bool -> MSIValue
  def evalApplyNonStrict(ft,at,sb,spc,depth,trace?) =
    case at of
      | Record([("1",at1),("2",at2)],_) ->
        (case evalRec(at1,sb,spc,depth+1,trace?) of
	   | Bool b? ->
	     (case ft of
	       | Fun(And,_,_) ->
	         if b? then evalRec(at2,sb,spc,depth+1,trace?)
		  else Bool false
	       | Fun(Or,_,_) ->
		 if b? then Bool true
		  else evalRec(at2,sb,spc,depth+1,trace?)
	       | Fun(Implies,_,_) ->
		 if b? then evalRec(at2,sb,spc,depth+1,trace?)
		  else Bool true)
	   | Unevaluated r_at1 ->
	     Unevaluated(mkApply(ft,mkTuple([r_at1,at2]))))
      | _ -> evalApplySpecial(ft,evalRec(at,sb,spc,depth+1,trace?),sb,spc,depth,trace?)
	   
  op  evalApply: MSIValue * MSIValue * Subst * Spec * Nat * Bool -> MSIValue
  def evalApply(f,a,sb,spc,depth,trace?) =
    case f of
      | Closure(match,csb) ->
        (case patternMatchRules(match,a,csb,spc,depth,trace?) of
	  | Some v -> maybeMkLetOrSubst(v,csb,sb)
	  | None -> Unevaluated(mkSimpApply(valueToTerm f,valueToTerm a)))
      | RecClosure(match,csb,ids) ->
        (case patternMatchRules(match,a,extendLetRecSubst(sb,csb,ids),spc,depth,trace?) of
	  | Some v -> maybeMkLetOrSubst(v,csb,sb)
	  | None -> Unevaluated(mkSimpApply(valueToTerm f,valueToTerm a)))
      | ChooseClosure(cl,_,_) ->
	(case a of
	  | QuotientVal(_,v,_) -> evalApply(cl,v,sb,spc,depth,trace?)
	  | _ -> Unevaluated(mkApply(valueToTerm f,valueToTerm a)))
      | Constant(qid, ty) -> Constructor(qid, a, ty)
      | Unevaluated ft -> evalApplySpecial(ft,a,sb,spc,depth,trace?)
      | _ -> Unevaluated (mkApply(valueToTerm f,valueToTerm a))

  op  mkSimpApply: MSTerm * MSTerm -> MSTerm
  def mkSimpApply(f,x) =
    case f of
      | Lambda([(p,_,bod)],_) -> mkLet([(p,x)],bod)
      | _ -> mkApply(f,x)

  op  evalApplySpecial: MSTerm * MSIValue * Subst * Spec * Nat * Bool -> MSIValue
  def evalApplySpecial(ft,a,sb,spc,depth,trace?) =
    let def default() = Unevaluated(mkApply(ft, valueToTerm a)) in
    case ft of
      | Fun(Embed(qid,true),ty,_) -> Constructor(qid,a,ty)
      | Fun(Op(qid as Qualified(spName,opName),_),ty,_) ->
        (if constructorOfType? spc qid ty
           then Constructor(qid,a,ty)
         else if spName in? evalQualifiers
	  then (case a
		  of RecordVal(fields) ->
		     (if (forall? (fn (_,tm) -> valConstant?(tm)) fields) % or spName = "Bool"
		       then attemptEvaln(spName,opName,fields,ft)
		       else default())
		    | _ -> (if evalConstant? a
			     then attemptEval1(opName,a,ft)
			     else default()))
	   else default())
      | Fun(Not,_,_) ->
	(case a of
	  | Bool x -> Bool(~ x)
	  | _ -> default())
      | Fun(And,_,_) ->
	(case a of
	   | RecordVal(fields) -> 
	     (case fields of
		| [(_,Bool x),(_,Bool y)] -> Bool(x && y)
		| [(_,Bool false),(_,_)]  -> Bool false
		| [(_,_),(_,Bool false)]  -> Bool false
		| [(_,ut),(_,Bool true)]  -> ut
		| [(_,Bool true),(_,ut)]  -> ut
		| _ -> default())
	   | None -> default())
      | Fun(Or,_,_) ->
	(case a of
	   | RecordVal(fields) -> 
	     (case fields of
		| [(_,Bool x),(_,Bool y)] -> Bool(x || y)
		| [(_,Bool true),(_,_)]   -> Bool true
		| [(_,_),(_,Bool true)]   -> Bool true
		| [(_,ut),(_,Bool false)] -> ut
		| [(_,Bool false),(_,ut)] -> ut
		| [(_,Unevaluated x),(_,Unevaluated y)] ->
		  (case (x,y) of
		     | (Apply (Fun (Not,_,_), lhs, _), rhs) ->
		       if equivTerm? spc (lhs,rhs) then
			 Bool true
		       else
			 default ()
		     | (lhs, Apply (Fun (Not,_,_), rhs, _)) ->
			 if equivTerm? spc (lhs,rhs) then
			   Bool true
			 else
			   default ()
		     | _ -> default ())
		| _  -> default())
	   | _  -> default())
      | Fun(Implies,_,_) ->
	(case a of
	   | RecordVal(fields) -> 
	     (case fields of
		| [(_,Bool x),(_,Bool y)] -> Bool(x => y)
		| [(_,Bool false),(_,_)]  -> Bool true
		| [(_,_),(_,Bool true)]   -> Bool true
		| [(_,Unevaluated t),(_,Bool false)] -> Unevaluated(mkNot(t))
		| [(_,Bool true),(_,ut)]  -> ut
		| _  -> default())
	   | _  -> default())
      | Fun(Iff,_,_) ->
	(case a of
	   | RecordVal(fields) -> 
	     (case fields of
		| [(_,Bool x),(_,Bool y)] -> Bool(x <=> y)
		| [(_,Bool false),(_,Unevaluated t)] -> Unevaluated(mkNot(t))
		| [(_,Unevaluated t),(_,Bool false)] -> Unevaluated(mkNot(t))
		| [(_,ut),(_,Bool true)]  -> ut
		| [(_,Bool true),(_,ut)]  -> ut
		| _ -> default())
	   | _ -> default())
      | Fun(Equals,_,a1) ->
	(case checkEquality(a,sb,spc,depth,trace?) of
	  | Some b -> Bool b
	  | None   ->
         case a of
           | RecordVal [("1", Constructor(id1, v1, s1)), ("2", Constructor(id2, v2, _))] ->
             if id1 = id2
               then evalApplySpecial(Fun(Equals,mkArrow(mkProduct[s1, s1], boolType),a1),
                                     RecordVal [("1", v1), ("2", v2)],
                                     sb, spc, depth, trace?)
               else Bool false
           | _ -> default())
      | Fun(NotEquals,_,_) ->
	(case checkEquality(a,sb,spc,depth,trace?) of
	  | Some b -> Bool (~ b)
	  | None   -> default())
      | Fun(RecordMerge,_,_) ->
	(case a of
	  | RecordVal[(_,RecordVal r1),(_,RecordVal r2)] ->
	    RecordVal(mergeFields(r1,r2))
	  | _ -> default()) 
      | Fun(Quotient srt_id,srt,_) ->
	(case stripSubtypes(spc,range(spc,srt)) of
	  | Quotient(_,equiv,_) -> QuotientVal(evalRec(equiv,sb,spc,depth+1,trace?),a,srt_id)
	  | _ -> default())
      %% Handled at n
      | Fun(Choose srt_id,srt,_) -> ChooseClosure(a,srt,srt_id)
      | Fun(Restrict,_,_) -> a		% Should optionally check restriction predicate
      | Fun(Relax,_,_) -> a
      | Fun(Project id,_,_) ->
	(case a of
	  | RecordVal rm -> findField(id,rm)
	  | _ -> default())
      | Fun(Embedded id,srt,_) ->
	(case a of
	  | Constructor(constr_id,_,_) -> Bool(id=constr_id)
	  | Constant(constr_id,_) -> Bool(id=constr_id)
	  | _ -> default())
	
      %| Fun(Select id,srt,_) ->
      | _ -> default()

  op  checkEquality: MSIValue * Subst * Spec * Nat * Bool -> Option Bool
  def checkEquality(a,sb,spc,depth,trace?) =
    case a of
      | RecordVal [("1",QuotientVal(equivfn,a1,_)),("2",QuotientVal(_,a2,_))] ->
        (case evalApply(equivfn,RecordVal[("1",a1),("2",a2)],sb,spc,depth,false) of
	   | Bool b -> Some b
	   | _ -> None)
      | RecordVal [("1",a1),("2",a2)] ->
        (case (a1,a2) of
           | (Unevaluated t1,Unevaluated t2) ->
             if equivTerm? spc (t1, t2)
               then Some true
             else None
           | (Unevaluated _, _) -> None
           | (_, Unevaluated _) -> None
           | _ -> equalValue?(a1, a2))
      | _ -> None
        
  def mergeFields(row1,row2) =
    let def loop(row1,row2,merged) =
          if row1 = [] then merged++row2
	  else if row2 = [] then merged++row1
	  else
	  let (e1::r1,e2::r2) = (row1,row2) in
	  case compare(e1.1,e2.1) of
	    | Less    -> loop(r1,row2,merged++[e1])
	    | Greater -> loop(row1,r2,merged++[e2])
	    | Equal   -> loop(r1,r2,merged++[e2])
    in loop(row1,row2,[])

  op  extendLetRecSubst: Subst * Subst * List Id -> Subst
  %% storedSb has all the environment except for the letrec vars which we get from dynSb
  def extendLetRecSubst(dynSb,storedSb,letrecIds) =
    % let _ = writeLine("extendLetRecSubst: "^anyToString letrecIds^"\n"^printSubst dynSb^"\n\n"^printSubst storedSb) in
    if letrecEnv?(dynSb,storedSb,letrecIds)
      then dynSb
      else if dynSb = [] then []
      else extendLetRecSubst(tail dynSb,storedSb,letrecIds)

  def letrecEnv?(dynSb,storedSb,letrecIds) =
          case (dynSb,letrecIds) of
	    | ((idS,_)::rDynSb,id1::rids) ->
	      (idS = id1 && letrecEnv?(rDynSb,storedSb,rids))
	    | _ -> letrecIds = [] && dynSb = storedSb
    
 %% Adapted from HigherOrderMatching 
 type MatchResult = | Match Subst | NoMatch | DontKnow

 op  patternMatchRules : MSMatch * MSIValue * Subst * Spec * Nat * Bool -> Option MSIValue
 def patternMatchRules(rules,N,sb,spc,depth,trace?) = 
     case rules 
       of [] -> None
        | (pat,Fun(Bool true,_,_),body)::rules -> 
	  (case patternMatch(pat,N,sb,rules = [],spc,depth,trace?)
	     of Match S -> Some(maybeMkLetOrSubst(evalRec(body,S,spc,depth+1,trace?),S,sb))
	      | NoMatch -> patternMatchRules(rules,N,sb,spc,depth,trace?)
	      | DontKnow -> None)
	| _ :: rules -> None

 op  patternMatch : MSPattern * MSIValue * Subst * Bool * Spec * Nat * Bool -> MatchResult 
 def patternMatch(pat,N,S,soft_conds?,spc,depth,trace?) =
   %% soft_conds? is true when there is no fall-through case, i.e. it is in a let or
   %% it is the last clause of a lambda (case).
     case pat
       of VarPat((x,_), _) -> Match(addToSubst(S,x,N))
	| WildPat _ -> Match S
	| AliasPat(p1,p2,_) ->
	  (case patternMatch(p1,N,S,soft_conds?,spc,depth,trace?) of
	     | Match S1 -> patternMatch(p2,N,S1,soft_conds?,spc,depth,trace?)
	     | result -> result)
	| RecordPat(fields, _) ->
	  (case N of
	     | RecordVal valFields ->
	       foldl (fn (result,(lbl,rpat)) ->
		      case result of
			| Match S ->
			  (case lookup(valFields,lbl) of
			     | None -> DontKnow
			     | Some v -> patternMatch(rpat,v,S,soft_conds?,spc,depth,trace?))
			| _ -> result)
	         (Match S) fields
	     | _ -> DontKnow)
	| EmbedPat(lbl,None,srt,_) -> 
	  (if constructorOp? spc lbl
             then case N of
                    | Constant(lbl2,_) -> if lbl = lbl2 then Match S else NoMatch
                    | Unevaluated _ -> DontKnow
                    | _ -> NoMatch
           else let c_val = evalRec(mkOp(lbl, srt),[],spc,depth,trace?) in
                case checkEquality(RecordVal[("1",c_val),("2",N)], S, spc, depth, trace?) of
                  | None -> DontKnow
                  | Some true -> Match S
                  | Some false -> NoMatch)
	| EmbedPat(lbl,Some p,srt,_) -> 
	  (case N of 
	     | Constructor(lbl2,N2,_) -> 
	       if lbl = lbl2 
		  then patternMatch(p,N2,S,soft_conds?,spc,depth,trace?)
	       else NoMatch
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
        | QuotientPat(pat,_,_,_) ->
	  (case N of
	     | QuotientVal(_,v,_) -> patternMatch(pat,v,S,soft_conds?,spc,depth,trace?)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
        | RestrictedPat(pat,pred,_) ->
	  (case patternMatch(pat,N,S,soft_conds?,spc,depth,trace?) of
	     | Match S1 ->
	       (case evalRec(pred,S1,spc,depth+1,trace?) of
		 | Bool true  -> Match S1
		 | Bool false -> NoMatch
		 | _ ->  %% If soft_conds? then succeed as there is no other case
                   if soft_conds? then Match S1 else DontKnow)
	     | result -> result)
	| StringPat(n,_) ->
	  (case N
	    of String m -> (if n = m then Match S else NoMatch)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
	| BoolPat(n,_) ->
	  (case N
	    of Bool m -> (if n = m then Match S else NoMatch)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
	| CharPat(n,_) ->
	  (case N
	    of Char m -> (if n = m then Match S else NoMatch)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
	| NatPat(n,_) ->
	  (case N
	    of Int m -> (if n = m then Match S else NoMatch)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
	| _ -> DontKnow

  %% Considers incremental newSb vs oldSb. Looks for references to these vars in val and
  %% either substitutees them (if their values are simple) or let-binds them.
  op  maybeMkLetOrSubst: MSIValue * Subst * Subst -> MSIValue
  def maybeMkLetOrSubst(val,newSb,oldSb) =
    case val of
      | Unevaluated t -> Unevaluated(mkLetOrsubst(t,newSb,oldSb))
      | _ -> val

  op  mkLetOrsubst: MSTerm * Subst * Subst -> MSTerm
  def mkLetOrsubst(t,newSb,oldSb) =
    let def splitSubst sb =
          List.foldl (fn ((letSb,substSb),(vr,val)) ->
		 if evalConstant? val	% Could be more discriminating
		  then (letSb,Cons((vr,valueToTerm val),substSb))
		  else (Cons((vr,valueToTerm val),letSb),substSb))
	    ([],[]) sb
    in
    let localSb = ldiff(newSb,oldSb) in
    if localSb = emptySubst then t
      else
      let fvs = freeVars t in
      let usedSb = foldl (fn (rsb,(id1,v)) ->
			  case findLeftmost (fn (id2,_) -> id1 = id2) fvs of
			    | Some vr -> Cons((vr,v),rsb)
			    | None -> rsb)
		     [] localSb
      in
      let (letSb,substSb) = splitSubst usedSb in
      mkLetWithSubst(substitute(t,substSb),letSb)

  %% First list should contain second list as a tail
  op  ldiff: [a] List a * List a -> List a
  def ldiff(l1,l2) =
    if l1 = l2 || l1 = [] then []
      else Cons(head l1,ldiff(tail l1,l2))
      

  %% Evaluation of constant terms
  %% we need to include "Bool" for "compare", "toString", "show", "pp", etc.
  def evalQualifiers = ["Nat","Integer","IntegerAux","String","Char","System","Bool"]
  op  evalConstant?: MSIValue -> Bool
  def evalConstant?(v) =
    case v
      of Unevaluated t -> embed? Fun t
       | RecClosure _ -> false
       | Closure _ -> false
       | ChooseClosure _ -> false
       | Constructor(_, v1, _) -> evalConstant? v1
       | _ -> true

%% Only have to include those that have a definition you don't want to use (and doesn't include "the")
  op builtInQids: List QualifiedId =
    [Qualified("String","explode"),
     Qualified("String","implode"),
     Qualified("String","^"),
     Qualified("String","<"),
     Qualified("String","<="),
     Qualified("String",">"),
     Qualified("String",">="),
     
     Qualified("Integer","ipred"),
     Qualified("Integer","divides"),
     Qualified("Integer","divR"),
     Qualified("Integer","divE"),
     Qualified("Integer","divT"),
     Qualified("Integer","<"),
     Qualified("Integer","<="),
     Qualified("Integer",">"),
     Qualified("Integer",">="),
     Qualified("Char","ord"),
     Qualified("Char","isUpperCase"),
     Qualified("Char","isLowerCase"),
     Qualified("Char","isAlphaNum"),
     Qualified("Char","isAlpha"),
     Qualified("Char","isAscii")
     ]

   op avoidExpanding? (qid : QualifiedId) : Bool =
    qid in? builtInQids

  op  valConstant?: MSIValue -> Bool
  def valConstant? v =
    case v
      of Unevaluated _ -> false
       | _ -> true

  op  intVal: MSIValue -> Int
  def intVal = fn (Int i) -> i
  op  intVals: List(Id * MSIValue) -> Int * Int
  def intVals([(_,x),(_,y)]) = (intVal x,intVal y)

  op  charVal: MSIValue -> Char
  def charVal = fn (Char c) -> c

  op  stringVal: MSIValue -> String
  def stringVal = fn (String s) -> s
  op  stringVals: List(Id * MSIValue) -> String * String
  def stringVals([(_,x),(_,y)]) = (stringVal x,stringVal y)

  op  boolVal: MSIValue -> Bool
  def boolVal = fn (Bool s) -> s
  op  boolVals: List(Id * MSIValue) -> Bool * Bool
  def boolVals([(_,x),(_,y)]) = (boolVal x,boolVal y)

  op  stringIntVals: List(Id * MSIValue) -> String * Int
  def stringIntVals([(_,x),(_,y)]) = (stringVal x,intVal y)

  op  attemptEval1: String * MSIValue * MSTerm -> MSIValue
  def attemptEval1(opName,arg,f) =
    let def default() = Unevaluated(mkApply(f,valueToTerm arg)) in
    case (opName,arg) of
       | ("-", Int i)         -> Int (- i) 
       | ("~", Int i)         -> Int (- i) % TODO: deprecate
       | ("~", Bool b)        -> Bool (~b)
       | ("positive?", Int i) -> Bool (i >= 0)
       | ("pred", Int i)      -> Int (pred i)
       | ("toString", Int i)  -> String (show i)
       | ("toString", Bool b) -> String (show b)
       | ("toString", Char c) -> String (show c)
       | ("show", Int i)      -> String (show i)
       | ("show", Bool b)     -> String (show b)
       | ("show", Char c)     -> String (show c)
       | ("isucc",Int i)      -> Int (isucc i)
       | ("succ",Int i)       -> Int (isucc i)
       | ("ipred",Int i)      -> Int (ipred i)

%% Defined in InterpreterBase
%       | ("stringToInt",String s)  ->
%         if intConvertible s
%	   then Int(stringToInt s)
%	   else default()
%       | ("stringToNat",String s)  ->
%         if natConvertible s
%	   then Int(stringToNat s)
%	   else default()
       | ("length",String s)  -> Int(length s)
       | ("explode",String s) -> foldr (fn (c,r) -> Constructor(Qualified("List","Cons"),
                                                                RecordVal[("1",Char c),("2",r)],
                                                                mkArrow(mkProduct[charType, listCharType],
                                                                        listCharType)))
                                   (Constant(Qualified("List","Nil"),listCharType)) (explode s)
       | ("toScreen",String s)  -> let _ = toScreen  s in RecordVal []
       | ("print",String s)     -> let _ = System.print  s in RecordVal []
       | ("writeLine",String s) -> let _ = writeLine s in RecordVal []

       | ("implode",arg)        ->
         if metaList? arg
	   then String(foldr (fn(Char c,rs) -> (show c)^rs) "" (metaListToList arg))
	   else default()

       | ("isUpperCase",Char c) -> Bool(isUpperCase c)
       | ("isLowerCase",Char c) -> Bool(isLowerCase c)
       | ("isAlphaNum",Char c)  -> Bool(isAlphaNum c)
       | ("isAlpha",Char c)     -> Bool(isAlpha c)
       | ("isNum",Char c)       -> Bool(isNum c)
       | ("isAscii",Char c)     -> Bool(isAscii c)
       | ("toUpperCase",Char c) -> Char(toUpperCase c)
       | ("toLowerCase",Char c) -> Char(toLowerCase c)
       | ("ord",Char c)         -> Int(ord c)
       | ("chr",Int i)          -> Char(chr i)

       | ("fail",String s) -> fail s
       | ("debug",String s) -> debug s	% Might want to do something smarter
       | ("warn",String s) -> warn s
       | ("getEnv",String s) -> (case getEnv s of
				   | None -> Constant(Qualified("Option", "None"),optionStringType)
				   | Some s -> Constructor(Qualified("Option", "Some"),String s,optionStringType))
       | ("garbageCollect",Bool b) -> let _ = System.garbageCollect b in RecordVal []
       | ("trueFilename",String s) -> String(trueFilename s)

       | ("anyToString", Int i)      -> String (show i)
       | ("anyToString", Bool b)     -> String (show b)
       | ("anyToString", Char c)     -> String (show c)
       | ("anyToString", arg)     -> String (anyToString arg)
       %% Missing System. time, msWindowsSystem?, hackMemory

       | _                      -> default()

  op  attemptEvaln: String * String * List(Id * MSIValue) * MSTerm -> MSIValue
  def attemptEvaln(spName,opName,fields,f) =
    let def default() = Unevaluated(mkApply(f,valueToTerm(RecordVal fields))) in
    case opName of
       %% Int operations
       | "+"   -> Int(+(intVals fields))
       | "*"   -> Int( *(intVals fields))    % Space before * is needed so parser doesn't see a comment!
       | "-"   -> Int(-(intVals fields))
       | "gcd"   -> Int(gcd(intVals fields))
       | "lcm"   -> Int(lcm(intVals fields))
       | "<"   -> if spName = "String"
                    then Bool(<(stringVals fields))
		    else Bool(<(intVals fields))
       | "<="  -> if spName = "String"
                    then Bool(<=(stringVals fields))
		    else Bool(<=(intVals fields))
       %% Following have definitions but rather inefficient
       | ">"   -> if spName = "String"
                    then Bool(>(stringVals fields))
		    else Bool(>(intVals fields))
       | ">="  -> if spName = "String"
                    then Bool(>=(stringVals fields))
		    else Bool(>=(intVals fields))
       %| "min" -> Int(min(intVals fields))
       %| "max" -> Int(max(intVals fields))
       | "divides" -> Bool(divides(intVals fields))
       | "modT" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(modT(x,y))
       | "divT" -> let (x,y) = intVals fields in
		  if y = 0 then default()
 		    else Int(divT(x,y))
       | "modE" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(modE(x,y))
       | "divE" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(divE(x,y))
       | "modF" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(modF(x,y))
       | "divF" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(divF(x,y))
       | "modC" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(modC(x,y))
       | "divC" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(divC(x,y))
       | "modR" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(modR(x,y))
       | "divR" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(divR(x,y))

       %% string operations
       | "concat" -> String(^(stringVals fields))
       | "++"  -> String(^(stringVals fields))
       | "^"   -> String(^(stringVals fields))
       | "substring" ->
	 (case fields of
	    | [(_,s),(_,i),(_,j)] ->
	      let sv = stringVal s in
	      let iv = intVal i in
	      let jv = intVal j in
	      if iv <= jv && jv <= length sv
		then String(subFromTo(stringVal s,intVal i,intVal j))
		else default()
	    | _ -> default())
       | "leq" -> Bool(<=(stringVals fields))
       | "lt"  -> Bool(<( stringVals fields))
       | "sub" -> let (s,i) = stringIntVals fields in
	          if i >= 0 && i < length s
		    then Char(s@i)
		    else default()

    % %% Bool operations are non-strict
    %% %% Should it be non-strict in first argument as well as second?
    %% | "&&"   ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x & y)
    %%     | [(_,Bool false),(_,_)]  -> Bool false
    %%     | [(_,_),(_,Bool false)]  -> Bool false
    %%     | [(_,ut),(_,Bool true)]  -> ut
    %%     | [(_,Bool true),(_,ut)]  -> ut
    %%     | _                       -> default())
    %%  | "||"  ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x or y)
    %%     | [(_,Bool true),(_,_)]   -> Bool true
    %%     | [(_,_),(_,Bool true)]   -> Bool true
    %%     | [(_,ut),(_,Bool false)] -> ut
    %%     | [(_,Bool false),(_,ut)] -> ut
    %%     | [(_,Unevaluated x),(_,Unevaluated y)] ->
    %%        (case (x,y) of
    %%           | (Apply (Fun (Op (Qualified (_,"~"),fxty),srt,pos1), lhs, pos2), rhs) ->
    %%               if equivTerm? spc (lhs,rhs) then
    %%                 Bool true
    %%               else
    %%                 default ()
    %%           | (lhs, Apply (Fun (Op (Qualified (_,"~"),fxty),srt,pos1), rhs, pos2)) ->
    %%               if equivTerm? spc (lhs,rhs) then
    %%                 Bool true
    %%               else
    %%                 default ()
    %%           | _ -> default ())
    %%     | _                    -> default())
    %% 
    %%  | "=>"  ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x => y)
    %%     | [(_,Bool false),(_,_)]  -> Bool true
    %%     | [(_,_),(_,Bool true)]   -> Bool true
    %%     | [(_,Unevaluated t),(_,Bool false)] -> Unevaluated(mkNot(t))
    %%     | [(_,Bool true),(_,ut)]  -> ut
    %%     | _                       -> default())
    %% | "<=>"  ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x <=> y)
    %%     | [(_,Bool false),(_,Unevaluated t)] -> Unevaluated(mkNot(t))
    %%     | [(_,Unevaluated t),(_,Bool false)] -> Unevaluated(mkNot(t))
    %%     | [(_,ut),(_,Bool true)]  -> ut
    %%     | [(_,Bool true),(_,ut)]  -> ut
    %%     | _                       -> default())

       | _     -> default()

  %% Separate function rather than in-line because in Allegro time compile with a closure
  %% which gets created on each call even if not needed
  op  timeEvalRec:  MSTerm * Subst * Spec * Nat * Bool -> MSIValue
  def timeEvalRec(t,sb,spc,depth,trace?) =
    time(evalRec(t,sb,spc,depth,trace?))

  op  metaListToList: (MSIValue | metaList?) -> List MSIValue
  def metaListToList v =
    case v of
      | Constant (Qualified(_,"Nil"),_) -> []
      | Constructor(Qualified(_,"Cons"),RecordVal[("1",x),("2",r)],_) -> Cons(x,metaListToList r)

  op  metaList?: MSIValue -> Bool
  def metaList? v =
    case v of
      | Constant(Qualified(_,"Nil"),_) -> true
      | Constructor(Qualified(_,"Cons"),RecordVal[("1",_),("2",r)],_) -> metaList? r
      | _ -> false


  op  printMSIValue: MSIValue * Bool -> ()
  def printMSIValue (v,useXSymbol?) =
    PrettyPrint.toTerminal(format(100,ppValue (initialize(if useXSymbol?
							   then XSymbolPrinter
							   else asciiPrinter,
							 false))
				  v))

  op  stringValue: MSIValue -> String
  def stringValue v =
    PrettyPrint.toString(format(100,ppValue (initialize(asciiPrinter,false)) v))

  op printSubst (sb: Subst): String =
     PrettyPrint.toString(format(100,ppSubst (initialize(asciiPrinter,false)) sb))

  op printSubsts?: Bool = true

  op ppSubst (ctxt: PrContext) (sb: Subst): Pretty =
    if printSubsts? then
      let sb = trimSubst sb in
      prettysFill (addSeparator (string ", ")
                     (map (fn (id,x) ->
                             blockLinear
                             (0,
                              [(0,string  id),
                               (0,string  " -> "),
                               (0,ppValue ctxt x)]))
                        sb))
    else prEmpty

  op  ppValue: PrContext -> MSIValue -> Pretty
  def ppValue ctxt v =
    case v of
      | Int         n  -> string (show n)
      | Char        c  -> string ("\#"^show c)
      | String      s  -> string ("\"" ^ s ^ "\"")
      | Bool        b  -> string (if b then "true" else "false")
      | RecordVal   rm ->
        if tupleFields? rm
	  then prettysNone [string "(",
			    prettysFill(addSeparator (string ", ")
					 (map (fn (_,x) -> ppValue ctxt x) rm)),
			    string ")"]
	  else prettysNone [string "{",
			    prettysFill(addSeparator (string ", ")
					  (map (fn (id,x) ->
						   blockLinear
						   (0,
						    [(0,string  id),
						     (0,string  " = "),
						     (0,ppValue ctxt x)]))
					       rm)),
			    string "}"]
      | Constructor(Qualified(_,"Cons"),arg as RecordVal[(_,_),(_,_)],_) ->
	(case valueToList v of
	   | Some listVals ->
	     prettysNone [string "[",
			  prettysFill(addSeparator (string ", ")
					(map (ppValue ctxt) listVals)),
			  string "]"]
	   | None -> prettysFill[string "Cons",string " ",ppValue ctxt arg])
      | Constructor (qid,arg,_) -> prettysFill [string(printQualifiedId qid),string " ",ppValue ctxt arg]
      | Constant        (qid,_) -> string(printQualifiedId qid)
      | QuotientVal (f,arg,srt_id)  -> prettysFill [string "quotient[",
                                                    string (printQualifiedId srt_id), string "] ",
                                                    ppValue ctxt arg]
      | ChooseClosure(cl,_,srt_id)  ->
	prettysFill [string "choose[",string (printQualifiedId srt_id), string "] "]
      | Closure(_,sb)  ->
        prettysNone[string "<Closure {",
                    ppSubst ctxt sb,
                    string "}>"]
      | RecClosure(_,sb,ids)  -> 
	prettysNone[string "<Closure {",
		    ppSubst ctxt sb,
		    string "}, ",
		    string "{",
		    prettysFill(addSeparator (string ", ") (map (fn id -> string id) ids)),
		    string "}>"]
      | Unevaluated t  -> prettysNone[string "<Unev: ",
				      ppTerm ctxt ([],Top:ParentTerm) t,
				      string ">"]

  op  valueToList: MSIValue -> Option(List MSIValue)
  def valueToList v =
    case v of
      | Constructor(Qualified(_,"Cons"),RecordVal[(_,a),(_,rl)],_) ->
        (case valueToList rl of
	  | Some l -> Some(Cons(a,l))
	  | None -> None)
      | Constant (Qualified(_,"Nil"),_) -> Some []
      | _ -> None

  op  valueToTerm: MSIValue -> MSTerm
  def valueToTerm v =
    case v of
      | Int         n  -> mkInt n
      | Char        c  -> mkChar c
      | String      s  -> mkString s
      | Bool        b  -> mkBool b
      | RecordVal   rm -> mkRecord(map (fn (id,x) -> (id,valueToTerm x)) rm)
      | Constructor (id,arg,ty) -> mkApply(mkFun(Op(id, Constructor1), ty), valueToTerm arg)
      | Constant    (id,ty) -> mkFun(Op(id, Constructor0), ty)
% TODO: restore these
      | QuotientVal (f,arg,srt_qid)  ->
        let argtm = valueToTerm arg in
	mkQuotient(argtm,srt_qid,termType argtm)
      | ChooseClosure(a,srt,srt_id) -> mkApply(mkFun(Choose srt_id,srt),valueToTerm a)
      | Closure(f,sb)   -> mkLetOrsubst(Lambda(f,noPos),sb,emptySubst)
      | RecClosure(f,_,_) -> Lambda(f,noPos)
      | Unevaluated t  -> t

  op fullyReduced?(v: MSIValue): Bool =
    case v of
      | Unevaluated_  -> false
      | Closure _ -> false
      | RecClosure _ -> false
      | RecordVal rm -> forall? (fn (_,x) -> fullyReduced? x) rm
      | Constructor(_,arg,_) -> fullyReduced? arg
      | QuotientVal (f,arg,srt_qid) -> fullyReduced? arg
      | ChooseClosure (arg,srt,srt_id) -> fullyReduced? arg
      | _ -> true

  op  unknownType: MSType
  def unknownType = mkTyVar "Unknown"

  %% Generally useful utility
  op  loopn: [a] (Nat * a -> a) -> a -> Nat -> a
  def loopn f init n =
    let def loop(i,result) =
          if i = n then result else loop(i+1,f(i,result))
    in loop(0,init)

  op termToValue : MSTerm -> MSIValue
  def termToValue term =
    case term of
      | Fun (Nat n,srt,pos) -> Int n
      | Fun (Char c,srt,pos) -> Char c
      | Fun (String s,srt,pos) -> String s
      | Record (flds,pos) -> RecordVal (map (fn (id,x) -> (id,termToValue x)) flds)
      | Apply (Fun (Op (id,_),srt,pos),t2,srt2) -> Constructor (id, termToValue t2,srt)
      | Fun (Op (id,_),srt,pos) -> Constant(id,srt)
      | Apply (Fun (Embed (id,_),srt,pos),t2,srt2) -> Constructor (id, termToValue t2,srt)
      | Fun (Embed (id,_),srt,pos) -> Constant(id,srt)
      | _ -> Unevaluated term

 op dontReduceQualifiers: Ids = ["System"]
 op dontReduceQIds: QualifiedIds = [mkQualifiedId("C","uintConstant"), mkQualifiedId("C","uintOfMathInt"),
                                    mkUnQualifiedId("mathIntOfUint2"), mkUnQualifiedId("uintOfMathInt2")]

 op dontReduceTerm?(tm: MSTerm): Bool =
   case tm of
     | Apply(f, x, _) -> dontReduceTerm? f || dontReduceTerm? x
     | Fun(Op(qid as Qualified(q,id),_), _, _) ->
       q in? dontReduceQualifiers
         || qid in? dontReduceQIds
     | _ -> false

 op assumeNoSideEffects?: Bool = true

 op reduceTerm(term: MSTerm, spc: Spec): MSTerm =
   if ~(constantTerm? term) && freeVarsRec term true = []
     && (if assumeNoSideEffects? then ~(hasSideEffect? term)
           else sideEffectFree term)
     && ~(existsSubTerm dontReduceTerm? term)
     then
       % let _ = writeLine("reduceTerm: "^printTerm term) in
       let v = eval(term,spc) in
       if fullyReduced? v
         then let new_tm = valueToTerm v in
              % let _ = writeLine("--> "^printTerm new_tm) in
              new_tm
         else term
     else term

 op reduceSubTerms(term: MSTerm, spc: Spec): MSTerm =
   mapTerm (fn t -> reduceTerm(t,spc), id, id) term

 op trimSubst(sb: Subst): Subst =
   let def trim(sb, seen) =
         case sb of
           | [] -> []
           | (k, v) :: r_sb ->
             if k in? seen
               then trim(r_sb, seen)
               else (k, v) :: trim(r_sb, k :: seen)
   in
   trim(sb, [])

end-spec
%%% 
