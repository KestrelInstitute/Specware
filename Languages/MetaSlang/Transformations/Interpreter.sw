%%% Simple interpreter for MetaSlang. Assume type-correct term. If it evaluate a term
%%% it just returns the term.

MSInterpreter qualifying
spec
  import /Languages/MetaSlang/Specs/Environment
  import ../Specs/Utilities

  sort Value =
    | Int         Integer
    | Char        Char
    | String      String
    | Bool        Boolean
    | RecordVal   Subst
    | Constructor Id * Value
    | Constant    Id
    | QuotientVal Value * Value		% closure * element
    | ChooseClosure Value * MS.Sort
    | Closure     Match * Subst
    | RecClosure  Match * Subst * List Id
    | Unevaluated MS.Term

  sort Subst = List (Id * Value)

  op  unevaluated?: Value -> Boolean
  def unevaluated? x = embed? Unevaluated x

  op  emptySubst: Subst
  def emptySubst = []

  op lookup: Subst * Id -> Option Value
  def lookup(sbst,v) =
    case sbst of
      | [] -> None
      | (vi,vali)::rsbst ->
	if vi = v then Some vali else lookup(rsbst,v)

  op  addToSubst: Subst * Id * Value -> Subst
  def addToSubst(sb,v,t) = Cons((v,t),sb)

%%% --------------------
  op  eval: MS.Term * Spec -> Value
  def eval(t,spc) = evalRec(t,emptySubst,spc,0)

  op  traceEval?: Boolean
  def traceEval? = false

  op  traceable?: MS.Term -> Boolean
  def traceable? t =
    case t of
      %| Var _ -> false
      | Fun _ -> false
      | Lambda _ -> false
      | Record (("1", _)::_,_) -> false
      | _ -> true

  op  preTrace: MS.Term * Nat -> ()
  def preTrace(t,depth) =
    if traceEval? && traceable? t then
      let _ = toScreen (blanks depth) in
      case t of
	| Var _ ->
	  let _ = printTermToTerminal t in
	  let _ = toScreen ": " in
	  ()
	| _ ->
	  let _ = toScreen ((toString depth)^"< ") in
	  let _ = printTermToTerminal t in
	  let _ = toScreen newline in
	  ()
    else ()
    
  op  postTrace: MS.Term * Value * Nat -> ()
  def postTrace(t,val,depth) =
    if traceEval? && traceable? t then
      case t of
	| Var _ ->
	  let _ = printValue val in
	  let _ = toScreen newline in
	  ()
	| _ ->
	  let _ = toScreen (blanks depth) in
	  let _ = toScreen ((toString depth)^"> ") in
	  let _ = printValue val in
	  let _ = toScreen newline in
	  ()
    else ()

  op  evalRec: MS.Term * Subst * Spec * Nat -> Value
  def evalRec(t,sb,spc,depth) =
    let _ = preTrace(t,depth) in
    let depth = if traceable? t then depth else depth -1 in
    let val = 
	case t of
	  | Var((v,_),_) ->
	    (case lookup(sb,v) of
	      | Some e -> e
	      | None -> Unevaluated t)
	  | Fun(fun,_,_) -> evalFun(fun,t,sb,spc,depth)
	  | Apply(Fun(Op(Qualified("System","time"),_),_,_),y,_) -> timeEvalRec(y,sb,spc,depth+1)
	  | Apply(x,y,_) ->
	    if nonStrict? x
	      then evalApplyNonStrict(x,y,sb,spc,depth)
	      else evalApply(evalRec(x,sb,spc,depth+1),evalRec(y,sb,spc,depth+1),sb,spc,depth)
	  | Record(fields,a) ->
	    RecordVal(map (fn(lbl,e) -> (lbl,evalRec(e,sb,spc,depth+1))) fields)
	  | IfThenElse(P,M,N,a) ->
	    (case evalRec(P,sb,spc,depth+1) of
	      | Bool true  -> evalRec(M,sb,spc,depth+1)
	      | Bool false -> evalRec(N,sb,spc,depth+1)
	      | Unevaluated nP -> Unevaluated (IfThenElse(nP,M,N,a))
	      | _ -> Unevaluated t)
	  | Lambda(match,_) -> Closure(match,sb)
	  | Seq(tms,_) -> nth (map (fn s -> evalRec(s,sb,spc,depth+1)) tms, (length tms) - 1)
	  | Let(decls, body, a) ->
	    (let rdecls = map (fn (pat,e) -> (pat,evalRec(e,sb,spc,depth+1))) decls in
	     case foldl (fn ((pat,e),ssb) ->
			  case ssb of
			    | Some sbr ->
			      %% The e are evaluated in the outer environment (sb not sbr)
			      (case patternMatch(pat,e,sbr,spc,depth) of
				 | Match S -> Some S
				 | _ -> None)
			    | None -> None)
		   (Some sb) rdecls
	       of Some newsb -> maybeMkLetOrSubst(evalRec(body,newsb,spc,depth+1),newsb,sb)
		| None -> Unevaluated (Let(map (fn (pat,e) -> (pat,valueToTerm e)) rdecls, body, a)))
	  | LetRec(decls, body, _) ->
	    let ids = rev(map (fn ((v,_),_) -> v) decls) in
	    (case foldl (fn (((v,_),e),ssb) ->
			 case ssb of
			   | Some nsb ->
			     Some(addToSubst(nsb,v,
					     case evalRec(e,sb,spc,depth+1) of
					       | Closure(m,sbc) ->
						 RecClosure(m,sb,ids)
					       | v -> v))
			   | None -> ssb)
		   (Some sb) decls
	       of Some sb ->
		  (case evalRec(body,sb,spc,depth+1) of
		     | Unevaluated t1 ->
		       if exists (fn (id,_) -> member(id,ids)) (freeVars t)
		        then Unevaluated(mkLetRec(decls,t1))
			else Unevaluated t1
		     | v -> v)
		| None -> Unevaluated t)

	  % ? | Bind()
	  | _ -> Unevaluated t
    in
    let _ = postTrace(t,val,depth) in
    val
  
  op  evalFun: Fun * MS.Term * Subst * Spec * Nat -> Value
  def evalFun(fun,t,sb,spc,depth) =
    case fun of
      | Op (qid, _) ->
        (case findTheOp (spc, qid) of
	   | Some info ->
	     (if definedOpInfo? info then
		let tm = firstOpDefInnerTerm info in
		evalRec (tm, sb, spc, depth+1)
	      else
		case qid of 
		  | Qualified ("Nat", "zero") -> Int 0
		  | _ -> Unevaluated t)
	   | _ -> 
	     case qid of 
	       | Qualified ("Nat", "zero") -> Int 0
	       | _ -> Unevaluated t)
      | Nat    n -> Int    n
      | Char   c -> Char   c
      | String s -> String s
      | Bool   b -> Bool   b
      | Embed (id, false) -> Constant id
      | _ -> Unevaluated t

  op  nonStrict?: MS.Term -> Boolean
  def nonStrict? t =
    case t of
      | Fun(f,_,_)  -> member(f,[And,Or,Implies])
      | _ -> false

  op  evalApplyNonStrict: MS.Term * MS.Term * Subst * Spec * Nat -> Value
  def evalApplyNonStrict(ft,at,sb,spc,depth) =
    case at of
      | Record([("1",at1),("2",at2)],_) ->
        (case evalRec(at1,sb,spc,depth+1) of
	   | Bool b? ->
	     (case ft of
	       | Fun(And,_,_) ->
	         if b? then evalRec(at2,sb,spc,depth+1)
		  else Bool false
	       | Fun(Or,_,_) ->
		 if b? then Bool true
		  else evalRec(at2,sb,spc,depth+1)
	       | Fun(Implies,_,_) ->
		 if b? then evalRec(at2,sb,spc,depth+1)
		  else Bool true)
	   | Unevaluated r_at1 ->
	     Unevaluated(mkApply(ft,mkTuple([r_at1,at2]))))
      | _ -> evalApplySpecial(ft,evalRec(at,sb,spc,depth+1),sb,spc,depth)
	   
  op  evalApply: Value * Value * Subst * Spec * Nat -> Value
  def evalApply(f,a,sb,spc,depth) =
    case f of
      | Closure(match,csb) ->
        (case patternMatchRules(match,a,csb,spc,depth) of
	  | Some v -> maybeMkLetOrSubst(v,csb,sb)
	  | None -> Unevaluated(mkSimpApply(valueToTerm f,valueToTerm a)))
      | RecClosure(match,csb,ids) ->
        (case patternMatchRules(match,a,extendLetRecSubst(sb,csb,ids),spc,depth) of
	  | Some v -> maybeMkLetOrSubst(v,csb,sb)
	  | None -> Unevaluated(mkSimpApply(valueToTerm f,valueToTerm a)))
      | ChooseClosure(cl,_) ->
	(case a of
	  | QuotientVal(_,v) -> evalApply(cl,v,sb,spc,depth)
	  | _ -> Unevaluated(mkApply(valueToTerm f,valueToTerm a)))
      | Unevaluated ft -> evalApplySpecial(ft,a,sb,spc,depth)
      | _ -> Unevaluated (mkApply(valueToTerm f,valueToTerm a))

  op  mkSimpApply: MS.Term * MS.Term -> MS.Term
  def mkSimpApply(f,x) =
    case f of
      | Lambda([(p,_,bod)],_) -> mkLet([(p,x)],bod)
      | _ -> mkApply(f,x)

  op  evalApplySpecial: MS.Term * Value * Subst * Spec * Nat -> Value
  def evalApplySpecial(ft,a,sb,spc,depth) =
    let def default() = Unevaluated(mkApply(ft,valueToTerm a)) in
    case ft of
      | Fun(Embed(id,true),_,_) -> Constructor(id,a)
      | Fun(Op(Qualified(spName,opName),_),_,_) ->
        (if member(spName,evalQualifiers)
	  then (case a
		  of RecordVal(fields) ->
		     (if (all (fn (_,tm) -> evalConstant?(tm)) fields) % or spName = "Boolean"
		       then attemptEvaln(spName,opName,fields,ft)
		       else Unevaluated(mkApply(ft,valueToTerm a)))
		    | _ -> (if evalConstant? a
			     then attemptEval1(opName,a,ft)
			     else Unevaluated(mkApply(ft,valueToTerm a))))
	   else Unevaluated(mkApply(ft,valueToTerm a)))
      | Fun(Not,_,_) ->
	(case a of
	  | Bool x -> Bool(~ x)
	  | _ -> default())
      | Fun(And,_,_) ->
	(case a of
	   | RecordVal(fields) -> 
	     (case fields of
		| [(_,Bool x),(_,Bool y)] -> Bool(x & y)
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
		| [(_,Bool x),(_,Bool y)] -> Bool(x or y)
		| [(_,Bool true),(_,_)]   -> Bool true
		| [(_,_),(_,Bool true)]   -> Bool true
		| [(_,ut),(_,Bool false)] -> ut
		| [(_,Bool false),(_,ut)] -> ut
		| [(_,Unevaluated x),(_,Unevaluated y)] ->
		  (case (x,y) of
		     | (Apply (Fun (Not,_,_), lhs, _), rhs) ->
		       if equalTerm? (lhs,rhs) then
			 Bool true
		       else
			 default ()
		     | (lhs, Apply (Fun (Not,_,_), rhs, _)) ->
			 if equalTerm? (lhs,rhs) then
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
      | Fun(Equals,_,_) ->
	(case checkEquality(a,sb,spc,depth) of
	  | Some b -> Bool b
	  | None   -> Unevaluated(mkApply(ft,valueToTerm a)))
      | Fun(NotEquals,_,_) ->
	(case checkEquality(a,sb,spc,depth) of
	  | Some b -> Bool (~ b)
	  | None   -> Unevaluated(mkApply(ft,valueToTerm a)))
      | Fun(RecordMerge,_,_) ->
	(case a of
	  | RecordVal[(_,RecordVal r1),(_,RecordVal r2)] ->
	    RecordVal(mergeFields(r1,r2))
	  | _ -> default()) 
      | Fun(Quotient,srt,_) ->
	(case stripSubsorts(spc,range(spc,srt)) of
	  | Quotient(_,equiv,_) -> QuotientVal(evalRec(equiv,sb,spc,depth+1),a)
	  | _ -> Unevaluated(mkApply(ft,valueToTerm a)))
      %% Handled at n
      | Fun(Choose,srt,_) -> ChooseClosure(a,srt)
      | Fun(Restrict,_,_) -> a		% Should optionally check restriction predicate
      | Fun(Relax,_,_) -> a
      | Fun(Project id,_,_) ->
	(case a of
	  | RecordVal rm -> findField(id,rm)
	  | _ -> Unevaluated(mkApply(ft,valueToTerm a)))
      | Fun(Embedded id,srt,_) ->
	(case a of
	  | Constructor(constr_id,_) -> Bool(id=constr_id)
	  | _ -> Unevaluated(mkApply(ft,valueToTerm a)))
	
      %| Fun(Select id,srt,_) ->
      | _ -> Unevaluated(mkApply(ft,valueToTerm a))

  op  checkEquality: Value * Subst * Spec * Nat -> Option Boolean
  def checkEquality(a,sb,spc,depth) =
    case a of
      | RecordVal [("1",QuotientVal(equivfn,a1)),("2",QuotientVal(_,a2))] ->
        (case evalApply(equivfn,RecordVal[("1",a1),("2",a2)],sb,spc,depth) of
	   | Bool b -> Some b
	   | _ -> None)
      | RecordVal [("1",a1),("2",a2)] ->
        (if evalConstant? a1 & evalConstant? a2
	  then (case (a1,a2) of
		  | (Unevaluated t1,Unevaluated t2) ->
		    if equalTerm?(t1, t2)
		      then Some true
		      else None
		  | (Unevaluated _, _) -> None
		  | (_, Unevaluated _) -> None
		  | _ -> Some(a1 = a2))
	  else None)
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
    if letrecEnv?(dynSb,storedSb,letrecIds)
      then dynSb
      else extendLetRecSubst(tl dynSb,storedSb,letrecIds)

  def letrecEnv?(dynSb,storedSb,letrecIds) =
          case (dynSb,letrecIds) of
	    | ((idS,_)::rDynSb,id1::rids) ->
	      (idS = id1 & letrecEnv?(rDynSb,storedSb,rids))
	    | _ -> letrecIds = [] & dynSb = storedSb
    
 %% Adapted from HigherOrderMatching 
 sort MatchResult = | Match Subst | NoMatch | DontKnow

 op  patternMatchRules : Match * Value * Subst * Spec * Nat -> Option Value
 def patternMatchRules(rules,N,sb,spc,depth) = 
     case rules 
       of [] -> None
        | (pat,Fun(Bool true,_,_),body)::rules -> 
	  (case patternMatch(pat,N,sb,spc,depth)
	     of Match S -> Some(maybeMkLetOrSubst(evalRec(body,S,spc,depth+1),S,sb))
	      | NoMatch -> patternMatchRules(rules,N,sb,spc,depth)
	      | DontKnow -> None)
	| _ :: rules -> None

 op  patternMatch : Pattern * Value * Subst * Spec * Nat -> MatchResult 

 def patternMatch(pat,N,S,spc,depth) = 
     case pat
       of VarPat((x,_), _) -> Match(addToSubst(S,x,N))
	| WildPat _ -> Match S
	| AliasPat(p1,p2,_) ->
	  (case patternMatch(p1,N,S,spc,depth) of
	     | Match S1 -> patternMatch(p2,N,S1,spc,depth)
	     | result -> result)
	| RecordPat(fields, _) ->
	  (case N of
	     | RecordVal valFields ->
	       foldl (fn ((lbl,rpat),result) ->
		      case result of
			| Match S ->
			  (case lookup(valFields,lbl) of
			     | None -> DontKnow
			     | Some v -> patternMatch(rpat,v,S,spc,depth))
			| _ -> result)
	         (Match S) fields
	     | _ -> DontKnow)
	| EmbedPat(lbl,None,srt,_) -> 
	  (case N of
	     | Constant(lbl2) -> if lbl = lbl2 then Match S else NoMatch
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
	| EmbedPat(lbl,Some p,srt,_) -> 
	  (case N of 
	     | Constructor(lbl2,N2) -> 
	       if lbl = lbl2 
		  then patternMatch(p,N2,S,spc,depth)
	       else NoMatch
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
        | QuotientPat(pat,_,_) ->
	  (case N of
	     | QuotientVal(_,v) -> patternMatch(pat,v,S,spc,depth)
	     | Unevaluated _ -> DontKnow
	     | _ -> NoMatch)
        | RestrictedPat(pat,pred,_) ->
	  (case patternMatch(pat,N,S,spc,depth) of
	     | Match S1 ->
	       (case evalRec(pred,S1,spc,depth+1) of
		 | Bool true  -> Match S1
		 | Bool false -> NoMatch
		 | _ -> DontKnow)
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
  op  maybeMkLetOrSubst: Value * Subst * Subst -> Value
  def maybeMkLetOrSubst(val,newSb,oldSb) =
    case val of
      | Unevaluated t -> Unevaluated(mkLetOrsubst(t,newSb,oldSb))
      | _ -> val

  op  mkLetOrsubst: MS.Term * Subst * Subst -> MS.Term
  def mkLetOrsubst(t,newSb,oldSb) =
    let def splitSubst sb =
          List.foldl (fn ((vr,val),(letSb,substSb)) ->
		 if evalConstant? val	% Could be more discriminating
		  then (letSb,Cons((vr,valueToTerm val),substSb))
		  else (Cons((vr,valueToTerm val),letSb),substSb))
	    ([],[]) sb
    in
    let localSb = ldiff(newSb,oldSb) in
    if localSb = emptySubst then t
      else
      let fvs = freeVars t in
      let usedSb = foldl (fn ((id1,v),rsb) ->
			  case find (fn (id2,_) -> id1 = id2) fvs of
			    | Some vr -> Cons((vr,v),rsb)
			    | None -> rsb)
		     [] localSb
      in
      let (letSb,substSb) = splitSubst usedSb in
      mkLetWithSubst(substitute(t,substSb),letSb)

  %% First list should contain second list as a tail
  op  ldiff: fa(a) List a * List a -> List a
  def ldiff(l1,l2) =
    if l1 = l2 or l1 = [] then []
      else Cons(hd l1,ldiff(tl l1,l2))
      

  %% Evaluation of constant terms
  %% we need to include "Boolean" for "compare", "toString", "show", "pp", etc.
  def evalQualifiers = ["Nat","Integer","Integer_","IntegerAux","String","Char","System","Boolean"]  % "Integer_" is deprecated -- remove at some point
  def evalConstant?(v) =
    case v
      of Unevaluated t -> embed? Fun t
       | _ -> true

  op  intVal: Value -> Integer
  def intVal = fn (Int i) -> i
  op  intVals: List(Id * Value) -> Integer * Integer
  def intVals([(_,x),(_,y)]) = (intVal x,intVal y)

  op  charVal: Value -> Char
  def charVal = fn (Char c) -> c

  op  stringVal: Value -> String
  def stringVal = fn (String s) -> s
  op  stringVals: List(Id * Value) -> String * String
  def stringVals([(_,x),(_,y)]) = (stringVal x,stringVal y)

  op  booleanVal: Value -> Boolean
  def booleanVal = fn (Bool s) -> s
  op  booleanVals: List(Id * Value) -> Boolean * Boolean
  def booleanVals([(_,x),(_,y)]) = (booleanVal x,booleanVal y)

  op  stringIntVals: List(Id * Value) -> String * Integer
  def stringIntVals([(_,x),(_,y)]) = (stringVal x,intVal y)

  op  attemptEval1: String * Value * MS.Term -> Value
  def attemptEval1(opName,arg,f) =
    let def default() = Unevaluated(mkApply(f,valueToTerm arg)) in
    case (opName,arg) of
       | ("-", Int i)         -> Int (- i) 
       | ("~", Int i)         -> Int (- i) % TODO: deprecate
       | ("~", Bool b)        -> Bool (~b)
       | ("pred", Int i)      -> Int (pred i)
       | ("toString", Int i)  -> String (toString i)
       | ("toString", Bool b) -> String (toString b)
       | ("toString", Char c) -> String (toString c)
       | ("show", Int i)      -> String (toString i)
       | ("show", Bool b)     -> String (toString b)
       | ("show", Char c)     -> String (toString c)
       | ("succ",Int i)       -> Int (succ i)

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
       | ("explode",String s) -> List.foldr (fn (c,r) -> Constructor("Cons",RecordVal[("1",Char c),("2",r)]))
                                   (Constant "Nil") (explode s)
       | ("toScreen",String s)  -> let _ = toScreen  s in RecordVal []
       | ("writeLine",String s) -> let _ = writeLine s in RecordVal []

       | ("implode",arg)      ->
         if metaList? arg
	   then String(foldr (fn(Char c,rs) -> (toString c)^rs) "" (metaListToList arg))
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
				   | None -> Constant "None"
				   | Some s -> Constructor("Some",String s))
       | ("garbageCollect",Bool b) -> let _ = garbageCollect b in RecordVal []
       | ("trueFilename",String s) -> String(trueFilename s)

       | ("anyToString", Int i)      -> String (toString i)
       | ("anyToString", Bool b)     -> String (toString b)
       | ("anyToString", Char c)     -> String (toString c)
       | ("anyToString", arg)     -> String (anyToString arg)
       %% Missing System. time, msWindowsSystem?, hackMemory

       | _                      -> default()

  op  attemptEvaln: String * String * List(Id * Value) * MS.Term -> Value
  def attemptEvaln(spName,opName,fields,f) =
    let def default() = Unevaluated(mkApply(f,valueToTerm(RecordVal fields))) in
    case opName of
       %% Int operations
       | "+"   -> Int(+(intVals fields))
       | "*"   -> Int( *(intVals fields))    % Space before * is needed so parser doesn't see a comment!
       | "-"   -> Int(-(intVals fields))
       | "<"   -> if spName = "String"
                    then Bool(<(stringVals fields))
		    else Bool(<(intVals fields))
       | "<="  -> if spName = "String"
                    then Bool(<=(stringVals fields))
		    else Bool(<=(intVals fields))
       %% Following have definitions
       %| ">"   -> Bool(>(intVals fields))
       %| ">="  -> Bool(>=(intVals fields))
       %| "min" -> Int(min(intVals fields))
       %| "max" -> Int(max(intVals fields))
       | "rem" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(rem(x,y))
       | "div" -> let (x,y) = intVals fields in
		  if y = 0 then default()
		    else Int(div(x,y))

       %% string operations
       | "concat" -> String(concat(stringVals fields))
       | "++"  -> String(++(stringVals fields))
       | "^"   -> String(^(stringVals fields))
       | "substring" ->
	 (case fields of
	    | [(_,s),(_,i),(_,j)] ->
	      let sv = stringVal s in
	      let iv = intVal i in
	      let jv = intVal j in
	      if iv <= jv && jv <= length sv
		then String(substring(stringVal s,intVal i,intVal j))
		else default()
	    | _ -> default())
       | "leq" -> Bool(leq(stringVals fields))
       | "lt"  -> Bool(lt( stringVals fields))
       | "sub" -> let (s,i) = stringIntVals fields in
	          if i >= 0 && i < length s
		    then Char(sub(s,i))
		    else default()

    % %% Boolean operations are non-strict
    %% %% Should it be non-strict in first argument as well as second?
    %% | "&"   ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x & y)
    %%     | [(_,Bool false),(_,_)]  -> Bool false
    %%     | [(_,_),(_,Bool false)]  -> Bool false
    %%     | [(_,ut),(_,Bool true)]  -> ut
    %%     | [(_,Bool true),(_,ut)]  -> ut
    %%     | _                       -> default())
    %%  | "or"  ->
    %%  (case fields of
    %%     | [(_,Bool x),(_,Bool y)] -> Bool(x or y)
    %%     | [(_,Bool true),(_,_)]   -> Bool true
    %%     | [(_,_),(_,Bool true)]   -> Bool true
    %%     | [(_,ut),(_,Bool false)] -> ut
    %%     | [(_,Bool false),(_,ut)] -> ut
    %%     | [(_,Unevaluated x),(_,Unevaluated y)] ->
    %%        (case (x,y) of
    %%           | (Apply (Fun (Op (Qualified (_,"~"),fxty),srt,pos1), lhs, pos2), rhs) ->
    %%               if equalTerm? (lhs,rhs) then
    %%                 Bool true
    %%               else
    %%                 default ()
    %%           | (lhs, Apply (Fun (Op (Qualified (_,"~"),fxty),srt,pos1), rhs, pos2)) ->
    %%               if equalTerm? (lhs,rhs) then
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
  op  timeEvalRec:  MS.Term * Subst * Spec * Nat -> Value
  def timeEvalRec(t,sb,spc,depth) =
    time(evalRec(t,sb,spc,depth))

  op  metaListToList: (Value | metaList?) -> List Value
  def metaListToList v =
    case v of
      | Constant "Nil" -> []
      | Constructor("Cons",RecordVal[("1",x),("2",r)]) -> Cons(x,metaListToList r)

  op  metaList?: Value -> Boolean
  def metaList? v =
    case v of
      | Constant "Nil" -> true
      | Constructor("Cons",RecordVal[("1",_),("2",r)]) -> metaList? r
      | _ -> false


  op  printValue: Value -> ()
  def printValue v =
    PrettyPrint.toTerminal(format(80,ppValue (initialize(asciiPrinter,false)) v))

  op  stringValue: Value -> String
  def stringValue v =
    PrettyPrint.toString(format(80,ppValue (initialize(asciiPrinter,false)) v))


  op  ppValue: PrContext -> Value -> Pretty
  def ppValue context v =
    case v of
      | Int         n  -> string (toString n)
      | Char        c  -> string ("#"^toString c)
      | String      s  -> string ("\"" ^ s ^ "\"")
      | Bool        b  -> string (if b then "true" else "false")
      | RecordVal   rm ->
        if tupleFields? rm
	  then prettysNone [string "(",
			    prettysFill(addSeparator (string ", ")
					 (map (fn (_,x) -> ppValue context x) rm)),
			    string ")"]
	  else prettysNone [string "{",
			    prettysFill(addSeparator (string ", ")
					  (map (fn (id,x) ->
						   blockLinear
						   (0,
						    [(0,string  id),
						     (0,string  " = "),
						     (0,ppValue context x)]))
					       rm)),
			    string "}"]
      | Constructor("Cons",arg as RecordVal[(_,_),(_,_)]) ->
	(case valueToList v of
	   | Some listVals ->
	     prettysNone [string "[",
			  prettysFill(addSeparator (string ", ")
					(map (ppValue context) listVals)),
			  string "]"]
	   | None -> prettysFill[string "Cons",string " ",ppValue context arg])
      | Constructor (id,arg) -> prettysFill [string id,string " ",ppValue context arg]
      | Constant          id -> string id
      | QuotientVal (f,arg)  -> prettysFill [string "quotient",string " ",
					     case f of
					       | Closure _ -> string "<Closure>"
					       | _ -> ppValue context f,string " ",
					     ppValue context arg]
      | ChooseClosure(cl,_)  ->
	prettysFill [string "choose",string " <Closure> ",
		     case cl of
		       | Closure _ -> string "<Closure>"
		       | _ -> ppValue context cl]
      | Closure(_,sb)  -> prettysNone[string "<Closure {",
				      prettysFill(addSeparator (string ", ")
					(map (fn (id,x) ->
					      blockLinear
					        (0,
						 [(0,string  id),
						  (0,string  " -> "),
						  (0,ppValue context x)]))
					 sb)),
				      string "}>"]
      | RecClosure(_,sb,ids)  -> 
	prettysNone[string "<Closure {",
		    prettysFill(addSeparator (string ", ")
				  (map (fn (id,x) ->
					blockLinear
					  (0,
					   [(0,string  id),
					    (0,string  " -> "),
					    (0,ppValue context x)]))
				   sb)),
		    string "}, ",
		    string "{",
		    prettysFill(addSeparator (string ", ") (map (fn id -> string id) ids)),
		    string "}>"]
      | Unevaluated t  -> prettysNone[string "<Unev: ",
				      ppTerm context ([],Top:ParentTerm) t,
				      string ">"]

  op  valueToList: Value -> Option(List Value)
  def valueToList v =
    case v of
      | Constructor("Cons",RecordVal[(_,a),(_,rl)]) ->
        (case valueToList rl of
	  | Some l -> Some(Cons(a,l))
	  | None -> None)
      | Constant "Nil" -> Some []
      | _ -> None

  op  valueToTerm: Value -> MS.Term
  def valueToTerm v =
    case v of
      | Int         n  -> mkNat n
      | Char        c  -> mkChar c
      | String      s  -> mkString s
      | Bool        b  -> mkBool b
      | RecordVal   rm -> mkRecord(map (fn (id,x) -> (id,valueToTerm x)) rm)
      %% Punt on the sorts for now; could add sort fields to Constructor and Constant
      | Constructor (id,arg) -> mkApply(mkEmbed1(id,unknownSort), valueToTerm arg)
      | Constant    id -> mkEmbed0(id,unknownSort)
      | QuotientVal (f,arg)  ->
        let argtm = valueToTerm arg in
	mkQuotient(valueToTerm f,argtm,termSort argtm)
      | ChooseClosure(a,srt) -> mkApply(mkFun(Choose,srt),valueToTerm a)
      | Closure(f,sb)   -> mkLetOrsubst(Lambda(f,noPos),sb,emptySubst)
      | RecClosure(f,_,_) -> Lambda(f,noPos)
      | Unevaluated t  -> t

  op  unknownSort: Sort
  def unknownSort = mkTyVar "Unknown"

  %% Generally useful utility
  op  loopn: fa(a) (Nat * a -> a) -> a -> Nat -> a
  def loopn f init n =
    let def loop(i,result) =
          if i = n then result else loop(i+1,f(i,result))
    in loop(0,init)

  op termToValue : MS.Term -> Value
  def termToValue term =
    case term of
      | Fun (Nat n,srt,pos) -> Int n
      | Fun (Char c,srt,pos) -> Char c
      | Fun (String s,srt,pos) -> String s
      | Record (flds,pos) -> RecordVal (map (fn (id,x) -> (id,termToValue x)) flds)
      | Apply (Fun (Embed (id,b),srt,pos),t2,srt2) -> Constructor (id, termToValue t2)
      | Fun (Embed (id,b),srt,pos) -> Constant id
      | _ -> Unevaluated term

 endspec
%%% 
