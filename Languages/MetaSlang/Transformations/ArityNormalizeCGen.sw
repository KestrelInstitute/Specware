% Synchronized with version 1.3 of SW4/Languages/MetaSlang/Transformations/ArityNormalizeCGen.sl

(* 
   normalizeArity(specName,nameSupply,term) 

   normalizes the arities of function applications and tuple formations in term
   such that tuples only appear as arguments to functions that are declared as
   n-ary or to the polymorphic constructor TranslationBuiltIn.mkTuple
   (whose semantics is to be the identity function, but it is translated into
    the adequate constructors that form tuples).

   We assume that nested patterns have been be eliminated using the pattern 
   matching algorithm and that all identifiers are unique (resolveTerm has been
   invoked).



   Let f : fn x -> fn (y,z) -> (+ x y z) 
   then f 1 (2,3)
   translates into: (funcall (f 1) 2 3)

   Let f : fn x -> fn y -> (+ x (car y) (cdr y))
   then f 1 (2,3)
   translates into: (funcall (f 1) (mkTuple 2 3))

   Let f : fn (x,y) -> (+ x y)
   then f z
   translates into: (mkApply f z)	


   def foo(x,y) = x + y

   (fn f -> f(1,2)) foo
	translates to: funcall #' (lambda (f) (funcall f 1 2)) #'foo

 *)

ArityNormalizeCGen qualifying spec {
 import ../Specs/Environment
 % import StringUtilities  	% imported by SpecEnvironment
 % import MetaSlang       	% imported by SpecEnvironment

 op arityNormalize : Spec -> Spec



(*
 * The arity of a match is some n >= 0,
 * when all patterns in the match are records of arity n,
 * otherwise it is 1.
 *)

 op matchArity : Match -> Nat

 def matchArity(match) = 
     let
	def mA(match,num) = 
	    case match:Match
	      of [] -> num
	       | Cons((RecordPat(pats,_),_,_),match) ->
		 if num = length(pats)
		    then mA(match,num)
		 else 1
	       | _ -> 1
	    
     in
	case match
	  of [] -> 0
	   | Cons((RecordPat(pats,_),_,_),match) -> mA(match,length(pats))
	   | _ -> 1
        
 
% The arity map stores the ops having a domain sort consisting of
% a record (possibly subsetted)


 sort UsedNames = StringSet.Set
 sort Gamma 	= List(String * Option(Sort * Nat))

 op normalizeArity : Spec * Gamma * UsedNames * MS.Term -> MS.Term
 
 op termArity : Spec * Gamma * MS.Term    -> Option(Sort * Nat)
 op sortArity : Spec * Sort            -> Option(Sort * Nat)
 op opArity   : Spec * QualifiedId -> Option(Sort * Nat)



(*
 * Freshvar generates a unique suffix with the inserted name.
 *)

 op freshName: String * UsedNames -> String * UsedNames 
 def freshName(name0,names) = 
     let name1 = StringUtilities.freshName(name0,names) in
     (name1,StringSet.add(names,name1))

 def freshNames(name0,xs,names) =
     let (nameList,names) =  
	     foldr (fn (_,(nameList,names)) -> 
		let (name1,names) = freshName(name0,names) in
		(cons(name1,nameList),names))
		([],names) xs
     in
     (nameList,names)

 def opArity (sp, QId) = 
   %let _ = writeLine("(opArity: specName="^specName^", id="^id) in
   case findTheOp (sp, QId)
     of Some (_,_,(_,srt),_) -> let res = sortArity (sp, srt) in
        %let _ = writeLine(")") in
        res
      | None -> 
	%let _ = writeLine(" None)") in
	None
 
 op isShortTuple : fa(A) Nat * List(Id * A) -> Boolean
 def isShortTuple(i,row) = 
     case row
       of [] -> true
	| (lbl,r)::row -> lbl = toString i & isShortTuple(i + 1,row)
      
 def sortArity(sp,srt) =
     let 
	def productLength(srt:Sort) = 
	    case SpecEnvironment.productOpt(sp,srt)
	      of Some fields -> 
		if isShortTuple(1,fields)
		  then length fields 
		else
		  %let _ = writeLine("record(1): "^MetaSlangPrint.printSort(srt)) in
		  1
	       | None -> 1
     in
       case SpecEnvironment.arrowOpt(sp,srt)
	 of Some(dom,rng) -> 
	   let len = productLength(dom) in 
	   if  len > 1
	     then Some (dom,len)
	   else None
	  | _ -> None

 def sortEmbedArity(sp,srt,id:String) =
   let def productLength(srt:Sort) = 
	    case SpecEnvironment.productOpt(sp,srt)
	      of Some fields ->  
		if isShortTuple(1,fields)
		  then length fields 
		else
		  %let _ = writeLine("record(1): "^MetaSlangPrint.printSort(srt)) in
		  1
	       | None -> 1
   in
   let def findCoProduct(srt) =
            %let _ = writeLine("findCoProduct: "^MetaSlangPrint.printSort(srt)) in
            case srt
	      of  CoProduct(fields,_) -> 
		  let field1 = filter (fn(id0,_) -> (id0 = id)) fields in
		  (case field1
		    of [(_,Some srt)] -> Some(productLength(srt))
		      | _ -> None)
		| Quotient(s,t,_) -> findCoProduct(s)
		| Subsort(s,t,_) -> findCoProduct(s)
		| Base(qid,srts,_) ->
		  let def newtypevars(srts,n) =
		          case srts of [] -> []
			    | _::srts -> cons(TyVar("alpha"^toString(n),noPos),
						   newtypevars(srts,n+1))
		  in
		  let srts = newtypevars(srts,0) in
		  let srt = Base(qid,srts,noPos) in
		  %let _ = writeLine("unfolding "^MetaSlangPrint.printSort(srt)^"...") in
		  let usrt = SpecEnvironment.unfoldBase(sp,srt) in
		  if usrt = srt then None
		  else findCoProduct(usrt)
		| _ -> None

   in
   case SpecEnvironment.arrowOpt(sp,srt)
     of Some(dom,rng) -> 
       (case findCoProduct(rng)
	 of None -> sortArity(sp,srt)
	   | Some len ->
	   if  len > 1
	     then Some (dom,len)
	   else None
       )
      | _ -> None


(*
 Arities are associated with term identifiers according to 
 arities in sort definitions or arities of top-level pattern.
 The top-level pattern gets precedence such that the pattern 
 matching algorithm can always generate the pattern with 
 as many arguments as possible.
 *)
  
 def termArity(sp,gamma,term:MS.Term) = 
   %let _ = writeLine("(termArity: "^MetaSlangPrint.printTerm(term)) in
     case term
       of Apply _ -> None
        | Var((id,_),_) -> 
	  (case find (fn (id2,r) -> id = id2) gamma
	     of Some (w,r) -> r
	      | None -> None)
        | Fun(Not,      srt,_) -> sortArity(sp,srt)
        | Fun(And,      srt,_) -> sortArity(sp,srt)
        | Fun(Or,       srt,_) -> sortArity(sp,srt)
        | Fun(Implies,  srt,_) -> sortArity(sp,srt)
        | Fun(Iff,      srt,_) -> sortArity(sp,srt)
        | Fun(Equals,   srt,_) -> sortArity(sp,srt)
        | Fun(NotEquals,srt,_) -> sortArity(sp,srt)
	| Fun(Op (QId,_),_,_) -> 
	  opArity(sp,QId)
	| Fun(Embed(id,true),srt,_) -> 
	  %let _ = writeLine("embed "^id) in
	  sortEmbedArity(sp,srt,id)
	| Fun _ -> None
        | Let _ -> None
        | LetRec _ -> None
        | Bind _ -> None
        | Lambda(match,_) -> 
	  let mArity = matchArity match in
	  if mArity <= 1
	     then None
	  else Some(case match
		      of (pat,_,_)::_ -> patternSort pat
		       | _ -> System.fail "Unexpected empty match",mArity)
	| IfThenElse _ -> None
	| Record _ -> None
	| Seq _ -> None
	| _ -> System.fail "Unmatched term"

    
 def mkArityApply(sp,dom,t1,t2,usedNames) =
     % let def makeFreshBoundVariable(id,usedNames) = freshName("v"^id,usedNames) in % unused
     let
	def unfoldArgument(dom:Sort,t2) = 
            case SpecEnvironment.unfoldBase(sp,dom)
	      of Subsort(s,t,_) -> 
%
% First relax the argument, then restrict the result.
%
		 let relaxOp = mkRelax(s,t) in
		 let t2 = mkApply(relaxOp,t2) in
		 let (t2,decls) = unfoldArgument(s,t2) in
		 let t2 = mkRestriction({pred = t,term = t2}) in
		 (t2,decls)
	       | Product(fields,_) -> 
		 let (names,usedNames) = 
			foldr 
		         (fn((fieldName,srt),(names,usedNames)) ->
			    let (newName,usedNames) = freshName("v"^fieldName,usedNames) in
			    (cons((newName,fieldName,srt),names),usedNames))
			  ([],usedNames) fields
		 in
		 let (x,usedNames) = freshName("x",usedNames) in
		 let decl = (mkVarPat(x,dom),t2) in
		 let v = mkVar(x,dom) in
		 let fields = 
		     List.map 
		      (fn (name,label,srt)->
		      let trm = mkApply(mkProject(label,dom,srt),v) in
		      (label,trm))
		       names
		 in
		 (mkRecord fields,[decl])
	       | _ -> 
		(toScreen "Unexpected non-record argument to function ";
		 toScreen (MetaSlangPrint.printTerm t2^" :  " );
		 writeLine (MetaSlangPrint.printSort dom);
		(t2,[])) 
		  %% This should not happen (?) 
		  %% because we only apply it to terms expecting
		  %% a record of arguments.
     in
     let (t2,decls) = unfoldArgument(dom,t2) in
     mkLet(decls,mkApply(t1,t2))


 def mkArityTuple(sp,term) = 
     let srt = SpecEnvironment.inferType(sp,term) in
     mkApply(mkOp(["TranslationBuiltIn","mkTuple"],mkArrow(srt,srt)),term)


 def insertPattern(pat:Pattern,result as (usedNames,gamma:Gamma)) = 
     case pat
       of VarPat((v as (id,srt)),_) -> 
	  (StringSet.add(usedNames,id),cons((id,None),gamma):Gamma)
	| RecordPat(fields,_) -> 
	  List.foldr 
	     (fn ((_,p),result) -> insertPattern(p,result)) 
		result
		   fields

 def insertVars(vars,(usedNames,gamma)) =
     List.foldr 
	(fn (v as (id,srt),(usedNames,gamma)) -> 
	    (StringSet.add(usedNames,id),cons((id,None),gamma):Gamma))
		(usedNames,gamma) 
		    vars



  op  etaExpand : Spec * UsedNames * Sort * MS.Term -> MS.Term

  def etaExpand(sp,usedNames,srt,term) =
    let def etaExpandAux(dom,term) =
          let (name,_) = freshName("x",usedNames) in
          let x = (name,dom) in
	  (case term
	     of Lambda([(pat as (RecordPat(fields,_)),cond,term1)],a) -> 
	       %let _ = writeLine("etaExpandAux: "^MetaSlangPrint.printTerm(term)) in
	       if (isShortTuple(1,fields)) then term
	       else
		 %let _ = writeLine("  is record...") in
		 % foo({a,b}) = t --> foo(x) = let {a,b} = x in t
		 let res = Lambda([((VarPat(x,noPos)),cond,
				    Let([(pat,Var(x,noPos))],term,noPos))],a) in
		 %let _ = writeLine("res: "^MetaSlangPrint.printTerm(res)) in
		 res

	      | Lambda _ -> term
	      | _ -> 
		 let res = Lambda([(VarPat(x,noPos),mkTrue(),
				    Apply(term,Var(x,noPos),noPos))],noPos) in
	         res)
      in
      case SpecEnvironment.arrowOpt(sp,srt)
	of None -> term
	 | Some(dom,rng) -> 
      case SpecEnvironment.productOpt(sp,dom)
	of None -> etaExpandAux(dom,term)
	 | Some fields ->
	  %let _ = writeLine("etaExpand: "^MetaSlangPrint.printSort(dom)) in
	  if ~(isShortTuple(1,fields)) then 
	    %let _ = writeLine("  is record.") in
	    etaExpandAux(dom,term)
	  else
	    (*case fields
		of [_] -> term			% Singleton products don't get changed
	         |  _ ->*)
      let def etaExpandAux2(term) =
	   let (names,_) = freshNames("x",fields,usedNames) in
	   let vars = ListPair.map (fn (name,(label,srt)) -> (label,(name,srt))) (names,fields) in
	   let trm = Lambda 
	               ([(RecordPat(List.map (fn (l,v) -> (l,VarPat(v,noPos))) vars,noPos),
			  mkTrue(),
			  Apply(term,Record (List.map 
					     (fn (l,v) -> 
					      (l,Var(v,noPos):MS.Term)) vars,noPos),noPos))],noPos)
	   in
	   trm
      in
      case term
	of Lambda([(RecordPat fields,_,_)],_) -> term
	 | _ -> etaExpandAux2(term)

 def normalizeArityTopLevel(sp,gamma,usedNames,term:MS.Term):MS.Term = 
     case term
       of Lambda(rules,a) -> 
	  Lambda 
	    (List.map 
		(fn(pat,cond,body)->
		    let (usedNames,gamma) = insertPattern(pat,(usedNames,gamma)) in
		    (
		     pat,
		     normalizeArity(sp,gamma,usedNames,cond),
		     normalizeArity(sp,gamma,usedNames,body)
		     )
	     ) rules,a)
	| _ -> normalizeArity(sp,gamma,usedNames,term)


 def normalizeArity(sp,gamma,usedNames,term) = 
     let
	def normalizeRecordArguments(t:MS.Term):MS.Term * Boolean = 
	    case t
	      of Record(fields,_) -> 
		 let fields = 
		        List.map 
		        (fn(id,t)-> (id,normalizeArity(sp,gamma,usedNames,t)))
				 fields 
		 in
		 (mkRecord fields,true)
	       | Apply(t1 as (Fun(Restrict,_,_)),t2,a) -> 
		 let (t2,b) = normalizeRecordArguments(t2) in
		 (Apply(t1,t2,a),b)
	       | _ -> 
		 let t = normalizeArity(sp,gamma,usedNames,t) in
		 (t,false)
     in
     case term
       of Apply(t1,t2,_) ->
	 %let _ = writeLine("normalizeArity of apply-term: "^MetaSlangPrint.printTerm(term)) in
	  (case termArity(sp,gamma,t1)
	     of None -> 
		    (%toScreen  ("Applying with arity 1 : ");
		     %toScreen  (MetaSlangPrint.printTerm t1);
		     %toScreen  " ";
		     %writeLine (MetaSlangPrint.printTerm t2);
		     mkApply(normalizeArity(sp,gamma,usedNames,t1),
			     normalizeArity(sp,gamma,usedNames,t2))
		    )
	      | Some (dom,num) -> 
	        let (t2,isRecord) = normalizeRecordArguments(t2) in
		let t1 = case t1 
			   of Var _ -> t1
			    | Fun _ -> t1
			    | _ -> normalizeArityTopLevel(sp,gamma,usedNames,t1) 
		in
		(%toScreen  ("Applying with arity "^toString num^" : ");
		 %toScreen  (MetaSlangPrint.printTerm t1);
		 %toScreen  " ";
		 %writeLine (MetaSlangPrint.printTerm t2);
	         if isRecord 
		   then mkApply(t1,t2)
	         else mkArityApply(sp,dom,t1,t2,usedNames)
		)
	  )
	| Record(fields,_) -> 
	  let fields = 
	      List.map 
	      (fn(id,t)-> (id,normalizeArity(sp,gamma,usedNames,t))) fields in
	  mkArityTuple(sp,mkRecord fields)
	| Bind(binder,vars,term,_) -> 
	  let (usedNames,gamma) = insertVars(vars,(usedNames,gamma)) in
	  mkBind(binder,vars,normalizeArity(sp,gamma,usedNames,term))
	| Let(decls,term,_) -> 
	  let (decls,usedNames,gamma) = 
	      List.foldr
	      (fn((pat,t1),(decls,usedNames,gamma)) ->
		  let t2 = normalizeArity(sp,gamma,usedNames,t1) 		in
		  let (usedNames,gamma) = insertPattern(pat,(usedNames,gamma)) 	in
		  (cons((pat,t2),decls),usedNames,gamma)) 
			([],usedNames,gamma)
			     decls 
          in
	  let term  = normalizeArity(sp,gamma,usedNames,term) in
	  mkLet(decls,term)
	| LetRec(decls,term,_) ->
	  let (usedNames,gamma) = 
	      foldr 
	        (fn((v,term),(usedNames,gamma)) ->
		   let (id,_) = v 						in
		   let usedNames = StringSet.add(usedNames,id) 			in
		   let gamma = cons((id,termArity(sp,gamma,term)),gamma) 	in
		   (usedNames,gamma))
		   	(usedNames,gamma)
				decls
	  in
	  let decls = 
	      List.map 
	      (fn(var,trm) -> (var,normalizeArityTopLevel(sp,gamma,usedNames,trm)))
	      decls in
	  let term =  normalizeArity(sp,gamma,usedNames,term) in
	  mkLetRec(decls,term)
        | IfThenElse(t1,t2,t3,a) -> 
	  IfThenElse(normalizeArity(sp,gamma,usedNames,t1),
		     normalizeArity(sp,gamma,usedNames,t2),
		     normalizeArity(sp,gamma,usedNames,t3),a)
	| Seq(terms,a) -> 
	  Seq (List.map (fn trm -> normalizeArity(sp,gamma,usedNames,trm)) terms,a)
	| Lambda _ -> 
	  let term = normalizeArityTopLevel(sp,gamma,usedNames,term) in
	  convertToArity1(sp,gamma,usedNames,term)
	| Var _ -> convertToArity1(sp,gamma,usedNames,term)
	| Fun _ -> convertToArity1(sp,gamma,usedNames,term)


  def convertToArity1(sp,gamma,usedNames,term):MS.Term = 
    %let _ = toScreen("convertToArity1: termArity "^MetaSlangPrint.printTerm(term) ^"-> ") in
      case termArity(sp,gamma,term)
	of None -> %let _ = writeLine("None") in 
	  term
	 | Some (dom,num) ->
	   let (name,usedNames) = freshName("xx",usedNames) in
	   %let _ = writeLine("var "^name^":"^MetaSlangPrint.printSort(dom)) in
	   let x = (name,dom) in
	   (Lambda([((VarPat(x,noPos)),mkTrue(),
		     mkArityApply(sp,dom,term,mkVar x,usedNames))],noPos))

 

%
% This one ignores arity normalization in sorts, axioms and theorems.
%     

  def arityNormalize (spc) = 
    let usedNames = StringSet.fromList(StringMap.listDomain(spc.ops)) in
    setOps (spc, 
	    StringMap.map (fn m ->
			   StringMap.map 
			    (fn (op_names, fixity, (tyVars, srt), old_opt_def)->
			     let new_opt_def = 
			         mapOption (fn term -> 
					    normalizeArityTopLevel (spc,
								    [],
								    usedNames,
								    etaExpand (spc, usedNames, srt, term)))
			                   old_opt_def
			     in
			     (op_names, fixity, (tyVars, srt), new_opt_def))
			    m)
	                  spc.ops)


}


(****
 	| WildPat  _ -> result
(* These cases do not appear after pattern match compilation, 
   but are listed for independence of possible pattern matching *)
        | AliasPat(p1,p2) -> 
          insertPattern(p1,insertPattern(p2,result))
        | EmbedPat(_,Some p,_) -> insertPattern(p,result)
        | RelaxPat(p,t) -> insertPattern(p,result)
        | QuotientPat(p,t) -> insertPattern(p,result)
        | _ -> result

 ****)
