% Synchronized with version 1.3 of SW4/Languages/MetaSlang/Transformations/ArityNormalize.sl

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

ArityNormalize qualifying spec { 
 import ../Specs/Environment
 % import StringUtilities          % imported by SpecEnvironment
 % import MetaSlang               % imported by SpecEnvironment

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
               | Cons((WildPat(_,_),_,_),match) -> mA(match,num)
               | _ -> 1
            
     in
        case match
          of [] -> 0
           | Cons((RecordPat(pats,_),_,_),match) -> mA(match,length(pats))
           | _ -> 1
        
 
% The arity map stores the ops having a domain sort consisting of
% a record (possibly subsetted)


 sort UsedNames = StringSet.Set
 sort Gamma         = List(String * Option(Sort * Nat))

 op normalizeArity : Spec * Gamma * UsedNames * MS.Term -> MS.Term
 
 op termArity : Spec * Gamma * MS.Term    -> Option(Sort * Nat)
 op sortArity : Spec * Sort            -> Option(Sort * Nat)
% op opArity   : Spec * String * String -> Option(Sort * Nat)



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

 def sortArity(sp,srt) =
     let 
        def productLength(srt:Sort) = 
            case productOpt(sp,srt)
              of Some fields -> length fields
               | None -> 1
     in
     case arrowOpt(sp,srt)
       of Some(dom,rng) -> 
          let len = productLength(dom) in 
          if ~(len = 1)
             then Some (dom,len)
          else None
        | _ -> None

 def polymorphicDomainOp? (spc, idf) =
   case findTheOp (spc, idf)
     of Some (_,_,(_,srt),_) -> polymorphicDomain?(spc,srt)
      | None                 -> false

 def polymorphicDomain? (sp, srt) =
   case arrowOpt (sp, srt)
     of Some(TyVar _, _) -> true
      | _                -> false

(*
 Arities are associated with term identifiers according to 
 arities in sort definitions or arities of top-level pattern.
 The top-level pattern gets precedence such that the pattern 
 matching algorithm can always generate the pattern with 
 as many arguments as possible.
 *)
  
 def termArity(sp,gamma,term:MS.Term) = 
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
        | Fun(RecordMerge,srt,_) -> sortArity(sp,srt)
        %% sjw: 1/14/02 Have multiple entry points for functions
%        | Fun(Op (Local id,_),_,_) -> opArity(sp,specName,id)
%        | Fun(Op (Qualified(specName,id),_),_,_) -> 
%          opArity(sp,specName,id)
        | Fun(Embed(id,true),srt,_) -> sortArity(sp,srt)
        | Fun _ -> None
        | Let _ -> None
        | LetRec _ -> None
        | Bind _ -> None
        | Lambda(match,_) -> 
          let mArity = matchArity match in
          if mArity = 1
             then None
          else Some(case match
                      of (pat,_,_)::_ -> patternSort pat
                       | _ -> System.fail "Unexpected empty match",mArity)
        | IfThenElse _ -> None
        | Record _ -> None
        | Seq _ -> None
        | _ -> System.fail "Unmatched term"
    
 def mkArityApply(sp,dom,t1,t2,usedNames) =
     % let def makeFreshBoundVariable(id,usedNames) =  freshName("v"^id,usedNames) in
     let
        def unfoldArgument(dom:Sort,t2) = 
            case unfoldBase(sp,dom)
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
                     map 
                      (fn (name,label,srt)->
                      let trm = mkApply((Fun(Project label,mkArrow(dom,srt),noPos)),v) in
                      (label,trm))
                       names
                 in
                 (mkRecord fields,[decl])
               | _ -> 
                (toScreen "Unexpected non-record argument to function ";
                 toScreen (printTerm t2^" :  " );
                 writeLine (printSort dom);
                (t2,[])) 
                  %% This should not happen (?) 
                  %% because we only apply it to terms expecting
                  %% a record of arguments.
     in
     let (t2,decls) = unfoldArgument(dom,t2) in
     mkLet(decls,mkApply(t1,t2))


 def mkArityTuple(sp,term) = 
     let srt = inferType(sp,term) in
     mkApply(mkOp(Qualified("TranslationBuiltIn","mkTuple"),mkArrow(srt,srt)),term)


 def insertPattern(pat:Pattern,result as (usedNames,gamma:Gamma)) = 
     case pat
       of VarPat((v as (id,srt)),_) -> 
          (StringSet.add(usedNames,id),(cons((id,None),gamma)):Gamma)
        | RecordPat(fields,_) -> 
          foldr (fn ((_,p),result) -> insertPattern(p,result)) 
	    result fields

 def insertVars(vars,(usedNames,gamma)) =
     foldr (fn (v as (id,srt),(usedNames,gamma)) -> 
	     (StringSet.add(usedNames,id),(cons((id,None),gamma))))
       (usedNames,gamma) 
       vars

  op  addLocalVars: MS.Term * UsedNames -> UsedNames
  def addLocalVars(t,usedNames) =
    let used = Ref usedNames in
    let _ = mapTerm (id,id,fn (p as VarPat((qid,_),_))
		                -> (used := StringSet.add(!used,qid); p)
	                    | p -> p)
              t
    in !used

  op  etaExpand : Spec * UsedNames * Sort * MS.Term -> MS.Term

  def etaExpand(sp,usedNames,srt,term) = 
      case arrowOpt(sp,srt)
        of None -> term
         | Some(dom,rng) -> 
      (case productOpt(sp,dom)
        of None -> (case term
                      of Lambda _ -> term
                       | _ -> 
                        let (name,_) = freshName("x",usedNames) in
                        let x = (name,dom) in
                        Lambda([((VarPat(x,noPos)),mkTrue(),Apply(term,Var(x,noPos),noPos))],noPos))
         | Some fields ->
      (case fields
        of (*[_] -> term                        % Singleton products don't get changed
         | *) _ ->
      (if (case term
	     of Lambda(rules,_) -> simpleAbstraction rules
	      | _ -> false)
	  then term
	 else
           let (names,_) = freshNames("x",fields,usedNames) in
           let vars = ListPair.map (fn (name,(label,srt)) -> (label,(name,srt))) (names,fields) in
           let trm:MS.Term  = Lambda 
                              ([(RecordPat(map (fn (l,v) -> (l,VarPat(v,noPos))) vars,noPos),
                                    mkTrue(),
                                    Apply(term,Record((map 
                                        (fn (l,v) -> 
                                            (l,(Var(v,noPos)):MS.Term)) vars),noPos),noPos))],noPos)
           in
           trm)))

 def simplePattern pattern = 
      case pattern:Pattern
	of VarPat _ -> true
	 | _ -> false
 
 def simpleAbstraction(rules:Match) = 
     case rules
       of [(RecordPat(fields,_),cond,_)] -> 
	  isTrue cond & all (fn(_,p)-> simplePattern p) fields
        | [(pat,cond,_)] -> simplePattern pat & isTrue cond
	| _ -> false

  def isTrue(term:MS.Term) = 
      case term
	of Fun(Bool true,_,_) -> true
	 | _ -> false

 def normalizeArityTopLevel(sp,gamma,usedNames,term:MS.Term):MS.Term = 
     case term
       of Lambda(rules,a) -> 
          Lambda 
            (map 
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
                        map 
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
         def nonPolymorphicFun? t1 =
           case t1
             of Fun(Op(qid,_),_,_) -> ~(polymorphicDomainOp?(sp,qid))
              | _ -> false
     in
     case term
       of Apply(t1,t2,_) ->
          (if nonPolymorphicFun? t1
             then let (t2,_) = normalizeRecordArguments(t2) in
                  mkApply(t1,t2)        % Multiple entry points if necessary
           else
           case termArity(sp,gamma,t1)
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
                (%toScreen  ("Applying with arity "^Nat.toString num^" : ");
                 %toScreen  (MetaSlangPrint.printTerm t1);
                 %toScreen  " ";
                 %String.writeLine (MetaSlangPrint.printTerm t2);
                 if isRecord 
                   then mkApply(t1,t2)
                 else mkArityApply(sp,dom,t1,t2,usedNames)
                )
          )
        | Record(fields,_) -> 
          let fields = 
              map 
              (fn(id,t)-> (id,normalizeArity(sp,gamma,usedNames,t))) fields in
          mkArityTuple(sp,mkRecord fields)
        | Bind(binder,vars,term,_) -> 
          let (usedNames,gamma) = insertVars(vars,(usedNames,gamma)) in
          mkBind(binder,vars,normalizeArity(sp,gamma,usedNames,term))
        | Let(decls,term,_) -> 
          let (decls,usedNames,gamma) = 
              foldr
              (fn((pat,t1),(decls,usedNames,gamma)) ->
                  let t2 = normalizeArity(sp,gamma,usedNames,t1)                 in
                  let (usedNames,gamma) = insertPattern(pat,(usedNames,gamma))   in
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
                   let (id,_) = v                                                in
                   let usedNames = StringSet.add(usedNames,id)                   in
                   let gamma = cons((id,termArity(sp,gamma,term)),gamma)         in
                   (usedNames,gamma))
                           (usedNames,gamma)
                                decls
          in
          let decls = 
              map 
              (fn(v,trm) -> (v,normalizeArityTopLevel(sp,gamma,usedNames,trm)))
              decls in
          let term =  normalizeArity(sp,gamma,usedNames,term) in
          mkLetRec(decls,term)
        | IfThenElse(t1,t2,t3,a) -> 
          IfThenElse(normalizeArity(sp,gamma,usedNames,t1),
                     normalizeArity(sp,gamma,usedNames,t2),
                     normalizeArity(sp,gamma,usedNames,t3),a)
        | Seq(terms,a) -> 
          Seq (map (fn trm -> normalizeArity(sp,gamma,usedNames,trm)) terms,a)
        | Lambda _ -> 
          let term = normalizeArityTopLevel(sp,gamma,usedNames,term) in
          convertToArity1(sp,gamma,usedNames,term)
        | Var _ -> convertToArity1(sp,gamma,usedNames,term)
        | Fun _ -> convertToArity1(sp,gamma,usedNames,term)


  def convertToArity1(sp,gamma,usedNames,term):MS.Term = 
      case termArity(sp,gamma,term)
        of None -> term
         | Some (dom,num) ->
	   %% by using "pV" as the prefix, 
	   %% we pass the pV? test in reduceTerm,
	   %% which allows use to include an ignore decl
           %% if the var is not used in the body
           let (name,usedNames) = freshName("pV",usedNames) in
           let x = (name,dom) in
           (Lambda([(VarPat(x,noPos),mkTrue(),
                     mkArityApply(sp,dom,term,mkVar x,usedNames))],noPos))

 

%
% This one ignores arity normalization in sorts, axioms and theorems.
%     

  def arityNormalize (spc) =
    let usedNames = StringSet.fromList(qualifierIds spc.ops) in
    setOps (spc, 
            mapOpMap (fn (aliases, fixity, (tyVars, srt), old_defs)->
		      let new_defs =
		          map (fn (type_vars, term) ->
			       let usedNames = addLocalVars(term,usedNames) in
			       (type_vars,
				normalizeArityTopLevel (spc, [], usedNames,
							etaExpand(spc, usedNames, srt, term))))
			      old_defs
		      in 
			(aliases, fixity, (tyVars, srt), new_defs))
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
