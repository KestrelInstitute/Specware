% Synchronized with version 1.3 of SW4/Languages/MetaSlang/ToLisp/SpecToLisp.sl

SpecToLisp qualifying spec { 
 import ../../Transformations/PatternMatch
 import ../../Transformations/InstantiateHOFns
 import ../../Transformations/LambdaLift
 import ../../Transformations/RemoveCurrying
 import ../../Transformations/RecordMerge
 import Lisp
 import ../../Specs/StandardSpec

 op lisp : Spec -> LispSpec

 def generateCaseSensitiveLisp? = false
 
 def lispPackages = ["LISP", "COMMON-LISP", 
		     %% Added because of Xanalys packages, but prudent anyway
		     "SYSTEM", "SI", "IO", "BOOTSTRAP",
		     %% Added for cmulisp compatibility
		     "ALIST", "BYTES", "HASH", "HASHTABLE", "SEQ"]

 def lispStrings =
     StringSet.fromList 
       (["NIL","T","CONS","NULL","CAR","CDR","LIST","LISP",
	"APPEND","REVAPPEND","REVERSE","COMPILE","REDUCE",
	"SUBSTITUTE","COUNT","ENCLOSE","EVAL","ERROR","FIRST","LAST",
	"SECOND", "THIRD", "FOURTH", "FIFTH", "SIXTH",
	"SEVENTH", "EIGHTH", "NINTH", "TENTH",
	"UNION", "INTERSECTION", "SET", "SETQ","SOME",
	"ARRAY","POP","PUSH","TOP","REMOVE","GET",
	"REPLACE","PI","DELETE","IDENTITY","REM",
	"NTH","EQ","EQL","EQUAL","ZEROP","ODDP","EVENP",
	"SEARCH","COMPILE","MERGE","RETURN",
	"VECTOR","SVREF","FORALL","EXISTS","SETF","LOOP",
	"OR","AND","NOT","LENGTH","MAP","MEMBER","TIME",
	"CHAR","STRING","SYMBOL","NAT","MAKE-STRING",
	"CONST","IF","APPLY","QUOTE","MIN","GO",
	"PRINT", "READ", "WRITE","LOAD","..",
	"BLOCK","FORMAT","BREAK","SUBST","FIND","CLASS",
	"+","++","**","-","*",">","<","<=",">= ","\\=",
	"BOOLEAN", "INTEGER", "SHADOW", "TRACE", "WHEN"]
       ++ lispPackages)

 def notReallyLispStrings =
       ["C","D","I","M","N","P","S","V","X","Y","Z","KEY","NAME","VALUE","PATTERN"]

 def isLispString(id) = StringSet.member(lispStrings,id) or
 %% The above is only necessary for packages. They should be done differently in next release.
			(Lisp.uncell(Lisp.apply(Lisp.symbol("CL","FIND-SYMBOL"),
						[Lisp.string(id),
						 Lisp.string("CL")]))
			 & (~(member(id,notReallyLispStrings))))

 op  lispPackage?: String -> Boolean
 def lispPackage? id =
   let pkg = Lisp.apply(Lisp.symbol("CL","FIND-PACKAGE"), [Lisp.string(id)]) in
   Lisp.uncell pkg
     & List.member(Lisp.uncell(Lisp.apply(Lisp.symbol("CL","PACKAGE-NAME"), [pkg])),
		   lispPackages)

 op  ith : fa(a) Nat * String * List(String * a) -> Nat
 def ith(n,id,ids) = 
     case ids
       of [] -> System.fail ("No such index " String.++ id)
	| (id2,_)::ids -> 
	  if id = id2 then n else ith(n + 1,id,ids)

 def projectionIndex(sp,id,srt) = 
     let (dom,_) = arrow(sp,srt) in
     let row = product(sp,dom)   in
     ith(0,id,row)

 def isSpecialProjection(sp,srt,id):Option(String) = 
     case stripSubsorts(sp,srt)
       of Arrow(dom,_,_) -> 
          (case stripSubsorts(sp,dom)
             of Product([(id1,_),(id2,_)],_) -> 
                if id1 = id then Some "car" else Some "cdr"
	      | Product([(id1,_)],_) ->	% Unary record
		Some "functions::id"
              | _ -> None)
       | _ -> None

 op  isConsDataType : Spec * Sort -> Option(Id*Id)
 def isConsDataType(sp,srt):Option(Id*Id) = 
     let
        def isTwoTuple (srt:Sort) = 
            case stripSubsorts(sp,srt) 
              of Product([_,_],_) -> true 
               | _ -> false
     in
        case stripSubsorts(sp,srt)
          of CoProduct([("None",None),("Some",Some _)],_) -> None 
                        % Options never get to be cons types.
                        % This is required to make boot strapping work
                        % as hash-quote-spec prints options without optimization.
                                
           | CoProduct([(i1,None),(i2,Some s)],_) -> 
              if isTwoTuple s then Some(i1,i2) else None
           | CoProduct([(i2,Some s),(i1,None)],_) -> 
              if isTwoTuple s then Some(i1,i2) else None
           | _ -> None
    

def hasConsEmbed(sp,srt) = 
    case stripSubsorts(sp,srt)
      of Arrow(_,rng,_) -> 
         (case isConsDataType(sp,rng)
            of Some _ -> true
             | None -> false)
       | _ -> false

  def isConsIdentifier(sp,id,srt):Option(String) = 
    case isConsDataType(sp,srt)
      of Some(i1,i2) -> Some(if id = i1 then "null" else "consp")
       | None -> None

  def hasConsDomain(sp,id,srt):Option(String) = 
    case stripSubsorts(sp,srt)
      of Arrow(dom,_,_) -> 
         (case isConsDataType(sp,dom)
            of Some(i1,i2) -> Some(if id = i1 then "null" else "consp")
             | None -> None)
       | _ -> None
    

  def patternName (pattern:Pattern) = 
    case pattern 
      of VarPat((id,_),_) -> id 
       | _ -> System.fail ("SpecToLisp.patternName " ^ printPattern pattern)

  def patternNames (pattern:Pattern) = 
    case pattern 
      of VarPat((id,_),_) -> [id] 
       | RecordPat(fields,_) -> List.map (fn (_,p)-> patternName p) fields
       | _ -> System.fail ("SpecToLisp.patternNames " ^ printPattern pattern)


  %% Domain is qualification. First set is strings as given, second is upper case version
  op  userStringMap: Ref(StringMap.Map ((Ref StringSet.Set) * (Ref StringSet.Set)))
  def userStringMap = Ref(StringMap.empty)
  def initializeSpecId() =
      (userStringMap := StringMap.empty)
       
  op  lookupSpecId: String * String * String -> String
  def lookupSpecId(id,ID,pkg) =
    case StringMap.find(! userStringMap,pkg) of
      | Some (userStrings,userUpper) ->
        if StringSet.member(! userUpper,ID)
         then if StringSet.member(! userStrings,id)
              then id
              else "|!"^id^"|"
         else 
         (userUpper := StringSet.add(! userUpper,ID);
          userStrings := StringSet.add(! userStrings,id);
          id)
      | None -> (userStringMap := StringMap.insert(! userStringMap,pkg,
						   (Ref (StringSet.add(empty,id)),
						    Ref (StringSet.add(empty,ID))));
		 id)

  def specId (id,pkg) = 
      % TODO:  Optimize this to avoid needless consing for normal cases?
      let id = translate (fn #| -> "\\|" | #` -> "\\`" | #\\ -> "\\\\" |
                             ch -> Char.toString ch) id
      in
      let ID = if generateCaseSensitiveLisp? then id
                else String.map Char.toUpperCase id in
      if isLispString(ID) 
           or sub(id,0) = #!
        then "|!"^id^"|"
      else 
      if exists (fn ch -> ch = #:) 
           (explode id)
        then "|"^id^"|"
      else lookupSpecId(id,ID,pkg)

  def defaultSpecwarePackage = if generateCaseSensitiveLisp?
                                then "SW-User"
				else "SW-USER"

  def mkLPackageId id = 
      if id = UnQualified then defaultSpecwarePackage
      else
      let id = if generateCaseSensitiveLisp? then id
                else String.map Char.toUpperCase id in
      if isLispString(id) or lispPackage? id
        then id^"-SPEC"
        else id
      
  op  printPackageId: QualifiedId * String -> String
  def printPackageId (id,defPkgNm) = 
      case id
        of Qualified("System","time") -> "TIME"
         | Qualified(pack,id) ->
           let pkg = mkLPackageId pack in
           if pkg = defPkgNm
             then specId(id,"") % !!!
             else
               (pkg ^ "::" ^ specId(id,pkg))
      
  def opArity(sp,idf,srt) =
    case sortArity(sp,srt)
       of None -> None
        | arity ->
          if polymorphicDomainOp?(sp,idf)
           then None
           else arity

def compareSymbols = (mkLOp "eq") : LispTerm

def mkLispTuple valTms =
  case valTms
    of [] -> mkLBool(false)        % Nil
     %% Named tuples can be unary
     | [x] -> x
     | [_,_] -> mkLApply(mkLOp "cons",valTms)
     | _ -> mkLApply(mkLOp "vector",valTms)
     
op  unaryName: String -> String
def unaryName(nm: String): String = nm  % ^ "-1"

op  naryName: QualifiedId * Nat * String -> String
def naryName(Qualified(qid,nm),n,dpn) =
  printPackageId(Qualified(qid,nm ^ "-" ^ (Nat.toString n)),dpn)

def mkLUnaryFnRef(id: String,arity,vars) =
  if StringSet.member(vars,id) then mkLVar id
  else case arity
         of Some _ -> mkLOp (unaryName id)
          | _      -> mkLOp id

%op  mkLApplyArity: String * Option Nat *
def mkLApplyArity(id:QualifiedId,defPkgNm:String,arity,vars,args) =
  let pid = printPackageId(id,defPkgNm) in
  let rator = if StringSet.member(vars,pid) then mkLVar pid
               else case arity
                      of Some _ ->
			 if length(args) = 1
			   then mkLOp (unaryName pid)
			 else
			   mkLOp (naryName(id,length(args),defPkgNm))
                       | _ -> mkLOp pid
  in mkLApply(rator,args)

%
% Ad hoc optimization of the equality operation.
%
def mkLEqualityOp(sp,srt) = 
        case stripSubsorts(sp,srt) 
          of Arrow(dom,_,_) -> 
            (case stripSubsorts(sp,dom)
               of Product([(_,s),_],_) -> 
                  if natSort?(s)  % intSort?(s)
                    then "="
                  else
                  (case stripSubsorts(sp,s) of
		      | Boolean _ -> "eq"
                      | (Base (Qualified("Nat",     "Nat"),     _,_)) -> "="
                      | (Base (Qualified("Integer", "Integer"), _,_)) -> "="
                      | (Base (Qualified("String",  "String"),  _,_)) -> "string="
                      | (Base (Qualified("Char",    "Char"),    _,_)) -> "eq"
                      | _ -> "slang-built-in::slang-term-equals-2")
             | _ -> "slang-built-in::slang-term-equals-2")
        | _ -> "slang-built-in::slang-term-equals-2"

%
% Ad hoc optimization of the inequality operation.
%
def mkLInEqualityOp(sp,srt) = 
        case stripSubsorts(sp,srt) 
          of Arrow(dom,_,_) -> 
            (case stripSubsorts(sp,dom)
               of Product([(_,s),_],_) -> 
                  if natSort?(s)  % intSort?(s)
                    then "/="
                  else
                  (case stripSubsorts(sp,s) of
		     | Boolean _ -> "slang-built-in:boolean-term-not-equals-2"
		     | (Base (Qualified("Nat",     "Nat"),     _,_)) -> "/="
		     | (Base (Qualified("Integer", "Integer"), _,_)) -> "/="
		     | (Base (Qualified("String",  "String"),  _,_)) -> "slang-built-in:string-term-not-equals-2"  % careful! string/= won't work
		     | (Base (Qualified("Char",    "Char"),    _,_)) -> "char/="
		     | _ -> "slang-built-in::slang-term-not-equals-2")
             | _ -> "slang-built-in::slang-term-not-equals-2")
        | _ -> "slang-built-in::slang-term-not-equals-2"

op  mkLTermOp : fa(a) Spec * String * StringSet.Set * (Fun * Sort * a)
                       * Option(MS.Term) -> LispTerm

def mkLTermOp (sp,dpn,vars,termOp,optArgs) =
  case termOp of
    | (Project id,srt,_) -> 
      (case (isSpecialProjection(sp,srt,id),optArgs) of
	 | (Some proj,None) -> 
	   mkLLambda(["!x"],[],mkLApply(mkLOp proj,[mkLVar "!x"]))
	 | (Some proj,Some trm) ->
	   let lTrm = mkLTerm(sp,dpn,vars,trm) in
	   if proj = "functions::id" then lTrm
	   else mkLApply(mkLOp proj,[lTrm])
	 | (None,Some trm) -> 
           let id = projectionIndex(sp,id,srt)  in
	   mkLApply(mkLOp "svref",[mkLTerm(sp,dpn,vars,trm),mkLNat id])
	 | (None,None) -> 
	   let id = projectionIndex(sp,id,srt) in
	   mkLLambda(["!x"],[],mkLApply(mkLOp "svref",[mkLVar "!x",mkLNat id]))
	  )
    | (Not, srt, _ ) ->
      let oper = mkLOp("cl:not") in
      (case optArgs of
        %| None -> oper  
	 | Some arg -> mkLApply (oper,mkLTermList(sp,dpn,vars,arg)))
    | (And, srt, _ ) ->
      % Note: And ("&&") is non-strict -- it might not evalute the second arg.
      %       This means it is not commutative wrt termination.
      let oper = mkLOp("cl:and") in  % lisp AND is also non-strict
      (case optArgs of
        %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
	 | Some arg -> mkLApply (oper,mkLTermList(sp,dpn,vars,arg)))
    | (Or, srt, _ ) ->
      % Note: Or ("||") is non-strict -- it might not evalute the second arg
      %       This means it is not commutative wrt termination.
      let oper = mkLOp("cl:or") in  % lisp OR is also non-strict
      (case optArgs of
        %| None -> oper  % TODO: is this situation possible? Given note above, should it be allowed?
	 | Some arg -> mkLApply (oper,mkLTermList(sp,dpn,vars,arg)))
    | (Implies, srt, _ ) ->
      % Note: Implies ("=>") is non-strict -- it might not evalute the second arg.
      %       This means it is not commutative (to the contrapositive) wrt termination.
      (case optArgs of
        %| None -> mkLOp ("slang-built-in:implies-2") % TODO: is this situation possible? Given note above, should it be allowed?
	 | Some (Record([(_,x),(_,y)],_)) ->
	   % "x => y" = "if x then y else true" = "or (~ x, y)"
	   mkLApply (mkLOp("cl:or"),         
		     [mkLApply(mkLOp "cl:not", 
			       [mkLTerm(sp,dpn,vars,x)]),
		      mkLTerm(sp,dpn,vars,y)]))
    | (Iff, srt, _ ) ->
      % Note: Iff ("<=>") is strict, becasue the second arg must be evaluated, no matter what the value of the first arg is.
      %       This means it is commmuative wrt termination.
      (case optArgs of
        %| None -> mkLOp("cl:eq") % presumably boolean-valued args each evaluate to T or NIL, so this should be ok.
	 | Some (Record([(_, x), (_, y)],_)) ->
	   % "x => y" = "if x then y else ~ y"
	   mkLIf (mkLTerm(sp,dpn,vars,x),
		  mkLTerm(sp,dpn,vars,y),		   
		  mkLApply (mkLOp "cl:not",
			    [mkLTerm(sp,dpn,vars,y)])))
    | (Equals,srt,_) ->
      let oper = mkLOp(mkLEqualityOp(sp,srt)) in
      (case optArgs of
        %| None -> oper
	 | Some arg -> mkLApply (oper,mkLTermList(sp,dpn,vars,arg)))
    | (NotEquals,srt,_) ->
      (case optArgs of
        %| None -> mkLOp(mkLInEqualityOp(sp,srt))
	 | Some arg -> 
	   %% for efficiency, open-code the call to not
           %% let ineq_op = mkLOp(mkLInEqualityOp(sp,srt)) in
           %% mkLApply (ineq_op,mkLTermList(sp,dpn,vars,arg)))
	   let eq_oper = mkLOp(mkLEqualityOp(sp,srt)) in
	   mkLApply(mkLOp "cl:not",
		    [mkLApply (eq_oper,mkLTermList(sp,dpn,vars,arg))]))
    | (Select id,srt,_) -> 
      (case (hasConsDomain(sp,id,srt),optArgs) of
	 | (Some queryOp,None) -> mkLLambda(["!x"],[],mkLVar "!x")
         | (Some queryOp,Some term) -> mkLTerm(sp,dpn,vars,term)
         | (None,None) -> mkLOp "cdr"
         | (None,Some term) -> 
           mkLApply(mkLOp "cdr",[mkLTerm(sp,dpn,vars,term)]))
   | (Embedded id,srt,_) -> 
     let dom = domain(sp,srt) in
     (case (isConsIdentifier(sp,id,dom),optArgs) of
        | (Some queryOp,None) -> 
          mkLLambda(["!x"],[],mkLApply(mkLOp queryOp,[mkLVar "!x"]))
	| (Some queryOp,Some term) -> 
          mkLApply(mkLOp queryOp,[mkLTerm(sp,dpn,vars,term)])
	| (None,None) -> 
	  mkLLambda(["!x"],
		    [],
		    mkLApply (compareSymbols,
			      [mkLApply (mkLOp "car",[mkLVar "!x"]),
			       mkLIntern(id)]))
	| (None,Some term) -> 
	  mkLApply (compareSymbols,
		    [mkLApply (mkLOp "car",[mkLTerm(sp,dpn,vars,term)]),
		     mkLIntern(id)])
        )
   | (Nat n,srt,_) -> mkLInt n
   | (String s,srt,_) -> mkLString s
   | (Bool b,srt,_) -> mkLBool b
   | (Char c,srt,_) -> mkLChar c

   | (Op (id,_),srt,_) -> 
     let arity = opArity(sp,id,srt) in
     (case optArgs of
        | None ->
	  let pid = printPackageId(id,dpn) in
          if functionSort?(sp,srt)
	    then mkLUnaryFnRef(pid,arity,vars)
	  else Const(Parameter pid)
	| Some term ->
	  mkLApplyArity(id,dpn,arity,vars,mkLTermList(sp,dpn,vars,term)))
   | (Embed(id,true),srt,_) ->
     let rng = range(sp,srt) in
     (case isConsDataType(sp,rng) of
        | Some _ ->
	  (case optArgs of
	     | None -> mkLLambda(["!x"],[],mkLVar "!x")
	     | Some term -> mkLTerm(sp,dpn,vars,term))
	| None -> 
          let id = mkLIntern id in
          (case optArgs of
	     | None -> mkLLambda(["!x"],
				 [],
				 mkLApply(mkLOp "cons",
					  [id, mkLVar "!x"]))
	     | Some term -> 
	       mkLApply (mkLOp "cons",[id,mkLTerm(sp,dpn,vars,term)])))
   | (Embed(id,false),srt,_) -> 
     (case isConsDataType(sp,srt) of
	| Some _ -> mkLBool false
        | None   -> mkLApply(mkLOp "list",[mkLIntern id]))
   | (Quotient,srt,_) -> 
     let dom = range(sp,srt) in
     let Quotient(_,equiv,_) = stripSubsorts(sp,dom) in
     let equiv = mkLTerm(sp,dpn,vars,equiv) in
     (case optArgs of
	| None -> mkLApply(mkLOp  "slang-built-in::quotient",[equiv])
        | Some term -> mkLApply(mkLOp "slang-built-in::quotient-1-1",
				[equiv,mkLTerm(sp,dpn,vars,term)]))
   | (Choose,srt,_) ->  
     %% let srt1 = range(sp,srt) in
     %% let dom = domain(sp,srt1) in
     %% Don't need the equivalence relation when doing a choose
     %% let Quotient(_,equiv,_) = stripSubsorts(sp,dom) in
     %% let equiv = mkLTerm(sp,dpn,vars,equiv) in
     (case optArgs of
	| None -> mkLApply(mkLOp "slang-built-in::choose",[])
        | Some term ->
	  mkLApply(mkLOp "slang-built-in::choose-1",
		   [mkLTerm(sp,dpn,vars,term)]))
(*
 *  Restrict and relax are implemented as identities
 *)

   | (Restrict,srt,_) -> 
     (case optArgs of
	| None -> mkLLambda(["!x"],[],mkLVar "!x")
        | Some term -> mkLTerm(sp,dpn,vars,term))
   | (Relax,srt,_) -> 
     (case optArgs of
	| None -> mkLLambda(["!x"],[],mkLVar "!x")
        | Some term -> mkLTerm(sp,dpn,vars,term))
   | _ -> (System.fail ("Unexpected termOp: " ^ (anyToString termOp)))

 op flattenFailWith : MS.Term -> List (MS.Term)

 def flattenFailWith term =
     case term
       of Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _,_),
                Record([(_, t1), (_, t2)],_),_) -> 
          flattenFailWith t1 ++ flattenFailWith t2
        | _ -> [term]


  def lispBlock(sp,dpn,vars,term:MS.Term):LispTerm = 
      let terms = flattenFailWith term in
      let terms = List.map (fn term -> blockAtom(sp,dpn,vars,term)) terms in
      mkLSeq(terms)        

  def blockAtom(sp,dpn,vars,term:MS.Term):LispTerm = 
     case term

       of IfThenElse (t1, t2, Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"),
                                       _), _,_),_) -> 
          IfThen (mkLTerm (sp,dpn,vars, t1), blockAtom (sp, dpn, vars, t2))

        | IfThenElse (t1, t2, t3,_) -> 
          If (mkLTerm (sp, dpn, vars, t1), 
              blockAtom(sp, dpn, vars, t2),
              blockAtom(sp, dpn, vars, t3))

        | Let(decls,body,_) -> 
           let (pats,terms) = ListPair.unzip decls in
          let  names = List.map patternName pats  in
          let  names = List.map (fn id -> specId(id,"")) names      in
          mkLLet(names,
            List.map (fn t -> mkLTerm(sp,dpn,vars,t)) terms,
            blockAtom(sp,dpn,StringSet.addList(vars,names),body))   

        | Apply (Fun(Op (Qualified ("TranslationBuiltIn","mkSuccess"),_),_,_),
		 term,_) -> 
          mkLApply(mkLOp "return",[mkLTerm(sp,dpn,vars,term)])

        | Apply (Fun(Op (Qualified ("TranslationBuiltIn","mkFail"),_),_,_),
                 Fun(String msg,_,_),_) -> 
          mkLApply(mkLOp "error",[mkLString msg])
        
        | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _,_),
                 _,_) -> 
          lispBlock(sp,dpn,vars,term)
        | _ -> System.fail ("Unexpected atom "^printTerm term)

% DIE HARD if the above cases are not exhaustive

op  sortOfOp: Spec * QualifiedId -> Sort
def sortOfOp(sp,id) =
  case findTheOp(sp,id) of
    | Some (_,_,(_,srt),_) -> srt

op fullCurriedApplication : AnnSpec.Spec * String * StringSet.Set * MS.Term
                        -> Option LispTerm
def fullCurriedApplication(sp,dpn,vars,term) =
  let def aux(term,i,args) =
        case term
          of Fun(Op (id,_),srt,_) ->
             if i > 1 & i = curryShapeNum(sp,sortOfOp(sp,id))
               then Some(mkLApply(mkLOp(unCurryName(id,i,dpn)),
				  List.map (fn t -> mkLTerm(sp,dpn,vars,t)) args))
              else None
	   | Fun(Choose,_,_) ->
	     if i = 2
	       then
		 case args of
		   | [f,val] ->
		     if identityFn? f
		       then Some (mkLApply(mkLOp "slang-built-in::quotient-element",
					   [mkLTerm(sp,dpn,vars,val)]))
		       else Some(mkLApply(mkLOp "slang-built-in::choose-1-1",
				 [mkLTerm(sp,dpn,vars,f),
				  mkLTerm(sp,dpn,vars,val)]))
		   | _ -> None		% Shouldn't happen
	       else None
           | Apply(t1,t2,_) -> aux(t1,i+1,cons(t2,args))
           | _ -> None
  in aux(term,0,[])


def mkLTermList(sp,dpn,vars,term:MS.Term) = 
    case term 
      of Record(fields,_) -> List.map (fn (_,t) -> mkLTerm(sp,dpn,vars,t)) fields
       | _ -> [mkLTerm(sp,dpn,vars,term)]

def mkLTerm (sp,dpn,vars,term : MS.Term) = 
  case fullCurriedApplication(sp,dpn,vars,term)
    of Some lTerm -> lTerm
     | _ ->
    (case term
      of Fun termOp -> mkLTermOp(sp,dpn,vars,termOp,None)
       | Var((id,srt),_) -> 
         let id = specId (id,"") in
         if StringSet.member(vars,id)
            then Var id else Op id
       | Let(decls,body,_) ->
         let (pats,terms) = ListPair.unzip decls in
         let  names = List.map patternName pats  in
         let  names = List.map (fn id -> specId(id,"")) names      in
         mkLLet(names,
            List.map (fn t -> mkLTerm(sp,dpn,vars,t)) terms,
            mkLTerm(sp,dpn,StringSet.addList(vars,names),body))   
       | LetRec(decls,term,_) ->
           let
               def unfold(decls,names,terms) = 
                   case decls
                      of [] -> (names,terms)
                       | (name,term)::decls -> 
                         unfold(decls,cons(name,names),cons(term,terms))
                    
           in
           let (names,terms) = unfold(decls,[],[]) in
           let names = List.map (fn (id,_)-> specId(id,"")) names in
           let vars  = StringSet.difference
                            (vars,StringSet.fromList(names))
           in
               (* Letrec bound names are to be treated as *)
               (* op-refs and not var-refs *)
               mkLLetRec(names,
                       List.map (fn t -> mkLTerm(sp,dpn,vars,t)) terms,
                       mkLTerm(sp,dpn,vars,term))

       | Apply(t1,Apply(Fun(Restrict,_,_),t2,_),a) ->
         mkLTerm(sp,dpn,vars,Apply(t1,t2,a))

       | Apply(t1,Apply(Fun(Relax,_,_),t2,_),a) ->
         mkLTerm(sp,dpn,vars,Apply(t1,t2,a))

(*
 * Here we translate the pattern matching monads that are inserted 
 * by the pattern matching translator.
 * They are translated to block constructs.
 *)


       | Apply (Fun(Op (Qualified ("TranslationBuiltIn","block"),_),_,_),t,_) ->
%%         let _ = writeLine("Block "^.printTerm term) in 
         let terms = flattenFailWith t in
         let terms = List.map (fn term -> blockAtom(sp,dpn,vars,term)) terms in
         mkLApply(mkLOp "block",cons(Const (Boolean false),terms))


(** Forced tuples are translated to tuples by translating the argument to mkLTuple
    recursively
 **)
       | Apply(Fun(Op (Qualified ("TranslationBuiltIn","mkTuple"),_),_,_),
                term,_) -> mkLTerm(sp,dpn,vars,term)
(** Functions of arity different from 1 are wrapped in an apply when given only
    1 argument
 **)
       | Apply(Fun(Op (Qualified ("TranslationBuiltIn","mkApply"),_),_,_),
               Record([(_,t1),(_,t2)],_),_) -> 
         mkLApply(mkLOp "apply",[mkLTerm(sp,dpn,vars,t1),mkLTerm(sp,dpn,vars,t2)])

       | Apply (term,term2 as Record(fields,_),_) ->
         (case term
            of Fun termOp -> 
               mkLTermOp(sp,dpn,vars,termOp,Some(term2))
             | _ -> 
               let terms = List.map (fn (_,t) -> mkLTerm(sp,dpn,vars,t)) fields in
               mkLApply (mkLTerm(sp,dpn,vars,term),terms))         
       | Apply(term1,term2,_) -> 
         (case term1
            of Fun termOp -> 
               mkLTermOp(sp,dpn,vars,termOp,Some term2)
             | Var((id,srt),_) ->
               let id = specId(id,"") in
               if StringSet.member(vars,id)
                  then mkLApply(mkLTerm(sp,dpn,vars,term1),
                                [mkLTerm(sp,dpn,vars,term2)])
               else mkLApply(mkLOp id,[mkLTerm(sp,dpn,vars,term2)])
             | _ -> mkLApply(mkLTerm(sp,dpn,vars,term1),
                             [mkLTerm(sp,dpn,vars,term2)]))
       | Record(row,_) ->
           mkLispTuple(List.map (fn (_,t) -> mkLTerm(sp,dpn,vars,t)) row)
       | IfThenElse(t1,t2,t3,_) -> 
           mkLIf(mkLTerm(sp,dpn,vars,t1),
                 mkLTerm(sp,dpn,vars,t2),
                 mkLTerm(sp,dpn,vars,t3))
       | Lambda([(pat,cond,trm)],_) ->
            let names = patternNames pat in 
            let names = List.map (fn id -> specId(id,"")) names    in
                mkLLambda(names,
			  [],
			  mkLTerm(sp,dpn,StringSet.addList(vars,names),trm))
            
       | Seq(terms,_) ->
            mkLSeq(List.map (fn t -> mkLTerm(sp,dpn,vars,t)) terms)
       | _ -> System.fail ("Unexpected term "^printTerm term))
    

(* Poor man's optimizer. 
   Takes care of unnecessary redexes generated by compiler. *)

%
% Count occurrences up to at most 2
%
  def countOccurrence2(x,count,terms:List LispTerm) = 
      case terms
        of [] -> count 
         | Cons(term,terms) -> 
           (case term
              of Apply (term_,terms_) -> 
                 countOccurrence2(x,count,Cons(term_,terms_ ++ terms))

               | Lambda(vars,_,body) -> 
		 %% Was: 2 (* give up *) 
		 %% Never do a real subsitution within a lambda body, but if there are no 
		 %% occurences, return count of 0 to trigger vacuous
		 %% subsitution that allows us to drop unused arg.
                 if member(x,vars) or countOccurrence2(x,0,[body]) = 0
		   then countOccurrence2(x,count,terms)		% Captured
		   else 2 (* give up because may be called more than once *)

               | Letrec(vars,terms1,body) -> 
		 %% Was: 2 (* give up *)
		 %% Similar to Lambda case
		 if member(x,vars) or countOccurrence2(x,0,[body]) = 0
		   then countOccurrence2(x,count,cons(body,terms1 ++ terms))
		   else 2

               | Let(vars,terms1,body) -> 
                 countOccurrence2(x,count,cons(body,terms1 ++ terms))

               | If(t1,t2,t3) -> countOccurrence2(x,count,[t1,t2,t3] ++ terms)
               | IfThen(t1,t2) -> countOccurrence2(x,count,[t1,t2] ++ terms)
               | Seq terms1 ->  countOccurrence2(x,count,terms1 ++ terms)
               | Var y -> 
                 if x = y then 
                 if count > 0 then 2 else
                   countOccurrence2(x,count + 1,terms)
                 else countOccurrence2(x,count,terms)
               | _ -> countOccurrence2(x,count,terms)
            )
      

  def newName(name,names):String = 
      let
          def loop(i) = 
              let
                   n = name^(Nat.toString i)
              in
                  if exists (fn m -> n = m) names
                      then loop(i + 1)
                  else n
               
      in
          loop(1)
      

  def getNames(term:LispTerm) =
      case term
        of Apply(t1,terms) -> 
           foldr (fn(t,names)-> getNames t ++ names) (getNames t1) terms
         | Lambda(vars,_,t) -> vars ++ (getNames t)
         | Op r -> [r]
         | Var r -> [r] 
         | Const _ -> []
         | If(t1,t2,t3) -> 
           (getNames t1)++(getNames t2)++(getNames t3)
         | IfThen(t1,t2) -> 
           (getNames t1)++(getNames t2)
         | (Let(vars,terms,body)) -> 
            vars ++(flatten (List.map getNames terms))++(getNames body)
         | (Letrec(vars,terms,body)) -> 
            vars ++(flatten (List.map getNames terms))++(getNames body)
         | (Seq terms) -> flatten (List.map getNames terms)
         | _ -> System.fail "Unexpected term in getNames"
      

  op rename : String * 
        (List(String) * List(String) * LispTerm) -> 
                List(String) * List(String) * LispTerm
  op rename2 : String * 
        (List(String) * List(LispTerm) * List(String) * LispTerm) -> 
                List(String) * List(LispTerm) * List(String) * LispTerm


  def rename (v,(vars,names,body)) = 
      if exists (fn n -> n = v) names
         then 
         let n = newName(v,names) in
         let body = substitute(v,mkLVar n) body in
             ((cons(n,vars)):List(String),
              (cons(n,names)):List(String),body)
      else (cons(v,vars),names,body)
  def rename2 (v,(vars,terms,names,body)) = 
      if exists (fn n -> n = v) names
         then 
         let n = newName(v,names) in 
         let body = substitute(v,(mkLVar n):LispTerm) body  in 
         let terms = List.map (substitute(v,mkLVar n)) terms  in
             (cons(n,vars),terms,cons(n,names),body)
         
      else (cons(v,vars),terms,names,body)
  op substitute: (String * LispTerm) -> LispTerm -> LispTerm
  def substitute(x,arg) body = 
    let def subst_in_decls decls =
         case arg of
	   | Var new_var ->
             (List.map (fn decl ->
			case decl of
			  | Ignore ignored_vars -> 
			    Ignore (List.map (fn ignored_var -> 
					      if ignored_var = x then new_var else ignored_var)
				             ignored_vars))
	               decls)
	   | _ -> decls
    in
      case body
        of Apply(term,terms) -> 
           Apply(substitute(x,arg) term,
                 List.map (substitute(x,arg)) terms)
         | Lambda(vars,decls,body) -> 
           if exists (fn v -> x = v) vars 
               then mkLLambda(vars,decls,body) 
           else
           let names = getNames(arg) in
           let (vars,names,body) = foldr rename ([],names,body) vars
           in
               mkLLambda(vars,
			 %% we might be renaming a var, in which case
                         %% any decls referring to it must be updated
			 subst_in_decls decls, 
			 substitute(x,arg) body)
           
         | Var y -> if x = y then arg else mkLVar y
         | Let(vars,terms,body) -> 
           if exists (fn v -> x = v) vars 
               then mkLLet(vars,List.map (substitute(x,arg)) terms,body)
           else 
           let terms = List.map (substitute(x,arg)) terms in
           let names = getNames(arg) in
           let (vars,names,body) = foldr rename ([],names,body) vars
           in
               mkLLet(vars,terms,substitute (x,arg) body)
           
         | Letrec(vars,terms,body) -> 
           if exists (fn v -> x = v) vars 
               then mkLLetRec(vars,terms,body)
           else 
           let     names = getNames(arg)
           in let  terms = List.map (substitute(x,arg)) terms
           in let (vars,terms,names,body) = 
                   foldr rename2 ([],terms,names,body) vars  
           in
               mkLLetRec(vars,terms,substitute (x,arg) body)
           
         | If(t1,t2,t3) -> 
           mkLIf(substitute(x,arg) t1,
		 substitute(x,arg) t2,
		 substitute(x,arg) t3)
         | IfThen(t1,t2) -> 
           IfThen(substitute(x,arg) t1,
                  substitute(x,arg) t2)
         | Seq(ts) -> 
           mkLSeq(List.map (substitute(x,arg)) ts)
         | _ -> body
     

  def simpleTerm(term:LispTerm) = 
      case term
        of Var _ -> true
         | Const _ -> true
         | Op _ -> true
         | _ -> false
      

  def pure(term:LispTerm) = 
      case term
        of Var _ -> true
         | Const _ -> true
         | Op _ -> true
         | Lambda _ -> true
         | Apply (Op "cdr",terms)    -> all pure terms % Selector from data type constructors.
         | Apply (Op "car",terms)    -> all pure terms % Selector from tuple.
         | Apply (Op "svref",terms)  -> all pure terms % Projection from record
         | Apply (Op "vector",terms) -> all pure terms % Tuple formation
         | Apply (Op "cons",terms)   -> all pure terms % Tuple formation
         | _ -> false
      
  
  def pV? var_name =
   case explode var_name of
     | #p :: #V :: digits -> all isNum digits % lexer gets upset if no space between "::#"
     | _ -> false

  def reduceTerm(term:LispTerm) = 
      case term
        of Apply(Lambda(xs,_,body),args) -> reduceTerm(Let(xs,args,body))
         | Apply (term,terms) -> 
           let term  = reduceTerm term   in
           let terms = List.map reduceTerm terms in
           (* unused ...
           let (* Ops need an argument *)
               def etaExpandOp(term:LispTerm) = 
                   case term
                     of Op _ -> mkLLambda(["!x"],[],mkLApply(term,[mkLVar "!x"]))
                      | _ -> term
           in *)
           
%% DELETED 6/7/00 nsb to make choose and quotient compile correctly.
%% Where is this relevant?
%           let terms = List.map etaExpandOp terms
%           in
               mkLApply (term,terms)
           
         | Lambda(vars,decls,body) -> 
           let reduced_body = reduceTerm body in
           let unused_and_unignored_pv_vars = 
               List.foldr (fn (var_name, unused_vars) ->
                           if (%% internally generated?
			       %% (For user-defined vars, we do NOT want add an ignore decl,
			       %%  as that would hide useful debugging information.)
			       (pV? var_name) &
			       %% unused?
			       (countOccurrence2 (var_name, 0, [reduced_body]) = 0) &
			       %% not already in an ignore declaration?
			       %% (can happen if there are multiple passes through reduceTerm)
			       ~ (exists (fn decl ->
					  case decl of
					    | Ignore ignored_names ->
					      exists (fn ignored_name -> var_name = ignored_name) 
					             ignored_names
					    | _ -> false)
				         decls) &
			       %% duplications among the vars probably shouldn't happen, 
			       %% but it doesn't hurt to double-check
			       ~ (member (var_name, unused_vars)))
			     then cons (var_name, unused_vars)
			     else unused_vars)
                          []      
                          vars
           in
           let augmented_decls = 
	       (case unused_and_unignored_pv_vars of
		  | [] -> decls
		  | _  -> cons(Ignore unused_and_unignored_pv_vars, decls))
	   in
	     mkLLambda (vars, augmented_decls, reduced_body)
%
% Optimized by deleting pure arguments that do not
% occur in the body at all.
%
         | Let(xs,args,body) -> 
           let body = reduceTerm(body)          in
           let args = List.map reduceTerm args  in
           let xArgs = ListPair.zip (xs,args)   in
%
% Count along multiplicity of a variable in the let bound arguments.
% This prevents capture in sequential substitution.
% ?? Example please...
%
           let terms = cons(body,args)          in
           let xNumArgs = 
               List.map (fn(x,arg) ->
                           if simpleTerm arg then
			     %% If arg is a constant, why do we not substitute if
			     %%  there are 2 or more occurrences of the var among 
			     %%  the args (ignoring the body)?
                             %% Why not always substitute? (I.e. return count of 0 or 1)
			     %% Is this related to the capture issue above?
			     (x, countOccurrence2(x,0,args),  false, arg)
                           else if pure arg then
			     (x, countOccurrence2(x,0,terms), false, arg)
                           else if countOccurrence2(x,0,terms) > 0 then
			     %% arg has possible side effects, and var is used,
			     %% so leave it in place and don't substitute into body
			     (x, 2,                           false, arg)
	                   else
			     %% arg has possible side effects, 
			     %% but var is never used, so convert to sequence
			     (x, 2,                           true, arg)) 
                         xArgs                              
           in
           let (xs,args,body)  = 
                foldr (fn ((x, num, convert_to_seq?, arg), (xs,args,body)) -> 
		       %% If num = 0, then x and arg will vanish from result.
		       %% This happens only if arg is pure or simpleTerm.
		       if num < 2 then
			 (xs, 
			  args, 
			  substitute (x,arg) body)
		       else if convert_to_seq? then
			 %% "let _ = xxx in yyy" => "(xxx ; yyy)"
			 (xs,
			  args,
			  mkLSeq [arg, body])
	               else
			 (cons(x,xs),
			  cons(arg,args),
			  body)) 
		      ([],[],body) 
		      xNumArgs
           in
           mkLLet(rev xs, rev args, body)
         | Letrec(vars,terms,body) -> 
           mkLLetRec(vars,List.map reduceTerm terms,reduceTerm body)
         | If(t1,t2,t3) -> 
           mkLIf(reduceTerm t1,reduceTerm t2,reduceTerm t3)
         | IfThen(t1,t2) -> 
           IfThen(reduceTerm t1,reduceTerm t2)
         | Seq(terms) -> mkLSeq (List.map reduceTerm terms)
         | l -> l
                          
  def lispTerm (sp,dpn,term) = 
      reduceTerm(mkLTerm(sp,dpn,StringSet.empty,term))

  def functionSort?(sp,srt) = 
      case unfoldBase(sp,srt)
        of Arrow _ -> true
         | Subsort(s,_,_) -> functionSort?(sp,s)
         | _ -> false

  def genNNames n = tabulate(n,fn i -> "x"^(Nat.toString i))
  def nTupleDerefs(n,vr) = if n = 2 then [mkLApply(mkLOp "car",[vr]),
                                          mkLApply(mkLOp "cdr",[vr])]
                            else tabulate(n,fn i -> mkLApply(mkLOp "svref",[vr,mkLNat i]) )

  def duplicateString(n,s) =
    case n
      of 0 -> ""
       | _ -> s^duplicateString(n - 1,s)

  op  unCurryName: QualifiedId * Nat * String -> String
  def unCurryName(Qualified(qid,name),n,dpn) =
    printPackageId(Qualified(qid,name^duplicateString(n,"-1")),dpn)

  %% fn x -> fn(y1,y2) -> fn z -> bod --> fn(x,y,z) let (y1,y2) = y in bod
  def unCurryDef(term,n) =
    let def auxUnCurryDef(term,i,params,let_binds) =
          if i > n then (Some (reduceTerm (mkLLambda(params,
						     [],
						     foldl (fn((vars,vals),bod) ->
							    mkLLet(vars,vals,bod))
						     term let_binds)))) : (Option LispTerm)
          else
            case term
              of Lambda (formals,_,body) ->
                 (case formals
                    of [_] -> auxUnCurryDef(body,i+1,params ++ formals,let_binds)
                     | _ -> let newParam = "!x"^(Nat.toString i) in
                            auxUnCurryDef(body,i+1,params ++ [newParam],
                                          [(formals,
                                            nTupleDerefs(length formals,
                                                         mkLVar newParam))]
                                          ++ let_binds))
               %% Lets are effectively pushed inwards
               | Let(vars,terms,body) ->
                 auxUnCurryDef(body,i,params, [(vars,terms)] ++ let_binds)
               | _ -> None        
    in auxUnCurryDef(term,1,[],[])

  % fn(x,y,z) -> f-1(tuple(x,y,z))
  def defNaryByUnary(name,n) =
    let vnames = genNNames n in
    reduceTerm (mkLLambda(vnames,
			  [],
			  mkLApply(mkLOp(name), [mkLispTuple(List.map mkLVar vnames)])))

  % fn(x,y,z) -> f-1(tuple(x,y,z))
  def defAliasFn(name,n) =
    let vnames = genNNames n in
    reduceTerm (mkLLambda(vnames,
			  [],
			  mkLApply(mkLOp(name), List.map mkLVar vnames)))

  % fn x -> f(x.1,x.2,x.3)
  def defUnaryByNary(name,n) =
    reduceTerm (mkLLambda([if n = 0 then "ignore" else "x"],
			  if n = 0 then [Ignore ["ignore"]] else [],
			  mkLApply(mkLOp name, nTupleDerefs(n,mkLVar "x"))))

  % fn x1 -> fn ... -> fn xn -> name(x1,...,xn)
  def defCurryByUncurry(name,n) =
    let def auxRec(i,args) =
          if i > n then mkLApply(mkLOp(name), args)
            else let vn = "x"^(Nat.toString i) in
	         reduceTerm (mkLLambda([vn],
				       [],
				       auxRec(i+1,args++[mkLVar vn])))
    in auxRec(1,[])

  % fn(x1,...,xn) -> f x1 ... xn
  def defUncurryByUnary(name,n) =
    let def auxRec(i,args,bod) =
          if i > n then reduceTerm (mkLLambda(args,[],bod))
            else let vn = "x"^(Nat.toString i) in
                 auxRec(i+1,args++[vn],mkLApply(bod,[mkLVar vn]))
    in auxRec(1,[],mkLOp name)

  op renameDef? : ListADT.LispTerm -> Option String
  def renameDef? term =
    case term
      of Lambda([v], _, Apply(Op fnName,[Var vr])) ->
         if v = vr then Some fnName else None
       | _ -> None

  def lisp (spc) =
%     let _   = printSpecToTerminal spc         in
    let _   = initializeSpecId()                          in
    let packages = map mkLPackageId (qualifiers spc.ops) in
    let (defPkgName,extraPackages) = (defaultSpecwarePackage,packages)
%% Make defaultSpecwarePackage be the standard package name rather than some random package
%        case packages
%          of x::r -> (x,r)
%           | [] -> (defaultSpecwarePackage,[])
    in
    let
      def mkLOpDef(qname,name,decl,defs) = % ???
        case decl:OpInfo
          of (op_names, fixity, (tyVars,srt), (type_vars, term)::_) -> % TODO: check for other defs?
             let term = lispTerm(spc,defPkgName,term) in
	     let qid = Qualified(qname,name) in
             let uName = unaryName(printPackageId(qid,defPkgName)) in
             if functionSort?(spc,srt)
                then
                (case (curryShapeNum(spc,srt),sortArity(spc,srt))
                   of (1,None) ->
                      (case term
                         of Lambda (formals,_,_) -> [(uName,term)]
                          | _ -> [(uName,mkLLambda(["!x"], [],
						   mkLApply(term,[mkLVar "!x"])))])
                    | (1,Some (_,arity)) ->
		      let nName = naryName(qid,arity,defPkgName) in
                      (case term
                         of Lambda (formals,_,_) ->
                            let n = length formals in
                            [(nName,
                              if n = arity then term
                              else defNaryByUnary(uName,arity)), % fn(x,y,z) -> f-1(tuple(x,y,z))
                             (uName,
                              if n = arity
                                then defUnaryByNary(nName,n)    % fn x -> f(x.1,x.2,x.3)
                              else term)]
                           | _ ->  % Not sure that arity normalization hasn't precluded this case
                             [(nName,defNaryByUnary(uName,arity)), % fn(x,y,z) -> f-1(tuple(x,y,z))
                              (uName, mkLLambda(["!x"], [],
						mkLApply(term,[mkLVar "!x"])))])
                    | (curryN,None) ->
                      let ucName = unCurryName(qid,curryN,defPkgName) in
                      (case unCurryDef(term,curryN)
                         of Some uCDef ->  % fn x -> fn y -> fn z -> f-1-1-1(x,y,z)
                            [(uName,defCurryByUncurry(ucName,curryN)),
                             (ucName,uCDef)]
                          | _ ->
			    [(uName,term),
			     (ucName,
			      case renameDef? term
				of Some equivFn -> % fn(x,y,z) -> equivFn-1-1-1( x, y,z)
				  %% Questionable call to unCurryName
				   defAliasFn(unCurryName(Qualified(defPkgName,equivFn),
							  curryN,defPkgName),
					      curryN)
				 | _ -> % fn(x,y,z) -> f x y z
				  defUncurryByUnary(uName,curryN))])
                    | (curryN,Some (_,arity)) ->
                      let ucName = unCurryName(qid,curryN,defPkgName) in
		      let nName = naryName(qid,arity,defPkgName) in
                      (case unCurryDef(term,curryN)
                         of Some uCDef ->
                            [(nName,defNaryByUnary(uName,arity)), %fn(x,y,z) -> f-1(tuple(x,y,z))
                             % fn x -> fn y -> fn z -> f-1-1-1(x,y,z)
                             (uName,defCurryByUncurry(ucName,curryN)),
                             (ucName,uCDef)]
                          | _ ->
                       (case term:LispTerm
                         of Lambda (formals,_,_) ->
                            let n = length formals in
                            [(nName,
                              if n = arity then term
                              else defNaryByUnary(uName,arity)), % fn(x,y,z) -> f-1(tuple(x,y,z))
                             (uName,
                              if n = arity
                                then defUnaryByNary(nName,n)    % fn x -> f(x.1,x.2,x.3)
                              else term),
                             (ucName,defUncurryByUnary(uName,curryN))]  % fn(x,y,z) -> f-1 x y z
                          | _ ->
                            [(nName,defNaryByUnary(uName,arity)), % fn(x,y,z) -> f-1(tuple(x,y,z))
                             (uName,mkLLambda(["!x"], [],
					      mkLApply(term,[mkLVar "!x"]))),
                             (ucName,defUncurryByUnary(uName,curryN))])))
               ++ defs
             else cons((uName,term),defs)
           | _ -> defs
    in
    let defs = foldriAQualifierMap mkLOpDef [] spc.ops in
    { name          = defPkgName,
      extraPackages = extraPackages,
      ops         = List.map (fn(n,_)-> n) defs,
      axioms      = [],
      opDefns     = defs
     } : LispSpec
      

  op toLisp        : Spec -> LispSpec
  op toLispEnv     : Spec -> LispSpec
  op toLispFile    : Spec * String * String -> ()
  op toLispFileEnv : Spec * String * String -> ()

  def toLisp spc =
      toLispEnv(spc)

  op  instantiateHOFns?: Boolean
  def instantiateHOFns? = true
  op  lambdaLift?: Boolean
  def lambdaLift? = false
  op  removeCurrying?: Boolean
  def removeCurrying? = false

  def toLispEnv (spc) =
      % let _   = writeLine ("Translating " ^ spc.name ^ " to Lisp.") in
      let spc = setProperties(spc,[]) in % axioms are irrelevant for code generation
      let spc = if removeCurrying?
                 then removeCurrying spc
		 else spc 
      in
      let spc = if instantiateHOFns?
                 then instantiateHOFns spc
		 else spc 
      in
      let spc = if lambdaLift?
                 then lambdaLift spc
		 else spc 
      in
      let spc = translateMatch(spc) in
      let spc = translateRecordMergeInSpec(spc) in
      let spc = arityNormalize(spc) in
      let lisp_spec = lisp(spc) in
      lisp_spec 

  def toLispFile (spc, file, preamble) =  
      toLispFileEnv (spc, file, preamble) 

  def toLispFileEnv (spc, file, preamble) =
      % let _ = writeLine("Writing Lisp file "^file) in
      let spc = toLispEnv (spc) in
      ppSpecToFile (spc, file, preamble)

  op toLispText: Spec -> Text
  def toLispText spc =
      let lSpc = toLispEnv spc in
      let p = ppSpec lSpc in
      format(80, p)
      
 %% Just generates code for the local defs
 def localDefsToLispFile (spc, file, preamble)
    =  let localOps = spc.importInfo.localOps in
       let spc = setOps(spc, mapiAQualifierMap
		              (fn(qualifier,op_name,
				  opinfo as (op_names, fixity, sort_scheme_1, defs_1))
			        -> if memberQualifiedId(qualifier,op_name,localOps)
				     then opinfo
				   else (op_names, fixity, sort_scheme_1, []))
			      spc.ops)
      in toLispFile (spc, file, preamble)
     

(*
This is the same as MetaSlang.toLispFile only with an extra argument
giving the name of lisp package to be used in the generated lisp
file. This is intended to be used to generate code for "anonymous"
specs. These are specs defines by "def S = spec .. end" rather than
"spec S is .. end".  The latter sets the name field in the spec whereas
the former doesn't. Since the name of the package is computed from the
internal specname, we just create a new spec with the given name. The
proper way to do this would be to extend the parameters to the function
lisp (...) There are no references to that function from outside that
file.  This can come later once we come up with a coherent naming scheme.
In the meantime the following does the job.
*)

%   op toLispFileAsPackage : Spec * String * SpecName -> ()
  
%   def toLispFileAsPackage (spc, file, package) =
%    let renamedSpec = {
%      imports = spc.imports,
%      sorts = spc.sorts,
%      ops = spc.ops,
%      properties = spc.properties
%    } : Spec in
%      toLispFile (renamedSpec, file, [])
}

