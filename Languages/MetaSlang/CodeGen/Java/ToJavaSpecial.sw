(**
 * this spec contains special translation rules for Java, e.g., translation from predefined MetaSlang ops
 * to java.lang method (String utilities)
 *)

%JGen qualifying
spec

  import ToJavaBase
  import ToJavaStatements
  import Monad

  %op  specialTermToExpressionM: TCx * JGen.Term * Nat * Nat -> JGenEnv (Option (Block * Java.Expr * Nat * Nat))
  def specialTermToExpressionM(tcx,term,k,l) =
    %let _ = writeLine("specialTermToExpression: term="^printTerm(term)) in
    let
      def infixOp(binOp,t1,t2) =
	{
	 (s1,argexpr1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 (s2,argexpr2,k,l) <- termToExpressionM(tcx,t2,k,l);
	 let expr = CondExp(Bin(binOp,
				Un(Prim(Paren(argexpr1))),
				Un(Prim(Paren(argexpr2)))),
			    None)
	 in
	 return(Some (s1++s2,expr,k,l))
	}
    in
    let
      def stringConcat(t1,t2) =
	infixOp(Plus,t1,t2)
    in
    let
      def stringCompare(binOp,t1,t2) =
        let Var ((var_name,_), _) = t1 in
	{
	 (s,arg_expr, k,l) <- termToExpressionM(tcx,t2,k,l);
	 let minv = MethInv (mkViaPrimMI (Name ([], var_name), "compareTo", [arg_expr])) in
	 let expr = CondExp(Bin(binOp,
				Un (Prim minv),
				Un (Prim (IntL 0))),
			    None)
	 in
	 return(Some(s,expr,k,l))
	}
    in
    let
      def intToString(t) =
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["String"],"valueOf"),[argexpr]) in
	 return(Some (s,expr,k,l))
	}
    in
    let
      def stringToInt(t) =
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["Integer"],"parseInt"),[argexpr]) in
	 return(Some (s,expr,k,l))
	}
    in
    let
      def stringPrefix(s,size) =
	if (length s) < size then s else substring(s,0,size)
    in
    let
      def check4StaticOrNew(classid,opid,allargs) =
	%let _ = writeLine("check4StaticOrNew: classid="^classid^", opid="^opid) in
	if (classid = UnQualified) then return None
	else
	  {
	   (s,argexprs,k,l) <- translateTermsToExpressionsM(tcx,allargs,k,l);
	   % check, whether prefix of op is "new"; in this special case,
	   % the constructor of the class is invoked
	   let expr = if stringPrefix(opid,3) = "new"
			then
			 % invoke the constructor
			  (CondExp (Un (Prim (NewClsInst(ForCls(([],classid), argexprs, None)))), None))
		      else
			% invoke the static method
			mkMethInvName(([classid],opid),argexprs)
	   in
	   return(Some (s,expr,k,l))
	  }
    in
    let
      def charFun(fun,t) =
	let jfun = case fun of
	             | "isNum" -> "isDigit"
	             | "isAlpha" -> "isLetter"
	             | "isAlphaNum" -> "isLetterOrDigit"
	             | _ -> fun
	in
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["Character"],jfun),[argexpr]) in
	 return(Some (s,expr,k,l))
	}
    in
    case term of
      | Apply(Fun(Op(Qualified("System","fail"),_),_,_),t,_) ->
        {
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 %let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	 let def mkPrim p = CondExp(Un(Prim p),None) in
	 % this constructs the following Java expression that throws an exception:
	 % (new Object() { public void throwException(String s) {
         %                     throw new IllegalArgumentException(s);
         %                 }
         %               }).throwException(argexpr)
	 let mname = "throwException" in
	 let varname = "msg" in
	 let stringtype:Java.Type = (Name ([],"String"),0) in
	 let methheader:MethHeader = ([Public],None,mname,[(false,stringtype,(varname,0))],[]) in
	 let newException = mkPrim(NewClsInst(ForCls(([],"IllegalArgumentException"),[mkPrim(Name ([],varname))],None))) in
	 let throwStmt = Throw(newException) in
	 let block = [Stmt throwStmt] in
	 let meth = (methheader,Some block) in
	 let clsbody = {
			handwritten = [], staticInits = [], flds = [], constrs = [],
			meths = [meth], clss = [], interfs = []
		       }
	 in
	 let newexpr = mkPrim(NewClsInst(ForCls(([],"Object"),[],Some clsbody))) in
	 let expr = mkMethExprInv(newexpr,mname,[argexpr]) in
	 return(Some(s,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("String","writeLine"),_),_,_),t,_) -> 
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	 return(Some (s,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("String","toScreen"),_),_,_),t,_) -> 
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	 return(Some (s,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("String","concat"),_),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","++"),    _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","^"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","<"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringCompare(Lt,t1,t2)
      | Apply(Fun(Op(Qualified("String",">"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringCompare(Gt,t1,t2)

      | Fun(Op(Qualified("String","newline"),_),_,_) ->
	let sep = mkJavaString "line.separator" in
	let expr = mkMethInvName((["System"],"getProperty"),[sep]) in
	return(Some (mts,expr,k,l))

      | Apply(Fun(Op(Qualified("String","length"),_),_,_),t,_) ->
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let opid = "length" in
	 let expr = mkMethExprInv(argexpr,opid,[]) in
	 return(Some (s,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("String","substring"),_),_,_),Record([(_,t1),(_,t2),(_,t3)],_),_) ->
	{
	 (s1,argexpr1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 (s2,argexpr2,k,l) <- termToExpressionM(tcx,t2,k,l);
	 (s3,argexpr3,k,l) <- termToExpressionM(tcx,t3,k,l);
	 let opid = "substring" in
	 let expr = mkMethExprInv(argexpr1,opid,[argexpr2,argexpr3]) in
	 return(Some (s1++s2++s3,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("String","sub"),_),_,_),Record([(_,t1),(_,t2)],_),_) ->
	{
	 (s1,argexpr1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 (s2,argexpr2,k,l) <- termToExpressionM(tcx,t2,k,l);
	 let opid = "charAt" in
	 let expr = mkMethExprInv(argexpr1,opid,[argexpr2]) in
	 return(Some (s1++s2,expr,k,l))
	}
      | Apply(Fun(Op(Qualified("Nat","toString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Nat","natToString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Nat","show"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","toString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","intToString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","show"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","stringToInt"),_),_,_),t,_) -> stringToInt(t)
      | Apply(Fun(Op(Qualified("Nat","stringToNat"),_),_,_),t,_) -> stringToInt(t)

      | Apply(Fun(And,     _, _), Record([(_,t1),(_,t2)],_),_) -> infixOp(CdAnd,t1,t2)
      | Apply(Fun(Or,      _, _), Record([(_,t1),(_,t2)],_),_) -> infixOp(CdOr,t1,t2)
      | Apply(Fun(Implies, _, _), Record([(_,t1),(_,t2)],_),b) ->
	let t = IfThenElse(t1,t2,mkTrue(),b) in
	{
	 res <- termToExpressionM(tcx,t,k,l);
	 return(Some res)
	}
      | Apply(Fun(Iff,     _, _), Record([(_,t1),(_,t2)],_),b) ->
	let srt = Arrow(boolSort,boolSort,b):Sort in
	let nott2 = Apply(Fun(Not,srt,b),t2,b) in
	let t = IfThenElse(t1,t2,nott2,b) in
	{
	 res <- termToExpressionM(tcx,t,k,l);
	 return(Some res)
	}

      | Apply(Fun(Op(Qualified("Char",fun as "isNum"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isAlpha"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isAlphaNum"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isLowerCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isUpperCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "toLowerCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "toUpperCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(qid as Qualified(qual,id),_),opsrt,_),argterm,b) ->
	if builtinBaseTypeId?(qual) then return None else
	%let _ = writeLine("checking for method call of "^qual^"."^id) in
	let argterms = applyArgsToTerms(argterm) in
	%if ~(opIdIsDefinedInSpec?(spc,id)) then
	{
	 spc <- getEnvSpec;
	 if (case AnnSpec.findTheOp(spc,qid) of Some _ -> false | _ -> true) then
	   (case argterms of
	      | allargs as (t1::argterms) ->
	        % check whether the first argument has an unrefined sort
	        %let _ = writeLine("  --> checking for method call: "^printTerm(t1)) in
	        let t1srt = unfoldBase(spc,inferTypeFoldRecords(spc,t1)) in
		let t1srt = findMatchingUserType(spc,t1srt) in
		%let _ = writeLine("  --> t1srt="^(printSort t1srt)) in
		if ~(builtinBaseType? t1srt) && ~(sortIsDefinedInSpec?(spc,t1srt)) then
		 %let _ = writeLine("   found java method call to "^printQualifiedId(qid)) in
		 let opid = id in
		 {
		  (s1,objexpr,k,l) <- termToExpressionM(tcx,t1,k,l);
		  (s2,argexprs,k,l) <- translateTermsToExpressionsM(tcx,argterms,k,l);
		  let expr = mkMethExprInv(objexpr,opid,argexprs) in
		  return(Some (s1++s2,expr,k,l))
		 }
	       else
		 % check whether the qualifier is present
		 check4StaticOrNew(qual,id,allargs)
	     | [] -> check4StaticOrNew(qual,id,[]))
	else
	  %let _ = writeLine("    "^(printQualifiedId qid)^" *not* found in spec.") in
	  return None
       }
      | _ -> return None

endspec
