(**
 * this spec contains special translation rules for Java, e.g., translation from predefined MetaSlang ops
 * to java.lang method (String utilities)
 *)

JGen qualifying
spec

  import ToJavaBase
  import ToJavaStatements

  %op specialTermToExpression: TCx * JGen.Term * Nat * Nat * Spec -> Option ((Block * Java.Expr * Nat * Nat) * Collected)
  def specialTermToExpression(tcx,term,k,l,spc) =
    %let _ = writeLine("specialTermToExpression: term="^printTerm(term)) in
    let
      def infixOp(binOp,t1,t2) =
        let ((s1,argexpr1,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
        let ((s2,argexpr2,k,l),col2) = termToExpression(tcx,t2,k,l,spc) in
	let expr = CondExp(Bin(binOp,
			       Un(Prim(Paren(argexpr1))),
			       Un(Prim(Paren(argexpr2)))),
			   None) in
	Some ((s1++s2,expr,k,l),concatCollected(col1,col2))
    in
    let
      def stringConcat(t1,t2) =
	infixOp(Plus,t1,t2)
    in
    let
      def stringCompare(binOp,t1,t2) =
        let Var ((var_name,_), _) = t1 in
        let ((s,arg_expr, k,l),col) = termToExpression(tcx,t2,k,l,spc) in
	let minv = MethInv (mkViaPrimMI (Name ([], var_name), "compareTo", [arg_expr])) in
	let expr = CondExp(Bin(binOp,
			       Un (Prim minv),
			       Un (Prim (IntL 0))),
			   None) in
	Some ((s,expr,k,l),col)
    in
    let
      def intToString(t) =
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["String"],"valueOf"),[argexpr]) in
	Some ((s,expr,k,l),col)
    in
    let
      def stringToInt(t) =
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["Integer"],"parseInt"),[argexpr]) in
	Some ((s,expr,k,l),col)
    in
    let
      def stringPrefix(s,size) =
	if (length s) < size then s else substring(s,0,size)
    in
    let
      def check4StaticOrNew(classid,opid,allargs) =
	%let _ = writeLine("check4StaticOrNew: classid="^classid^", opid="^opid) in
	if (classid = UnQualified) then None
	else
	  let ((s,argexprs,k,l),col) =
	  translateTermsToExpressions(tcx,allargs,k,l,spc) in
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
	  Some ((s,expr,k,l),col)
    in
    let
      def charFun(fun,t) =
	let jfun = case fun of
	             | "isNum" -> "isDigit"
	             | "isAlpha" -> "isLetter"
	             | "isAlphaNum" -> "isLetterOrDigit"
	             | _ -> fun
	in
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["Character"],jfun),[argexpr]) in
	Some ((s,expr,k,l),col)
    in
    case term of
      | Apply(Fun(Op(Qualified("System","fail"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	%let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	let def mkPrim p = CondExp(Un(Prim p),None) in
	% this (painfully) constructs the following Java expression that throws an exception:
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
	Some ((s,expr,k,l),col)

      | Apply(Fun(Op(Qualified("String","writeLine"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	Some ((s,expr,k,l),col)

      | Apply(Fun(Op(Qualified("String","toScreen"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	Some ((s,expr,k,l),col)

      | Apply(Fun(Op(Qualified("String","concat"),_),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","++"),    _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","^"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","<"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringCompare(Lt,t1,t2)
      | Apply(Fun(Op(Qualified("String",">"),     _),_,_),Record([(_,t1),(_,t2)],_),_) -> stringCompare(Gt,t1,t2)

      | Fun(Op(Qualified("String","newline"),_),_,_) ->
	let sep = mkJavaString "line.separator" in
	let expr = mkMethInvName((["System"],"getProperty"),[sep]) in
	Some ((mts,expr,k,l),nothingCollected)

      | Apply(Fun(Op(Qualified("String","length"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let opid = "length" in
	let expr = mkMethExprInv(argexpr,opid,[]) in
	Some ((s,expr,k,l),col)

      | Apply(Fun(Op(Qualified("String","substring"),_),_,_),Record([(_,t1),(_,t2),(_,t3)],_),_) ->
        let ((s1,argexpr1,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
        let ((s2,argexpr2,k,l),col2) = termToExpression(tcx,t2,k,l,spc) in
        let ((s3,argexpr3,k,l),col3) = termToExpression(tcx,t3,k,l,spc) in
	let opid = "substring" in
	let expr = mkMethExprInv(argexpr1,opid,[argexpr2,argexpr3]) in
	Some ((s1++s2++s3,expr,k,l),concatCollected(col1,concatCollected(col2,col3)))
      | Apply(Fun(Op(Qualified("String","sub"),_),_,_),Record([(_,t1),(_,t2)],_),_) ->
        let ((s1,argexpr1,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
        let ((s2,argexpr2,k,l),col2) = termToExpression(tcx,t2,k,l,spc) in
	let opid = "charAt" in
	let expr = mkMethExprInv(argexpr1,opid,[argexpr2]) in
	Some ((s1++s2,expr,k,l),concatCollected(col1,col2))
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
	let res = termToExpression(tcx,t,k,l,spc) in
	Some res
      | Apply(Fun(Iff,     _, _), Record([(_,t1),(_,t2)],_),b) ->
	let srt = Arrow(boolSort,boolSort,b):Sort in
	let nott2 = Apply(Fun(Not,srt,b),t2,b) in
	let t = IfThenElse(t1,t2,nott2,b) in
	let res = termToExpression(tcx,t,k,l,spc) in
	Some res

      | Apply(Fun(Op(Qualified("Char",fun as "isNum"),_),_,_),t,_) -> 
	%let _ = writeLine("isNum used.") in
	charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isAlpha"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isAlphaNum"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isLowerCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "isUpperCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "toLowerCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(Qualified("Char",fun as "toUpperCase"),_),_,_),t,_) -> charFun(fun,t)
      | Apply(Fun(Op(qid as Qualified(qual,id),_),opsrt,_),argterm,b) ->
	if builtinBaseTypeId?(qual) then None else
	%let _ = writeLine("checking for method call of "^qual^"."^id) in
	let argterms = applyArgsToTerms(argterm) in
	%if ~(opIdIsDefinedInSpec?(spc,id)) then
	if (case AnnSpec.findTheOp(spc,qid) of Some _ -> false | _ -> true) then
	  %let _ = writeLine("    "^(printQualifiedId qid)^" found, #argterms="^(toString(length(argterms)))) in
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
		 let ((s1,objexpr,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
		 let ((s2,argexprs,k,l),col2) = translateTermsToExpressions(tcx,argterms,k,l,spc) in
		 let expr = mkMethExprInv(objexpr,opid,argexprs) in
		 Some ((s1++s2,expr,k,l),concatCollected(col1,col2))
	       else
		 % check whether the qualifier is present
		 check4StaticOrNew(qual,id,allargs)
	     | [] -> check4StaticOrNew(qual,id,[]))
	else
	  %let _ = writeLine("    "^(printQualifiedId qid)^" *not* found in spec.") in
	  None
      | _ -> None

endspec
