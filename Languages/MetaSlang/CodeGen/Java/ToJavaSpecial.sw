(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(**
 * this spec contains special translation rules for Java, e.g., translation from predefined MetaSlang ops
 * to java.lang method (String utilities)
 *)

JGen qualifying
spec

  import ToJavaBase
  import ToJavaStatements
  import Monad

 %op  JGen.specialTermToExpressionM: TCx * JGen.Term * Nat * Nat -> JGenEnv (Option (JavaBlock * JavaExpr * Nat * Nat))
  def JGen.specialTermToExpressionM(tcx,term,k,l) =
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
	if (length s) < size then s else subFromTo(s,0,size)
    in
    let
      def check4StaticOrNew (classid, opid, allargs) =
	% let _ = writeLine ("    check4StaticOrNew: classid = " ^ classid ^ ", opid = " ^ opid) in
	if (classid = UnQualified) then 
	  % let _ = writeLine ("    Unqualified class (which means???)") in
	  % let _ = writeLine ("    ------------") in
	  return None
	else
	  {
	   (s,argexprs,k,l) <- translateTermsToExpressionsM(tcx,allargs,k,l);
	   % check, whether prefix of op is "new"; in this special case,
	   % the constructor of the class is invoked
	   let expr = if stringPrefix(opid,3) = "new" then
	                % invoke the constructor
                	% let _ = writeLine ("    Constructor") in
			(CondExp (Un (Prim (NewClsInst(ForCls(([],classid), argexprs, None)))), None))
		      else
			% invoke the static method
			%% Accord note:  expressions such as  foo.field can arrive here (with opid = "field"),
			%%               to produce field(foo), which later transforms to foo.field
			% let _ = writeLine ("    Static method") in
			% let _ = writeLine ("    fn   = " ^ classid ^ "#" ^ opid) in
			% let _ = writeLine ("    args = " ^ anyToString argexprs) in
			mkMethInvName(([classid],opid),argexprs)
	   in
	     % let _ = writeLine ("    Expr = " ^ anyToString expr) in
	     % let _ = writeLine ("    ------------") in
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

    %% this is part of the BitString hack (see below):
    let
      def bitStringOp1(opid,t1,k,l) =
	{
	 (block,e1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 let res = mkUnExp(opid,[e1]) in
	 return (Some(block,res,k,l))
	}
      def bitStringOp(opid,t1,t2,k,l) =
	{
	 (block,[e1,e2],k,l) <- translateTermsToExpressionsM(tcx,[t1,t2],k,l);
	 let res = mkBinExp(opid,[e1,e2]) in
	 return (Some(block,res,k,l))
	}
    in
    %% ----------------------------------------------

    case term of

      | Apply(Apply(Fun(Op(Qualified(newq,"new"),_),_,_),Fun(Op(Qualified(_,className),_),_,_),_),arg,_) ->
       %let _ = writeLine("found new, qualifier="^newq^", className="^className^", args="^(printTerm arg)) in
	let args = (case arg of
		      | Record(fields,_) -> map (fn(_,t) -> t) fields
		      | _ -> [arg])
	in
	check4StaticOrNew(className,"new",args)
	%return None

      | Apply(Fun(Op(Qualified(_,"currentTimeMillis"),_),_,_),_,_) ->
        let expr = mkMethInvName((["System"],"currentTimeMillis"),[]) in
	return(Some([],expr,k,l))

      | Apply (Fun (Op (Qualified ("System", "fail"), _), 
		    Arrow (dom_type, cod_type, _), 
		    _), 
	       arg, 
	       _) 
	->
	%% We want to turn System.fail into a throw expression, 
	%% but throw is a statement, so we construct the following 
	%% (somewhat tricky) Java expression that throws an exception:
	%%
	%% (new Object() { public <return_type> throwException(String s) {
        %%                     throw new IllegalArgumentException(s);
        %%                 }
        %%               }).throwException (<arg_expr>)
        %%
	%% where <return_type> is the translation of the codomain of the 
	%%                       arrow type assigned to fail by the type-checker,
	%%
	%%   and <arg_expr>    is the translation of the argument to fail, a string

	let 
          def mk_prim p = 
	    CondExp (Un (Prim p), None) 

	  def mk_new (class_name, args, opt_body) = 
	    mk_prim (NewClsInst (ForCls (([], class_name), args, opt_body)))
	in
        {
         (s, arg_expr, k, l) <- termToExpressionM (tcx, arg, k, l);
	 java_result_type    <- tt_v3M cod_type;

	 let name_of_throwing_method = "throwException"         in
	 let var_name                = "msg"                    in
	 let java_string_type        = (Name ([], "String"), 0) in % should be same as tt_v3M dom_type 
	 
	 let throwing_method_hdr : MethHeader = ([Public], 
						 Some java_result_type,
						 name_of_throwing_method,
						 [(false, java_string_type, (var_name, 0))], 
						 []) 
	 in
	 let throwing_block   = (let new_exception = mk_new ("IllegalArgumentException",
							     [mk_prim (Name ([], var_name))],
							     None)
				 in
				   [Stmt (Throw new_exception)])
	 in
	 let throwing_method  = (throwing_method_hdr, Some throwing_block) in
	 let local_class_body = {
				 handwritten = [],
				 staticInits = [], 
				 flds        = [], 
				 constrs     = [],
				 meths       = [throwing_method], 
				 clss        = [], 
				 interfs     = []
				}
	 in
	 let new_local_class_expr = mk_new ("Object", [], Some local_class_body) in
	 let throwing_expr = mkMethExprInv (new_local_class_expr, name_of_throwing_method, [arg_expr]) in
	 return (Some (s, throwing_expr, k, l))
	}

      | Apply(Fun(Op(Qualified("System","writeLine"),_),_,_),t,_) -> 
	{
	 (s,argexpr,k,l) <- termToExpressionM(tcx,t,k,l);
	 let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	 return(Some (s,expr,k,l))
	}

      | Apply(Fun(Op(Qualified("System","toScreen"),_),_,_),t,_) -> 
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

      | Apply(Fun(Op(Qualified("String","subFromTo"),_),_,_),Record([(_,t1),(_,t2),(_,t3)],_),_) ->
	{
	 (s1,argexpr1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 (s2,argexpr2,k,l) <- termToExpressionM(tcx,t2,k,l);
	 (s3,argexpr3,k,l) <- termToExpressionM(tcx,t3,k,l);
	 let opid = "substring" in
	 let expr = mkMethExprInv(argexpr1,opid,[argexpr2,argexpr3]) in
	 return(Some (s1++s2++s3,expr,k,l))
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

      | Apply(Fun(Op(Qualified("String",at_or_sub),_),_,_),Record([(_,t1),(_,t2)],_),_)
          | at_or_sub in? ["@", "sub"] ->
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
	let srt = Arrow(boolType,boolType,b):MSType in
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
      | Apply(Fun(Op(Qualified("Char",fun as "toString"),_),_,_),t,_) -> charFun(fun,t)

      %% special cases for the BitString class (hack)
      | Apply(Fun(Op(Qualified(_,"complement"),_),_, _), t1,b) -> bitStringOp1(BitNot,t1,k,l)
      | Apply(Fun(Op(Qualified(_,"notZero"),_),_, _), t1,b) ->
	{
	 (block,e1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 let res = mkBinExp("!=",[e1,mkJavaNumber 0]) in
	 return (Some(block,res,k,l))
	}
      | Apply(Fun(Op(Qualified(_,"leftShift"),_),_, _), Record([(_,t1),(_,t2)],_),b) -> bitStringOp("<<",t1,t2,k,l)
      | Apply(Fun(Op(Qualified(_,"rightShift"),_),_, _), Record([(_,t1),(_,t2)],_),b) -> bitStringOp(">>>",t1,t2,k,l)
      | Apply(Fun(Op(Qualified(_,"andBits"),_),_, _), Record([(_,t1),(_,t2)],_),b) -> bitStringOp("&",t1,t2,k,l)
      | Apply(Fun(Op(Qualified(_,"xorBits"),_),_, _), Record([(_,t1),(_,t2)],_),b) -> bitStringOp("^",t1,t2,k,l)
      | Apply(Fun(Op(Qualified(_,"orBits"),_),_, _), Record([(_,t1),(_,t2)],_),b) -> bitStringOp("|",t1,t2,k,l)
      %% -------------------------------------------

      | Apply(Fun(Op(Qualified("IntegerAux","-"),_),_, _), t1,b) ->  % new version for unary minus
	{
	 (block,e1,k,l) <- termToExpressionM(tcx,t1,k,l);
	 let res = UnOp.mkUnExp(Minus,[e1]) in
	 return (Some(block,res,k,l))
	}

      | Apply (Fun (Op (qid as Qualified (q, id), _), opsrt,_), argterm, b) ->
	{
	 var_to_jexpr <- getLocalVarToJExprFun;  % var_to_jexpr is a hook added for Accord
	 case var_to_jexpr id of             
           | Some jexpr ->       
	     %%  For now, only Accord comes here.
	     %%  TODO: we should probably handle this situation here:
	     %%    For the two "None" cases here, isField? will be true for id in translateApplyToExprM,
	     %%    so translateUserApplToExprM will convert from method invocation to field ref.
	     (case argterm of 
		| Fun (Op (Qualified (var_q, var_id), _), Base (Qualified (type_q, type_id), _, _), _) ->
		  %% presumably type_q = type_id, but we probably don't care
		  if var_q = type_id && var_id = "this" then
		    %% foo(this) [which would be interpreted as this.foo] => foo 
		    % let _ = writeLine ("    [Accord] Declared op indexing off 'this' in : " ^ myPrintTerm term) in
		    % let _ = writeLine ("    ------------") in
		    return (Some ([], jexpr, k, l)) % TODO: are k and l the right thing to use here?
		  else
		    % let _ = writeLine ("    [Accord] Declared Instance var/method [A] in : " ^ myPrintTerm term) in
		    % let _ = writeLine ("    ------------") in
		    return None % see note above
		| _ -> 
		  % let _ = writeLine ("    [Accord] Declared Instance var/method [B] in : " ^ myPrintTerm term) in
		  % let _ = writeLine ("    ------------") in
		  return None) % see note above
	   | _ -> 
	     if builtinJavaBaseTypeQualifier? q then 
	       % let _ = writeLine ("    Method within built-in base class: " ^ q ^ "." ^ id) in
	       % let _ = writeLine ("    ------------") in
	       return None 
	     else
	       let argterms = applyArgsToTerms argterm in
	       {
		spc          <- getEnvSpec;
		defined_ops  <- getDefinedOps;  % Accord uses this to keep track of ops defined across many specs

		%% WARNING:  The spec we just obtained here may not be completely kosher!
		%%           It was created by a call to transformSpecForJavaCodeGen,
		%%           which calls poly2mono, which can remove the declarations 
		%%           for types and ops, even if there are references to them
		%%           in terms throughout the spec.

		if  qid in? defined_ops || definedOp? (spc, qid) then  % even declaredOp? can be false here!
		  % let _ = writeLine ("    Normal declared op in: " ^ myPrintTerm term) in
		  % let _ = writeLine ("    ------------") in
		  return None
		else
		  % let _ = writeLine ("    Polymorphic op is not declared as such in: " ^ myPrintTerm term) in
		  % let _ = writeLine ("    ------------") in
		  (case argterms of
		     | allargs as (t1 :: argterms) ->
		       % check whether the first argument has an unrefined type
		       % let _ = writeLine ("  --> checking for method call based on first arg: " ^ myPrintTerm t1) in
		       let t1srt = unfoldBase (spc, inferTypeFoldRecords (spc, t1)) in
		       let t1srt = findMatchingUserType (spc, t1srt) in
		       % let _ = writeLine ("  --> t1srt=" ^ myPrintType t1srt) in
		       if builtinJavaBaseType? t1srt then
			 % let _ = writeLine ("    Type of first arg in " ^ myPrintTerm term ^ "\n    is builtin:: " ^ myPrintType t1srt) in
			 % let _ = writeLine ("    did not find java method call to " ^ printQualifiedId qid) in
			 % let _ = writeLine ("    see if new or static: " ^ printQualifiedId qid) in
			 % check whether the qualifier is present
			 check4StaticOrNew (q, id, allargs)
		       else if (typeIsDefinedInSpec? (spc, t1srt)) then
			 % let _ = writeLine ("    Type of first arg in " ^ myPrintTerm term ^ "\n    is defined:  "^ myPrintType t1srt) in
			 % let _ = writeLine ("    see if new or static: " ^ printQualifiedId qid) in
			 % let _ = writeLine ("    ------------") in
			 % check whether the qualifier is present
			 check4StaticOrNew (q, id, allargs)
		       else
			 % let _ = writeLine ("    Type of first arg in " ^ myPrintTerm term ^ "\n    has no current definition: " ^ myPrintType t1srt) in
			 % let _ = writeLine ("    presume non-static library method definition exists for for " ^ printQualifiedId qid) in
			 % let _ = writeLine ("    ------------") in
			 let opid = id in
			 {
			  (s1, objexpr,  k, l) <- termToExpressionM            (tcx, t1,       k, l);
			  (s2, argexprs, k, l) <- translateTermsToExpressionsM (tcx, argterms, k, l);
			  let expr = mkMethExprInv (objexpr, opid, argexprs) in
			  return (Some (s1++s2, expr, k, l))
			 }
		     | [] -> 
		       % let _ = writeLine ("    No args in " ^ myPrintTerm term) in
		       % let _ = writeLine ("    Did not find java method call to " ^ printQualifiedId qid) in
		       % let _ = writeLine ("    see if new or static: " ^ printQualifiedId qid) in
		       check4StaticOrNew (q, id, []))
		    }}

      % more special cases for the BitString library (hack)
      | Fun(Op(Qualified(q,"Zero"),_),_,_) -> return(Some([],mkJavaNumber 0,0,0))
      | Fun(Op(Qualified(q,"One"),_),_,_) -> return(Some([],mkJavaNumber 1,0,0))
      % ---------------------------------------------------


      | _ -> return None

 %%  op myPrintType : MS.Type -> String
 %%  def myPrintType tm =
 %%    my_trim_whitespace(printType tm)
 %%
 %%  op myPrintTerm : MS.Term -> String
 %%  def myPrintTerm tm =
 %%     my_trim_whitespace(printTerm tm)
 %%
 %%  def my_trim_whitespace (s : String) : String =
 %%    let 
 %%       def trim chars =
 %%	 let (_, new) = 
 %%	     foldl (fn (char, (saw_space?, new)) ->
 %%		    case char of
 %%		      | #\s  -> (true, if saw_space? then new else cons(#\s, new))
 %%		      | #\t  -> (true, if saw_space? then new else cons(#\s, new))
 %%		      | #\n  -> (true, if saw_space? then new else cons(#\s, new))
 %%		      | _ -> (false, cons(char, new)))
 %%	           (true, [])
 %%		   chars
 %%	 in
 %%	   rev new
 %%    in
 %%      implode (trim (explode s))

  op  builtinJavaBaseType?: MSType -> Bool
  def builtinJavaBaseType? typ =
    boolType?   typ || % v3:p1 
    intType?    typ || % v3:p1 
    natType?    typ || % v3:p1 says NO  -- TODO: resolve this
    stringType? typ || % v3:p1 says NO  -- TODO: resolve this
    charType?   typ    % v3:p1 

  op  builtinJavaBaseTypeQualifier?: Qualifier -> Bool  
  def builtinJavaBaseTypeQualifier? q =
    %% TODO: is this a complete set?  See basicQualifiers
    %% v3:p1 
    q in? ["Bool", 
           "Integer", 
           "Nat",     % v3:p1 says NO  -- TODO: resolve this
           "String",  % v3:p1 says NO  -- TODO: resolve this
           "Char"]

 %op  JGen.getPostSubstFun: JGenEnv (JavaExpr -> JavaExpr)
  def JGen.getPostSubstFun =
    return (fn e ->
	    case e of
	      | CondExp (Un (Prim (MethInv (ViaPrim (Name([],"Primitive"), mname, [e1, e2])))), None) ->
	        if mname = "min" || mname = "max" then
		  CondExp (Un (Prim (MethInv (ViaPrim (Name([], "Math"), mname, [e1, e2])))), None)
		else e
	      | _ -> e)


endspec
