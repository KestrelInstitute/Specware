(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(**
 * translation of higher order features to Java
 *
 * @author MA
 * @created Sun Jul 13 15:34:43 PDT 2003
 *)

JGen qualifying 
spec
  import ToJavaBase
  import ToJavaStatements

  import Monad

  (**
   * translates a lambda term into a java expression, called from translateToExpression in ToJavaStatements
   *)
  %op JGen.translateLambdaToExpr: TCx * MSTerm * Nat * Nat * Spec -> (JavaBlock * JavaExpr * Nat * Nat) * Collected
  %op JGen.translateLambdaToExprM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
  def JGen.translateLambdaToExprM(tcx,term (*as Lambda((pat,cond,body)::_,_)*),k,l) =
    case term of
      | Fun(Op(qid as Qualified(_,id),_),srt,_) -> translateStandAloneOpToExprM(tcx,(qid,srt),k,l)
      | Fun(Embed(Qualified(_, c),_),srt,_) ->
	let dom = typeDom srt in
	let rng = typeRng srt in
	{
	 apran <- tt_idM rng;
	 rexp <- return(mkMethInv(apran,c,mkNArgsExpr(dom,None)));
	 res <- standAloneFromTypeM (mkReturnStmt(rexp),srt,k,l);
	 return res
	}
      | Fun(Project(id),srt,_) -> 
	let rexp = mkMethInv("arg1",getFieldName(id),[]) in
	standAloneFromTypeM (mkReturnStmt(rexp),srt,k,l)
      | Fun(Restrict,srt,_) -> 
	let rng = typeRng srt in
	{
	 rngid <- tt_idM rng;
	 rexp <- return(mkNewClasInst(rngid,mkNArgsExpr([0],None)));
	 res <- standAloneFromTypeM(mkReturnStmt(rexp),srt,k,l);
	 return res
	}
      | Fun(Relax,srt,_) ->
	let rexp = mkFldAcc(mkVarJavaExpr("arg1"),"relax") in
	standAloneFromTypeM (mkReturnStmt(rexp),srt,k,l)
      | Fun(Choose _, srt, _) ->
	let rexp = mkFldAcc(mkVarJavaExpr("arg1"),"choose") in
	standAloneFromTypeM(mkReturnStmt(rexp),srt,k,l)
      | Fun(Quotient qid, srt, _) ->
	% let rng = srtRange(srt) in % TODO: verify this isn't needed
	{
	 % rngid <- tt_idM rng; % TODO: verify this isn't needed
         rngid <- tt_idM (Base (qid, [], noPos)); % TODO: verify this is correct 
	 rexp <- return(mkNewClasInst(rngid,mkNArgsExpr([0],None)));
	 res <- standAloneFromTypeM(mkReturnStmt(rexp),srt,k,l);
	 return res
	}
      | Lambda((pat,cond,body)::_,_) -> translateLambdaTermM(tcx,term,k,l)
      | _ -> raise(UnsupportedLambdaTerm(printTerm term),termAnn term)



   (**
    * this is called, when a lambda term is found in the input; it implements v3:p48:r4
    *)
   op translateLambdaTermM: TCx * MSTerm * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
   def translateLambdaTermM(tcx,term as Lambda((pat,cond,body)::_,_),k,l) =
     {
      spc <- getEnvSpec;
      termSrt <- return(inferTypeFoldRecords(spc,term));
      freeVars <- return(freeVars term);
      (block,tcx0) <- 
        foldM (fn (block0,tcx0) -> fn(wi,wisrt) ->
	     let initExpr = case StringMap.find(tcx,wi) of
			      | Some exp -> exp
			      | None -> mkVarJavaExpr(wi)
	     in
	     {
	      (tcx2,locvdecl) <-
	           let finwi = mkFinalVar(wi) in
		   %let _ = writeLine("final var: " ^ finwi) in
		   let finwi_exp = mkVarJavaExpr(finwi) in
		   let tcx1 = StringMap.insert(tcx0,wi,finwi_exp) in
		   {
		    locvdecl <- mkFinalVarDeclM(finwi,wisrt,initExpr);
		    if isIdentityAssignment?(locvdecl) then
		      return (tcx0,[])
		    else
		      return (tcx1,[locvdecl])
		   };
	      return (block0 ++ locvdecl,tcx2)
	     }) ([],tcx) freeVars;
      (s,_,_) <- termToExpressionRetM(tcx0,body,1,1,false);
      parNames <- return(mkParamsFromPattern pat);
      (_,e,_,_) <- standAloneFromTypeWithParNamesM(Block s,termSrt,parNames,k,l);
      return(block,e,k,l)
     }
  
    

   (**
    * this is active when a "stand-alone" operator appears as term, i.e. an operator symbol without any arguments
    *)
   op translateStandAloneOpToExprM: TCx * (QualifiedId * MSType) * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat *Nat)
   def translateStandAloneOpToExprM(tcx,(qid,srt),k,l) =
%     let _ = case srt of
%	       | Arrow(_,_,_) -> true
%               | _ -> fail("can't happen: srt in translateStandAloneOpToExpr is not an arrow type: "^printType(srt))
%     in
     let Qualified(spcname,id) = qid in
     if (id = "+" || id = "-" || id = "*" || id = "div" || id = "mod") &&
       (spcname = "Integer" || spcname = "Nat" || spcname = "PosNat")
       then
	 %v3:p44:r11
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standaloneM(mkReturnStmt(rexp),(["int","int"],"int"),(["Integer","Integer"],"Integer"),k,l)
     else
     if (id = "&&" || id = "||") &&
        (spcname = "Bool")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standaloneM(mkReturnStmt(rexp),(["boolean","boolean"],"boolean"),(["Boolean","Boolean"],"Boolean"),k,l)
     else
     if (id = "<" || id = "<=" || id = ">" || id = ">=") &&
       (spcname = "Integer" || spcname = "Nat" || spcname = "PosNat")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standaloneM(mkReturnStmt(rexp),(["int","int"],"boolean"),(["Integer","Integer"],"Boolean"),k,l)
     else
     if (id = "-") && (spcname = "IntegerAux")
       then
	 let rexp = mkUnExp("-",[mkVarJavaExpr("arg1")]) in
	 standaloneM(mkReturnStmt(rexp),(["int"],"int"),(["Integer"],"Integer"),k,l)
     else	 
     if (id = "~") && (spcname = "Integer") % deprecated
       then
	 let rexp = mkUnExp("-",[mkVarJavaExpr("arg1")]) in
	 standaloneM(mkReturnStmt(rexp),(["int"],"int"),(["Integer"],"Integer"),k,l)
     else	 
     if (id = "~") && (spcname = "Bool")
       then
	 let rexp = mkUnExp("~",[mkVarJavaExpr("arg1")]) in
	 standaloneM(mkReturnStmt(rexp),(["boolean"],"boolean"),(["Boolean"],"Boolean"),k,l)
     else
       let dom = typeDom srt in
       let rng = typeRng srt in
       {
	spc <- getEnvSpec;
	apdom <- mapTypeColM(tt_idM,dom);
	apran <- tt_idM rng;
	atdom <- mapTypeColM(srtIdM,dom);
	atran <- srtIdM rng;
	if forall? (fn(srt) -> notAUserType?(spc,srt)) dom then
	  if notAUserType?(spc,rng) then
	     case ut(spc,srt) of
	       | Some s -> % v3:p46:r4: no user toplevel user type found, but user type nested in some of the args
	         {
		  sid <- srtIdM s;
		  rexp <- return(mkMethInv(sid,id,mkNArgsExpr(dom,None)));
		  standaloneM(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
		 }
	       | None -> % v3:p46:r5
		 {
		  primitiveClassName <- getPrimitiveClassName;
		  rexp <- return(mkMethInv(primitiveClassName,id,mkNArgsExpr(dom,None)));
		  standaloneM(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
		 }
	   else
	     % v3:p46:r3: first user type found is the range type
	     let rexp = mkMethInv(apran,id,mkNArgsExpr(dom,None)) in
	     standaloneM(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
       else
	 % found a user type in the domain:
	 % v3:p46:r2
	 let split = splitAtLeftmost(fn(srt) -> userType?(spc,srt)) dom in
	 case split of
	   | Some(vars1,varh,vars2) ->
	     let h = length(vars1)+1 in
	     let argh = "arg"^Integer.show(h) in
	     let rexp = mkMethInv(argh,id,mkNArgsExpr(dom,Some h)) in
	     standaloneM(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
	   | None -> 
	     raise(Fail("can't happen in translateStandAloneOpToExpr: cannot find user type in type "^printType(srt)),typeAnn srt)

       }

op standaloneM: JavaStmt * (List String * String) * (List String * String) * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def standaloneM(s,applySig as (apdom,apran),arrowTypeSig as (atdom,atran),k,l) =
  let argNameBase = "arg" in
  let (parNames,_) = foldl (fn((argnames,nmb),argType) -> 
                              let argname = argNameBase^Integer.show(nmb) in
                              (argnames ++ [argname],nmb+1))
                       ([],1) apdom
  in
  standaloneWithParNamesM(s,applySig,arrowTypeSig,parNames,k,l)

op standaloneWithParNamesM: JavaStmt * (List String * String) * (List String * String) * List String * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def standaloneWithParNamesM(s,applySig as (apdom,apran),arrowTypeSig as (atdom,atran),parNames,k,l) =
  let meth = mkMethDeclWithParNames("apply",apdom,apran,parNames,s) in
  {
   clsname <- mkArrowSrtId(atdom,atran);
   (exp,cldecl) <- return(mkNewAnonymousClasInstOneMethod(clsname,[],meth));
   addArrowClass cldecl;
   return (mts,exp,k,l)
  }

op standAloneFromTypeM: JavaStmt * MSType * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def standAloneFromTypeM(s,srt,k,l) =
  let dom = typeDom srt in
  let rng = typeRng srt in
  %let apdom = map tt_id dom in
  {
   apdom <- mapTypeColM(tt_idM,dom);
   apran <- tt_idM rng;
   atdom <- mapTypeColM(srtIdM,dom);
   atran <- srtIdM rng;
   standaloneM(s,(apdom,apran),(atdom,atran),k,l)
  }

op mapTypeColM: (MSType -> JGenEnv Id) * MSTypes -> JGenEnv (List String)
def mapTypeColM(srtf,srtl) =
  mapM (fn(srt) -> srtf srt) srtl
%  foldl (fn((srtl,col),srt) ->
%	 let (sid,col1) = srtf srt in 
%	 (concat(srtl,[sid]),concatCollected(col,col1))) 
%  ([],nothingCollected) srtl

op standAloneFromTypeWithParNamesM: JavaStmt * MSType * List Id * Nat * Nat -> JGenEnv (JavaBlock * JavaExpr * Nat * Nat)
def standAloneFromTypeWithParNamesM(s,srt,parNames,k,l) =
  let dom = typeDom srt in
  let rng = typeRng srt in
  {
   spc <- getEnvSpec;
   apdom <- mapTypeColM(tt_idM,dom);
   apran <- tt_idM rng;
   atdom <- mapTypeColM(srtIdM,dom);
   rng <- return(findMatchingUserType(spc,rng));
   atran <- srtIdM rng;
   standaloneWithParNamesM(s,(apdom,apran),(atdom,atran),parNames,k,l)
  }

op mkNArgs: [T,E] (String -> E) -> List T * Option Nat -> List E
def mkNArgs trans (l,omit) =
  let
    def mkNArgs0(l,n) =
      case l of
	| [] -> []
	| _::l ->
	  let omit? = case omit of Some m -> m = n | _ -> false in 
	  let argid = "arg" ^ Integer.show(n) in
	  let argn = trans(argid) in
	  let rlist = mkNArgs0(l,n+1) in
	  if omit? then rlist else argn::rlist
  in
    mkNArgs0(l,1)

op mkNArgsExpr: [T] List T * Option Nat -> List JavaExpr
def mkNArgsExpr(l,omit) = (mkNArgs mkVarJavaExpr)(l,omit)


op mkNArgsId: [T] List T * Option Nat -> List Id
def mkNArgsId(l,omit) = (mkNArgs (fn(x)->x))(l,omit)

endspec
