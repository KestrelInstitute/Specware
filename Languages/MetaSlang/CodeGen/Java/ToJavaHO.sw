(**
 * translation of higher order features to Java
 *
 * @author MA
 * @created Sun Jul 13 15:34:43 PDT 2003
 *)

spec
  import ToJavaBase
  import ToJavaStatements

  (**
   * translates a lambda term into a java expression, called from translateToExpression in ToJavaStatements
   *)
%  op translateLambdaToExpr: TCx * JGen.Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
  def translateLambdaToExpr(tcx,term (*as Lambda((pat,cond,body)::_,_)*),k,l,spc) =
    case term of
      | Fun(Op(qid as Qualified(_,id),_),srt,_) -> translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc)
      | Fun(Embed(c,_),srt,_) -> 
	let dom = srtDom(srt) in
	let rng = srtRange(srt) in
	let apran = tt_id rng in
        let rexp = mkMethInv(apran,c,mkNArgsExpr(dom,None)) in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Fun(Project(id),srt,_) -> 
	let rexp = mkMethInv("arg1",getFieldName(id),[]) in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Fun(Restrict,srt,_) -> 
	let rng = srtRange(srt) in
	let rexp = mkNewClasInst(tt_id rng,mkNArgsExpr([0],None)) in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Fun(Relax,srt,_) ->
	let rexp = mkFldAcc(mkVarJavaExpr("arg1"),"relax") in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Fun(Choose,srt,_) ->
	let rexp = mkFldAcc(mkVarJavaExpr("arg1"),"choose") in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Fun(Quotient,srt,_) ->
	let rng = srtRange(srt) in
	let rexp = mkNewClasInst(tt_id rng,mkNArgsExpr([0],None)) in
	standAloneFromSort(mkReturnStmt(rexp),srt,k,l)
      | Lambda((pat,cond,body)::_,_) -> translateLambdaTerm(tcx,term,k,l,spc)
      | _ -> fail("not yet supported: stand-alone lambda terms: \""^printTerm(term)^"\"")



   (**
    * this is called, when a lambda term is found in the input; it implements v3:p48:r4
    *)
   op translateLambdaTerm: TCx * JGen.Term * Nat * Nat * Spec -> (Block * Java.Expr * Nat * Nat) * Collected
   def translateLambdaTerm(tcx,term as Lambda((pat,cond,body)::_,_),k,l,spc) =
     let termSrt = termSort(term) in
     let freeVars = freeVars(term) in
     let (block,tcx0) = foldl (fn((wi,wisrt),(block0,tcx0)) -> 
			       let initExpr = case StringMap.find(tcx,wi) of
						| Some exp -> exp
						| None -> mkVarJavaExpr(wi)
			       in
			       let finwi = mkFinalVar(wi) in
			       let finwi_exp = mkVarJavaExpr(finwi) in
			       let tcx0 = StringMap.insert(tcx0,wi,finwi_exp) in
			       let locvdecl = mkFinalVarDecl(finwi,wisrt,initExpr) in
			       (concat(block0,[locvdecl]),tcx0)
			       ) ([],tcx) freeVars
     in
     let ((s,_,_),col1) = termToExpressionRet(tcx0,body,1,1,spc) in
     let parNames = mkParamsFromPattern(pat) in
     let ((_,e,_,_),col2) = standAloneFromSortWithParNames(Block s,termSrt,parNames,k,l) in
     let col = concatCollected(col1,col2) in
     ((block,e,k,l),col)
  
    

   (**
    * this is active when a "stand-alone" operator appears as term, i.e. an operator symbol without any arguments
    *)
   op translateStandAloneOpToExpr: TCx * (QualifiedId * Sort) * Nat * Nat * Spec -> (Block * Java.Expr * Nat *Nat) * Collected
   def translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc) =
     let _ = case srt of
	       | Arrow(_,_,_) -> true
               | _ -> fail("can't happen: srt in translateStandAloneOpToExpr is not an arrow sort: "^printSort(srt))
     in
     let Qualified(spcname,id) = qid in
     if (id = "+" or id = "-" or id = "*" or id = "div" or id = "mod") &
       (spcname = "Integer" or spcname = "Nat" or spcname = "PosNat")
       then
	 %v3:p44:r11
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standalone(mkReturnStmt(rexp),(["int","int"],"int"),(["Integer","Integer"],"Integer"),k,l)
     else
     if (id = "and" or id = "or") &
        (spcname = "Boolean")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standalone(mkReturnStmt(rexp),(["boolean","boolean"],"boolean"),(["Boolean","Boolean"],"Boolean"),k,l)
     else
     if (id = "<" or id = "<=" or id = ">" or id = ">=") &
       (spcname = "Integer" or spcname = "Nat" or spcname = "PosNat")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standalone(mkReturnStmt(rexp),(["int","int"],"boolean"),(["Integer","Integer"],"Boolean"),k,l)
     else
     if (id = "~") & (spcname = "Integer")
       then
	 let rexp = mkUnExp("-",[mkVarJavaExpr("arg1")]) in
	 standalone(mkReturnStmt(rexp),(["int"],"int"),(["Integer"],"Integer"),k,l)
     else	 
     if (id = "~") & (spcname = "Boolean")
       then
	 let rexp = mkUnExp("~",[mkVarJavaExpr("arg1")]) in
	 standalone(mkReturnStmt(rexp),(["boolean"],"boolean"),(["Boolean"],"Boolean"),k,l)
     else
       let dom = srtDom(srt) in
       let rng = srtRange(srt) in
       let apdom = map tt_id dom in
       let apran = tt_id rng in
       let atdom = map srtId dom in
       let atran = srtId rng in
       if all (fn(srt) -> notAUserType?(srt)) dom 
	 then
	   if notAUserType?(rng) then
	     case ut(srt) of
	       | Some s -> % v3:p46:r4: no user toplevel user type found, but user type nested in some of the args
		 let rexp = mkMethInv(srtId s,id,mkNArgsExpr(dom,None)) in
		 standalone(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
	       | None -> % v3:p46:r5
		 let rexp = mkMethInv("Primitive",id,mkNArgsExpr(dom,None)) in
		 standalone(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
	   else
	     % v3:p46:r3: first user type found is the range type
	     let rexp = mkMethInv(apran,id,mkNArgsExpr(dom,None)) in
	     standalone(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
       else
	 % found a user type in the domain:
	 % v3:p46:r2
	 let split = splitList(fn(srt) -> userType?(srt)) dom in
	 case split of
	   | Some(vars1,varh,vars2) ->
	     let h = length(vars1)+1 in
	     let argh = "arg"^Integer.toString(h) in
	     let rexp = mkMethInv(argh,id,mkNArgsExpr(dom,Some h)) in
	     standalone(mkReturnStmt(rexp),(apdom,apran),(atdom,atran),k,l)
	   | None -> 
	     fail("can't happen in translateStandAloneOpToExpr: cannot find user type in sort "^printSort(srt))


       %fail("not yet implemented: stand-alone op "^id)

op standalone: Java.Stmt * (List String * String) * (List String * String) * Nat * Nat -> (Block * Java.Expr * Nat * Nat) * Collected
def standalone(s,applySig as (apdom,apran),arrowTypeSig as (atdom,atran),k,l) =
  let argNameBase = "arg" in
  let (parNames,_) = foldl (fn(argType,(argnames,nmb)) -> 
		    let argname = argNameBase^Integer.toString(nmb) in
		    (concat(argnames,[argname]),nmb+1))
                   ([],1) apdom
  in
  standaloneWithParNames(s,applySig,arrowTypeSig,parNames,k,l)

op standaloneWithParNames: Java.Stmt * (List String * String) * (List String * String) * List String * Nat * Nat -> (Block * Java.Expr * Nat * Nat) * Collected
def standaloneWithParNames(s,applySig as (apdom,apran),arrowTypeSig as (atdom,atran),parNames,k,l) =
  let meth = mkMethDeclWithParNames("apply",apdom,apran,parNames,s) in
  let clsname = mkArrowSrtId(atdom,atran) in
  let (exp,ifdecl) = mkNewAnonymousClasInstOneMethod(clsname,[],meth) in
  let col = {arrowifs=[ifdecl]} in
  ((mts,exp,k,l),col)

op standAloneFromSort: Java.Stmt * Sort * Nat * Nat -> (Block * Java.Expr * Nat * Nat) * Collected
def standAloneFromSort(s,srt,k,l) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  let apdom = map tt_id dom in
  let apran = tt_id rng in
  let atdom = map srtId dom in
  let atran = srtId rng in
  standalone(s,(apdom,apran),(atdom,atran),k,l)

op standAloneFromSortWithParNames: Java.Stmt * Sort * List Id * Nat * Nat -> (Block * Java.Expr * Nat * Nat) * Collected
def standAloneFromSortWithParNames(s,srt,parNames,k,l) =
  let dom = srtDom(srt) in
  let rng = srtRange(srt) in
  let apdom = map tt_id dom in
  let apran = tt_id rng in
  let atdom = map srtId dom in
  let atran = srtId rng in
  standaloneWithParNames(s,(apdom,apran),(atdom,atran),parNames,k,l)

op mkNArgs: fa(T,E) (String -> E) -> List T * Option Nat -> List E
def mkNArgs trans (l,omit) =
  let
    def mkNArgs0(l,n) =
      case l of
	| [] -> []
	| _::l ->
	  let omit? = case omit of Some m -> m = n | _ -> false in 
	  let argid = "arg" ^ Integer.toString(n) in
	  let argn = trans(argid) in
	  let rlist = mkNArgs0(l,n+1) in
	  if omit? then rlist else  cons(argn,rlist)
  in
    mkNArgs0(l,1)

op mkNArgsExpr: fa(T) List T * Option Nat -> List Java.Expr
def mkNArgsExpr(l,omit) = (mkNArgs mkVarJavaExpr)(l,omit)


op mkNArgsId: fa(T) List T * Option Nat -> List Id
def mkNArgsId(l,omit) = (mkNArgs (fn(x)->x))(l,omit)

endspec
