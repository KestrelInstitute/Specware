(**
 * translation of higher order features to Java
 *
 * @author MA
 * @created Sun Jul 13 15:34:43 PDT 2003
 *)

spec
  import ToJavaBase

  (**
   * translates a lambda term into a java expression, called from translateToExpression in ToJavaStatements
   *)
  op translateLambdaToExpr: TCx * JGen.Term * Nat * Nat * Spec -> Block * Java.Expr * Nat * Nat
  def translateLambdaToExpr(tcx,term (*as Lambda((pat,cond,body)::_,_)*),k,l,spc) =
    let termSrt = termSort(term) in
    case term of
      | Fun(Op(qid as Qualified(_,id),_),srt,_) -> translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc)
      | _ -> fail("not yet supported: stand-alone lambda terms: \""^printTerm(term)^"\"")


   (**
    * this is active when a "stand-alone" operator appears as term, i.e. an operator symbol without any arguments
    *)
   op translateStandAloneOpToExpr: TCx * (QualifiedId * Sort) * Nat * Nat * Spec -> Block * Java.Expr * Nat *Nat
   def translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc) =
     let
       def standalone(rexp,applySig as (apdom,apran),arrowTypeSig as (atdom,atran)) =
	 let s = mkReturnStmt(rexp) in
	 let meth = mkMethDecl("apply",apdom,apran,"arg",s) in
	 let clsname = mkArrowSrtId(atdom,atran) in
	 let exp = mkNewAnonymousClasInstOneMethod(clsname,[],meth) in
	 (mts,exp,k,l)
     in
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
	 standalone(rexp,(["int","int"],"int"),(["Integer","Integer"],"Integer"))
     else
     if (id = "and" or id = "or") &
        (spcname = "Boolean")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standalone(rexp,(["boolean","boolean"],"boolean"),(["Boolean","Boolean"],"Boolean"))
     else
     if (id = "<" or id = "<=" or id = ">" or id = ">=") &
       (spcname = "Integer" or spcname = "Nat" or spcname = "PosNat")
       then
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 standalone(rexp,(["int","int"],"boolean"),(["Integer","Integer"],"Boolean"))
     else
     if (id = "~") & (spcname = "Integer")
       then
	 let rexp = mkUnExp("-",[mkVarJavaExpr("arg1")]) in
	 standalone(rexp,(["int"],"int"),(["Integer"],"Integer"))
     else	 
     if (id = "~") & (spcname = "Boolean")
       then
	 let rexp = mkUnExp("~",[mkVarJavaExpr("arg1")]) in
	 standalone(rexp,(["boolean"],"boolean"),(["Boolean"],"Boolean"))
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
		 let rexp = mkMethInv(srtId s,id,mkNArgs(dom,None)) in
		 standalone(rexp,(apdom,apran),(atdom,atran))
	       | None -> % v3:p46:r5
		 let rexp = mkMethInv("Primitive",id,mkNArgs(dom,None)) in
		 standalone(rexp,(apdom,apran),(atdom,atran))
	   else
	     % v3:p46:r3: first user type found is the range type
	     let rexp = mkMethInv(apran,id,mkNArgs(dom,None)) in
	     standalone(rexp,(apdom,apran),(atdom,atran))
       else
	 % found a user type in the domain:
	 % v3:p46:r2
	 let split = splitList(fn(srt) -> userType?(srt)) dom in
	 case split of
	   | Some(vars1,varh,vars2) ->
	     let h = length(vars1)+1 in
	     let argh = "arg"^Integer.toString(h) in
	     let rexp = mkMethInv(argh,id,mkNArgs(dom,Some h)) in
	     standalone(rexp,(apdom,apran),(atdom,atran))
	   | None -> 
	     fail("can't happen in translateStandAloneOpToExpr: cannot find user type in sort "^printSort(srt))


       %fail("not yet implemented: stand-alone op "^id)


op mkNArgs: fa(T) List T * Option Nat -> List Java.Expr
def mkNArgs(l,omit) =
  let
    def mkNArgs0(l,n) =
      case l of
	| [] -> []
	| _::l ->
	  let omit? = case omit of Some m -> m = n | _ -> false in 
	  let argid = "arg" ^ Integer.toString(n) in
	  let argn = mkVarJavaExpr(argid) in
	  let rlist = mkNArgs0(l,n+1) in
	  if omit? then rlist else  cons(argn,rlist)
  in
    mkNArgs0(l,1)

endspec
