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
  def translateLambdaToExpr(tcx,term as Lambda((pat,cond,body)::_,_),k,l,spc) =
    let termSrt = termSort(term) in
    case body of
      | Fun(Op(qid as Qualified(_,id),_),srt,_) -> translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc)
      | _ -> fail("not yet supported: stand-alone lambda terms: \""^printTerm(term)^"\"")


   (**
    * this is active when a "stand-alone" operator appears as term, i.e. an operator symbol without any arguments
    *)
   op translateStandAloneOpToExpr: TCx * (QualifiedId * Sort) * Nat * Nat * Spec -> Block * Java.Expr * Nat *Nat
   def translateStandAloneOpToExpr(tcx,(qid,srt),k,l,spc) =
     let Qualified(spcname,id) = qid in
     if (id = "+" or id = "-" or id = "*" or id = "div" or id = "mod") &
       (spcname = "Integer" or spcname = "Nat" or spcname = "PosNat")
       then
	 %v3:p44:r11
	 let rexp = mkBinExp(id,[mkVarJavaExpr("arg1"),mkVarJavaExpr("arg2")]) in
	 let s = mkReturnStmt(rexp) in
	 let meth = mkMethDecl("apply",["int","int"],"int","arg",s) in
	 let clsname = mkArrowSrtId(["Integer","Integer"],"Integer") in
	 let exp = mkNewAnonymousClasInstOneMethod(clsname,[],meth) in
	 (mts,exp,k,l)
     else fail("not yet implemented: stand-alone op "^id)


endspec
