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
     let Qualified(q,id) = qid in
     fail("stand alone op: "^q^"."^id)


endspec
