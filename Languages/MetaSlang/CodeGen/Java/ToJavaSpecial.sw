(**
 * this spec contains special translation rules for Java, e.g., translation from predefined MetaSlang ops
 * to java.lang method (String utilities)
 *)

spec

  import ToJavaBase
  import ToJavaStatements

  %op specialTermToExpression: TCx * JGen.Term * Nat * Nat * Spec -> Option ((Block * Java.Expr * Nat * Nat) * Collected)
  def specialTermToExpression(tcx,term,k,l,spc) =
    case term of
      | Apply(Fun(Op(Qualified("String","writeLine"),_),_,_),t,_) -> None
      | _ -> None

endspec
