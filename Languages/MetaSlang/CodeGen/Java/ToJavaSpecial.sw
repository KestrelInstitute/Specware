(**
 * this spec contains special translation rules for Java, e.g., translation from predefined MetaSlang ops
 * to java.lang method (String utilities)
 *)

spec

  import ToJavaBase
  import ToJavaStatements

  %op specialTermToExpression: TCx * JGen.Term * Nat * Nat * Spec -> Option ((Block * Java.Expr * Nat * Nat) * Collected)
  def specialTermToExpression(tcx,term,k,l,spc) =
    let
      def stringConcat(t1,t2) =
        let ((s1,argexpr1,k,l),col1) = termToExpression(tcx,t1,k,l,spc) in
        let ((s2,argexpr2,k,l),col2) = termToExpression(tcx,t2,k,l,spc) in
	let expr = CondExp(Bin(Plus,Un(Prim(Paren(argexpr1))),Un(Prim(Paren(argexpr2)))),None) in
	Some ((s1++s2,expr,k,l),concatCollected(col1,col2))
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
    case term of
      | Apply(Fun(Op(Qualified("String","writeLine"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	Some ((s,expr,k,l),col)
      | Apply(Fun(Op(Qualified("String","toScreen"),_),_,_),t,_) -> 
        let ((s,argexpr,k,l),col) = termToExpression(tcx,t,k,l,spc) in
	let expr = mkMethInvName((["System","out"],"println"),[argexpr]) in
	Some ((s,expr,k,l),col)
      | Apply(Fun(Op(Qualified("String","concat"),_),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","++"),_),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
      | Apply(Fun(Op(Qualified("String","^"),_),_,_),Record([(_,t1),(_,t2)],_),_) -> stringConcat(t1,t2)
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
      | Apply(Fun(Op(Qualified("Nat","toString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Nat","natToString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Nat","show"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","toString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","intToString"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","show"),_),_,_),t,_) -> intToString(t)
      | Apply(Fun(Op(Qualified("Integer","stringToInt"),_),_,_),t,_) -> stringToInt(t)
      | Apply(Fun(Op(Qualified("Nat","stringToNat"),_),_,_),t,_) -> stringToInt(t)
      | _ -> None

endspec
