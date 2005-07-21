spec

  import TypesAndExpressions

  (* This spec provides an abstract datatype API for Types and
  Expressions. *)

  op VAR?: Expression -> Boolean
  def VAR?(e) =
    case e of
      | VAR _ -> true
      | _ -> false

  type VARExpr = (Expression | OPI?)

  op mkVAR: Variable -> VARExpr

  op var: VARExpr -> Variable

  axiom VARa1 is fa (var_v: Variable) var(mkVAR(var_v)) = var_v
  axiom VARc is fa (var_e: VARExpr) mkVAR(var(var_e)) = var_e

  op OPI?: Expression -> Boolean
  def OPI?(e) =
    case e of
      | OPI _ -> true
      | _ -> false

  type OPIExpr = (Expression | OPI?)

  op mkOPI: Operation * Types -> OPIExpr
  
  op oper: OPIExpr -> Operation

  op types: OPIExpr -> Types

  axiom OPIa1 is fa (oper_v: Operation, types_v: Types) oper(mkOPI(oper_v, types_v)) = oper_v
  axiom OPIa2 is fa (oper_v: Operation, types_v: Types) types(mkOPI(oper_v, types_v)) = types_v
  axiom OPIc is fa (opi_e: OPIExpr) mkOPI(oper(opi_e), types(opi_e)) = opi_e

  op APPLY?: Expression -> Boolean
  def APPLY?(e) =
    case e of
      | APPLY _ -> true
      | _ -> false

  type APPLYExpr = (Expression | APPLY?)

  op  exp1: APPLYExpr -> Expression
  op  exp2: APPLYExpr -> Expression

  op mkAPPLY: Expression * Expression -> APPLYExpr


  op FN?: Expression -> Boolean
  def FN?(e) =
    case e of
      | FN _ -> true
      | _ -> false

  type FNExpr = (Expression | FN?)

  op mkFN: Operation * Types -> FNExpr
  
  op typE: FNExpr -> Type

  op expr: FNExpr -> Expression

%  axiom FNa1 is fa (var_v: Variable, type_v: Type, expr_v: Expression) var(mkFN(var_v, type_v, expr_v)) = var_v
%  axiom FNa2 is fa (oper_v: Operation, types_v: Types) types(mkFN(oper_v, types_v)) = types_v
%  axiom FNc is fa (fn_e: FNExpr) mkFN(oper(fn_e), types(fn_e)) = fn_e

  op EQ?: Expression -> Boolean
  def EQ?(e) =
    case e of
      | EQ _ -> true
      | _ -> false

  type EQExpr = (Expression | EQ?)

  op IF?: Expression -> Boolean
  def IF?(e) =
    case e of
      | IF _ -> true
      | _ -> false

  type IFExpr = (Expression | IF?)

  op IOTA?: Expression -> Boolean
  def IOTA?(e) =
    case e of
      | IOTA _ -> true
      | _ -> false

  type IOTAExpr = (Expression | IOTA?)

  op PROJECT?: Expression -> Boolean
  def PROJECT?(e) =
    case e of
      | PROJECT _ -> true
      | _ -> false

  type PROJECTExpr = (Expression | PROJECT?)

  op EMBED?: Expression -> Boolean
  def EMBED?(e) =
    case e of
      | EMBED _ -> true
      | _ -> false

  type EMBEDExpr = (Expression | EMBED?)

  op QUOT?: Expression -> Boolean
  def QUOT?(e) =
    case e of
      | QUOT _ -> true
      | _ -> false

  type QUOTExpr = (Expression | QUOT?)

endspec
