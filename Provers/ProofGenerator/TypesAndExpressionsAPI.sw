spec

  import ../ProofChecker/Spec

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

  op mkFN: Variable * Type * Expression -> FNExpr
  def mkFN(v, t, e) = FN(v, t, e)
  
  op fnVar: FNExpr -> Variable
  def fnVar(FN(v,_,_)) = v

  op fnVarType: FNExpr -> Type
  def fnVarType(FN(_,t,_)) = t

  op fnBody: FNExpr -> Expression
  def fnBody(FN(_,_,b)) = b

%  axiom FNa1 is fa (var_v: Variable, type_v: Type, expr_v: Expression) var(mkFN(var_v, type_v, expr_v)) = var_v
%  axiom FNa2 is fa (oper_v: Operation, types_v: Types) types(mkFN(oper_v, types_v)) = types_v
%  axiom FNc is fa (fn_e: FNExpr) mkFN(oper(fn_e), types(fn_e)) = fn_e

  op EQ?: Expression -> Boolean
  def EQ?(e) =
    case e of
      | EQ _ -> true
      | _ -> false

  type EQExpr = (Expression | EQ?)

  op eqLhs: EQExpr -> Expression
  def eqLhs(EQ(l, r)) = l

  op eqRhs: EQExpr -> Expression
  def eqRhs(EQ(l, r)) = r

  op IF?: Expression -> Boolean
  def IF?(e) =
    case e of
      | IF _ -> true
      | _ -> false

  type IFExpr = (Expression | IF?)

  op ifCond: IFExpr -> Expression
  def ifCond(IF(c,_,_)) = c

  op ifThen: IFExpr -> Expression
  def ifThen(IF(_,t,_)) = t

  op ifElse: IFExpr -> Expression
  def ifElse(IF(_,_,e)) = e

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

  op TYPE?: Type -> Boolean
  def TYPE?(t) =
    case t of
      | TYPE _ -> true
      | _ -> false

  type TYPEType = (Type | TYPE?)

  op TYPESName: TYPEType -> TypeName
  def TYPEName(TYPE(tn, _)) = tn

  op TYPEtypes: TYPEType -> Types
  def TYPEtypes(TYPE(_, ts)) = ts

  op ARROW?: Type -> Boolean
  def ARROW?(t) =
    case t of
      | ARROW _ -> true
      | _ -> false

  type ARROWType = (Type | ARROW?)

  op domain: ARROWType -> Type
  def domain(ARROW(t1, _)) = t1

  op range: ARROWType -> Type
  def range(ARROW(_, t2)) = t2

  op RECORD?: Type -> Boolean
  def RECORD?(t) =
    case t of
      | RECORD _ -> true
      | _ -> false

  type RECORDType = (Type | RECORD?)

  op RECfields: RECORDType -> Fields
  def RECfields(RECORD(flds, _)) = flds

  op RECtypes: RECORDType -> Types
  def RECtypes(RECORD(_, types)) = types

  op SUM?: Type -> Boolean
  def SUM?(t) =
    case t of
      | SUM _ -> true
      | _ -> false

  type SUMType = (Type | SUM?)

  op SUMcnstrs: SUMType -> Constructors
  def SUMcnstrs(SUM(cs, _)) = cs

  op SUMtypes: SUMType -> Types
  def SUMtypes(SUM(_, types)) = types

  op RESTR?: Type -> Boolean
  def RESTR?(t) =
    case t of
      | RESTR (t, r) -> true
      | _ -> false

  type RESTRType = (Type | RESTR?)

  op superType: RESTRType -> Type
  def superType(t) =
    let RESTR (st, _) = t in st

  op restrictPred: RESTRType -> Expression
  def restrictPred(t) =
    let RESTR (_, r) = t in r

  op QUOTT?: Type -> Boolean
  def QUOTT?(t) =
    case t of
      | QUOT (t, r) -> true
      | _ -> false

  type QUOTType = (Type | QUOTT?)

  op quotType: QUOTType -> Type
  def quotType(t) =
    let QUOT (st, _) = t in st

  op quotPred: QUOTType -> Expression
  def quotPred(t) =
    let QUOT (_, r) = t in r

endspec
