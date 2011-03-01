(*
 * Intermediate Representation for Code Generation
 *
 * This file contains the definition of the intermediate imperative
 * language (i2l) that is used for generating code in imperative
 * languages.
 *)

I2L qualifying spec
{
  % import /Library/Legacy/DataStructures/MergeSort

  import CUtils % for qsort

  type IImpUnit = {
                   name     : String,
                   includes : IImpUnits,
                   decls    : IImpUnitDecls
                  }
  type IImpUnits = List IImpUnit

  type IImpUnitDecls = { 
                        typedefs : ITypeDefinitions,
                        opdecls  : IDeclarations,
                        funDecls : IFunDeclarations,
                        funDefns : IFunDefinitions,
                        varDecls : IDeclarations,
                        mapDecls : IFunDeclarations
                       }

  type ITypeName = String * String

  type ITypeDefinition = ITypeName * IType
  type ITypeDefinitions = List ITypeDefinition

  type IPrimitive = | IBool | IChar | IString | INat | IInt | IFloat

  type IType = | IPrimitive     IPrimitive
               | IRestrictedNat Nat
               | IStruct        IStructFields
               | IUnion         IUnionFields
               | ITuple         ITypes
               | IBoundList     IType * Nat      % list with maximum length
               | IList          IType
               | IBase          ITypeName        % reference to an itype definition
               | IFunOrMap      ITypes * IType
               | IRef           IType
               | IVoid
               | IAny
  type ITypes = List IType

  type IStructField = String * IType
  type IStructFields = List IStructField

  type IUnionField = String * IType  % constructor * typ
  type IUnionFields = List IUnionField

  type IOpName = String * String

  type IDeclaration = IOpName * IType * Option ITypedExpr
  type IDeclarations = List IDeclaration

  type IParameterDeclaration = String * IType
  type IParameterDeclarations = List IParameterDeclaration

  type IFunDefinition = {
                         decl : IFunDeclaration,
                         body : IFunBody
                        }
  type IFunDefinitions = List IFunDefinition

  type IFunDeclaration = {
                          name       : IOpName,
                          params     : IParameterDeclarations,
                          returntype : IType
                         }
  type IFunDeclarations = List IFunDeclaration

  type IFunBody = | IStads IStadsFunBody  % state-based
                  | IExp   ITypedExpr    % functional

  type IStadCode = {
                    initial?   : Bool,
                    showLabel? : Bool,
                    decls      : IImpUnit,
                    label      : String,
                    steps      : IStepsCode
                   }
  type IStadsFunBody = List IStadCode

  type ITypedExpr = IExpr * IType
  type ITypedExprs = List ITypedExpr

  type IExpr = | IStr            String
               | IInt            Int
               | IFloat          String
               | IChar           Char
               | IBool           Bool
               | IVar            IVarName
               | IVarDeref       IVarName         
               | IFunCall        IVarName * (*projections*) List String * ITypedExprs
               | IFunCallDeref   IVarName * (*projections*) List String * ITypedExprs
               | IMapAccess      IVarName * IType * (*projections:*) List String * ITypedExprs
               | IMapAccessDeref IVarName * IType * (*projections:*) List String * ITypedExprs
               | IVarRef         IVarName
               | IIfExpr         ITypedExpr * ITypedExpr * ITypedExpr
               | IComma          ITypedExprs
               | ILet            String * IType * ITypedExpr * ITypedExpr
               | IUnionCaseExpr  ITypedExpr * List IUnionCase
               | IAssignUnion    String * Option ITypedExpr
               | IConstrCall     IVarName * String * List ITypedExpr
               | IBuiltin        IBuiltinExpression
               | ITupleExpr      ITypedExprs
               | IStructExpr     IStructExprFields
               | IProject        ITypedExpr * String

  % a variable reference consists of a unit name and an identifier name
  type IVarName = String * String

  % a UnionCase is used to test a given expression, which must have a
  % union type, which alternative of the union it represents.

  type IUnionCase = | IConstrCase  Option String * Option IType * List (Option String) * ITypedExpr
                    | INatCase     Nat  * ITypedExpr
                    | ICharCase    Char * ITypedExpr

  type IStructExprField = String * ITypedExpr
  type IStructExprFields = List IStructExprField

  % a case is given by the constructor string, e.g. "Cons" or "Nil", the list of variable names
  % representing the arguments to the constructor (which can be omitted, in case they 
  % are not used in the expression), and the expression
  % that should be evaluated in case the corresping branch is
  % true. "None" as first part of the UnionCase means, that this case
  % matches everything; as a consequence, all cases following the one
  % with the wildcard constructor are not reachable.

  type IBuiltinExpression = | IEquals              ITypedExpr * ITypedExpr
                            | IStrEquals           ITypedExpr * ITypedExpr
                            | IIntPlus             ITypedExpr * ITypedExpr
                            | IIntMinus            ITypedExpr * ITypedExpr
                            | IIntUnaryMinus       ITypedExpr
                            | IIntMult             ITypedExpr * ITypedExpr
                            | IIntDiv              ITypedExpr * ITypedExpr
                            | IIntRem              ITypedExpr * ITypedExpr
                            | IIntLess             ITypedExpr * ITypedExpr
                            | IIntGreater          ITypedExpr * ITypedExpr
                            | IIntLessOrEqual      ITypedExpr * ITypedExpr
                            | IIntGreaterOrEqual   ITypedExpr * ITypedExpr
                            | IIntToFloat          ITypedExpr
                            | IStringToFloat       ITypedExpr
                            | IFloatPlus           ITypedExpr * ITypedExpr
                            | IFloatMinus          ITypedExpr * ITypedExpr
                            | IFloatUnaryMinus     ITypedExpr
                            | IFloatMult           ITypedExpr * ITypedExpr
                            | IFloatDiv            ITypedExpr * ITypedExpr
                            | IFloatLess           ITypedExpr * ITypedExpr
                            | IFloatGreater        ITypedExpr * ITypedExpr
                            | IFloatLessOrEqual    ITypedExpr * ITypedExpr
                            | IFloatGreaterOrEqual ITypedExpr * ITypedExpr
                            | IFloatToInt          ITypedExpr
                            | IBoolNot             ITypedExpr
                            | IBoolAnd             ITypedExpr * ITypedExpr
                            | IBoolOr              ITypedExpr * ITypedExpr
                            | IBoolImplies         ITypedExpr * ITypedExpr
                            | IBoolEquiv           ITypedExpr * ITypedExpr
 

  %% These are the rules that can occur in the body of a transformation step.
  %% An UpdateBlock contains a list of assignments together with local declaration
  %% that are needed to realize the parallel update semantics
  %% e.g. for updates x:=y,y:=x we have to introduce a auxiliary variable z to store
  %% the value of one of x or y, e.g. int z:=x;x:=y;y:=z (assuming x,y of type Nat)

  type IRule = | ISkip
               | IUpdateBlock IDeclarations * IUpdates
               | ICond        ITypedExpr * IRule
               | IUpdate      IUpdate
               | IProcCall    String * ITypedExprs
  type IRules = List IRule

  type IUpdate = Option ITypedExpr * ITypedExpr
  type IUpdates = List IUpdate

  % a step consists of rules and a next state label.
  % the rules are supposed to be executed in parallel
  type IStepCode = IRule * String
  type IStepsCode = List IStepCode

  % API ------------------------------------------------

  op iproc? (fpdef : IFunDefinition) : Bool = fpdef.decl.returntype = IVoid
  op ifun?  (fpdef : IFunDefinition) : Bool = ~(iproc? fpdef)
                    
  op mergeImpUnit (name : String, impunitlist : IImpUnits) : IImpUnit =
   case impunitlist of
     | [impunit] -> {
                     name     = name,
                     includes = impunit.includes,
                     decls    = impunit.decls
		    }
     | iu1 :: iu2 :: iulst -> 
       let iu = {
                 name     = name,
                 includes = iu1.includes ++ iu2.includes,
                 decls    = {
                             typedefs = iu1.decls.typedefs ++ iu2.decls.typedefs,
                             opdecls  = iu1.decls.opdecls  ++ iu2.decls.opdecls,
                             funDecls = iu1.decls.funDecls ++ iu2.decls.funDecls,
                             funDefns = iu1.decls.funDefns ++ iu2.decls.funDefns,
                             varDecls = iu1.decls.varDecls ++ iu2.decls.varDecls,
                             mapDecls = iu1.decls.mapDecls ++ iu2.decls.mapDecls
                            }
                  }
       in
       mergeImpUnit (name, iu::iulst)

  op addInclude (iu : IImpUnit, includedImpUnit : IImpUnit) : IImpUnit =
   iu << {includes = iu.includes ++ [includedImpUnit]}

  op addFunDefinition (iu : IImpUnit, fdefn : IFunDefinition) : IImpUnit =
   iu << {decls = {
                   typedefs = iu.decls.typedefs,
                   opdecls = iu.decls.opdecls,
                   funDecls = iu.decls.funDecls,
                   funDefns = iu.decls.funDefns ++ [fdefn],
                   varDecls = iu.decls.varDecls,
                   mapDecls = iu.decls.mapDecls
                  }}

  op emptyImpUnit (name : String) : IImpUnit =
   {
    name     = name,
    includes = [],
    decls     = {
                 typedefs = [],
                 opdecls  = [],
                 funDecls = [],
                 funDefns = [],
                 varDecls = [],
                 mapDecls = []
                 }
   }

  % --------------------------------------------------------------------------------

  op substVarName (exp : ITypedExpr, (old1, old2) : IVarName, newvar : IVarName) : ITypedExpr =
    mapExpression (fn e ->
		   case e of
                     | IVar (id1,id2) ->
		       if (id1=old1)&&(id2=old2) then IVar newvar else e

                     | IVarRef (id1,id2) ->
		       if (id1=old1)&&(id2=old2) then IVarRef newvar else e

		     | IVarDeref (id1,id2) ->
		       if (id1=old1)&&(id2=old2) then IVarDeref newvar else e

		     | IFunCall ((id1,id2),p,x) ->
		       if (id1=old1)&&(id2=old2) then IFunCall(newvar,p,x) else e

		     | IFunCallDeref ((id1,id2),p,x) ->
		       if (id1=old1)&&(id2=old2) then IFunCallDeref(newvar,p,x) else e

		     | _ -> e) 
                  exp
		     

  op substVarByExpr (exp : ITypedExpr, (v1,v2) : IVarName, sexp : IExpr) : ITypedExpr =
   mapExpression (fn e ->
                    case e of
                      | IVar (id1,id2) ->
                        if (id1=v1)&&(id2=v2) then sexp else e
                      | _ -> e) 
                 exp

  % --------------------------------------------------------------------------------

  op sortTypeDefinitions (iu : IImpUnit) (typedefns : ITypeDefinitions) : ITypeDefinitions =
   qsort (typeDefnMustFollow iu) typedefns 

  op typeDefnMustFollow (iu : IImpUnit) 
                        (td1 as (tname1 as (_,id1),_) : ITypeDefinition,
                         td2 as (tname2 as (_,id2),_) : ITypeDefinition)
   : Bool =
   let deps1 = typeDefinitionDepends (iu, td1) in
   let deps2 = typeDefinitionDepends (iu, td2) in
   let res = tname2 in? deps1 in
   %let _ = if res then writeLine(id1^" must follow "^id2) else
   %                    writeLine(id1^" does not depend on "^id2)
   %in
   res

  op typeDefinitionDepends (iu : IImpUnit, typedef as (tname,typ) : ITypeDefinition) : List ITypeName =
   typeDepends(iu,tname,typ)

  op typeDepends (iu : IImpUnit, t0name : ITypeName, t0 : IType) : List ITypeName =
   let 
     def typeDepends0 (iu, t, deps) =
       case t of

         | IBase (tname as (_, id1)) -> 
           let _ =
               if t0name = tname then
                 fail ("sorry, this version of the code generator doesn't support recursive types: \"" ^ id1 ^ "\"")
               else ()
           in
           if tname in? deps then 
             deps
           else
             let deps = tname :: deps in
             (case findTypeDefn (iu, tname) of
                | Some t -> typeDepends0 (iu, t, deps)
                | None -> deps)

         | IStruct fields  -> foldl (fn (deps, (_, t)) -> typeDepends0 (iu, t, deps)) deps fields

         | IUnion  fields  -> foldl (fn (deps, (_, t)) -> typeDepends0 (iu, t, deps)) deps fields

         | ITuple  types   -> foldl (fn (deps, t)      -> typeDepends0 (iu, t, deps)) deps types

         | IBoundList (t, _) -> typeDepends0 (iu, t, deps)

         | IFunOrMap (types, t) -> foldl (fn (deps, t) -> typeDepends0 (iu, t, deps))
                                         (typeDepends0 (iu, t, deps))
                                         types
         | IRef t -> typeDepends0 (iu, t, deps)

         | _ -> deps
    in
    typeDepends0 (iu, t0, [])

  op findTypeDefn (iu : IImpUnit, tname : ITypeName) : Option IType =
   case findLeftmost (fn (tname0, _) -> tname0 = tname) iu.decls.typedefs of
     | Some (_,t) -> Some t
     | _ -> None
  

  op impUnitSortTypeDefinitions (iu : IImpUnit) : IImpUnit =
   let decls = iu.decls << {typedefs = sortTypeDefinitions iu iu.decls.typedefs} in
   iu << {decls = decls} 

  % --------------------------------------------------------------------------------

  op mapExpression (f : IExpr -> IExpr) ((e,t) : ITypedExpr) : ITypedExpr =
   (mapExpr f e, t)

  op mapExpr (f : IExpr -> IExpr) (e : IExpr) : IExpr =
   let mp = (fn (e,t) -> (mapExpr f e, t)) in
   let e = f e in
   case e of

      | IFunCall (v, p, exps) -> 
        let exps = map mp exps in
        IFunCall (v, p, exps)

      | IFunCallDeref (v, p, exps) ->
        let exps = map mp exps in
        IFunCallDeref (v, p, exps)

      | IIfExpr (   e1,    e2,    e3) -> 
        IIfExpr (mp e1, mp e2, mp e3)

      | IComma exps -> 
        let exps = map mp exps in
        IComma exps

      | ILet (s, t,    e1,    e2) -> 
        ILet (s, t, mp e1, mp e2)

      | IUnionCaseExpr (   e, ucl) -> 
        let ucl = 
            map (fn ucase ->
                   case ucase of 
                     | IConstrCase (x1, x2, x3,    e) -> 
                       IConstrCase (x1, x2, x3, mp e)

                     | INatCase (n,    e) -> 
                       INatCase (n, mp e)

                     | ICharCase(c,    e) -> 
                       ICharCase(c, mp e))
                ucl
        in
	IUnionCaseExpr (mp e, ucl)

      | IAssignUnion(s, optexp) -> 
        let optexp = case optexp of 
                       | None   -> None 
                       | Some e -> Some (mp e)
        in
        IAssignUnion(s, optexp)

      | IConstrCall (varname, consid, exps) -> 
        let exps = map mp exps in
        IConstrCall (varname, consid, exps)

      | IBuiltin bexp -> 
        let bexp = mapBuiltin f bexp in
        IBuiltin bexp

      | ITupleExpr exps -> 
        let exps = map mp exps in
        ITupleExpr exps

      | IStructExpr fields -> 
        let fields = map (fn(s,e) -> (s,mp e)) fields in
        IStructExpr fields

      | IProject (   exp, s) -> 
        IProject (mp exp, s)

      | _ -> e

  op mapBuiltin (f : IExpr -> IExpr) (exp : IBuiltinExpression) : IBuiltinExpression =
    let mp = fn (exp, typ) -> (mapExpr f exp, typ) in
    case exp of

      | IEquals              (e1,e2) ->
        IEquals              (mp e1, mp e2)

      | IStrEquals           (e1,e2) ->
        IStrEquals           (mp e1, mp e2)

      | IIntPlus             (e1,e2) ->
        IIntPlus             (mp e1, mp e2)

      | IIntMinus            (e1,e2) ->
        IIntMinus            (mp e1, mp e2)

      | IIntUnaryMinus       (e1)    ->
        IIntUnaryMinus       (mp e1)

      | IIntMult             (e1,e2) ->
        IIntMult             (mp e1, mp e2)

      | IIntDiv              (e1,e2) ->
        IIntDiv              (mp e1, mp e2)

      | IIntRem              (e1,e2) ->
        IIntRem              (mp e1, mp e2)

      | IIntLess             (e1,e2) ->
        IIntLess             (mp e1, mp e2)

      | IIntGreater          (e1,e2) ->
        IIntGreater          (mp e1, mp e2)

      | IIntLessOrEqual      (e1,e2) ->
        IIntLessOrEqual      (mp e1, mp e2)

      | IIntGreaterOrEqual   (e1,e2) ->
        IIntGreaterOrEqual   (mp e1, mp e2)

      | IIntToFloat          (e1)    ->
        IIntToFloat          (mp e1) 

      | IFloatPlus           (e1,e2) ->
        IFloatPlus           (mp e1, mp e2)

      | IFloatMinus          (e1,e2) ->
        IFloatMinus          (mp e1, mp e2)

      | IFloatUnaryMinus     (e1)    ->
        IFloatUnaryMinus     (mp e1) 

      | IFloatMult           (e1,e2) ->
        IFloatMult           (mp e1, mp e2)

      | IFloatDiv            (e1,e2) ->
        IFloatDiv            (mp e1, mp e2)

      | IFloatLess           (e1,e2) ->
        IFloatLess           (mp e1, mp e2)

      | IFloatGreater        (e1,e2) ->
        IFloatGreater        (mp e1, mp e2)

      | IFloatLessOrEqual    (e1,e2) ->
        IFloatLessOrEqual    (mp e1, mp e2)

      | IFloatGreaterOrEqual (e1,e2) ->
        IFloatGreaterOrEqual (mp e1, mp e2)

      | IFloatToInt          (e1)    ->
        IFloatToInt          (mp e1) 

      | IBoolNot             (e1)    ->
        IBoolNot             (mp e1)

      | IBoolAnd             (e1,e2) ->
        IBoolAnd             (mp e1, mp e2)

      | IBoolOr              (e1,e2) ->
        IBoolOr              (mp e1, mp e2)

      | IBoolImplies         (e1,e2) ->
        IBoolImplies         (mp e1, mp e2)

      | IBoolEquiv           (e1,e2) ->
        IBoolEquiv           (mp e1, mp e2)


  % --------------------------------------------------------------------------------
  op findStadCode (allstads : List IStadCode, stadname : String) : Option IStadCode =
   findLeftmost (fn stadcode -> stadcode.label = stadname) allstads

  op initial? (allstads : List IStadCode, stadname : String) : Bool =
   case findStadCode (allstads,stadname) of
     | Some stc -> stc.initial?
     | _ -> false

  op final? (allstads : List IStadCode, stadname : String) : Bool =
   case findStadCode (allstads,stadname) of
     | Some stadcode -> stadcode.steps = []
     | _ -> true

  op reachable? (allstads : List IStadCode, stadname : String) : List String =
    let
      def reachableStads0 (stadname, visited) =
	case findStadCode (allstads, stadname) of
	  | None -> []
	  | Some stc -> 
            let targets = map (fn(_,trg) -> trg) stc.steps in
            foldl (fn (visited, stadname) ->
                     if stadname in? visited then 
                       visited
                     else
                       reachableStads0 (stadname, stadname::visited))
                  visited 
                  targets
    in
    reachableStads0 (stadname, [])

   % --------------------------------------------------------------------------------

}
