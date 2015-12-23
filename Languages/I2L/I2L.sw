(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(*
 * Intermediate Representation for Code Generation
 *
 * This file contains the definition of the intermediate imperative
 * language (i2l) that is used for generating code in imperative
 * languages.
 *)

I2L qualifying spec
{
  import /Library/Legacy/Utilities/System

  op [X] CUtils.quickSort (gt : X*X->Bool) (l : List X) : List X  % TODO: defined in CUtils.sw

  type I_ImpUnit = {
                    name     : String,
                    includes : I_ImpUnits,
                    decls    : I_ImpUnitDecls
                    }
  type I_ImpUnits = List I_ImpUnit

  type I_ImpUnitDecls = { 
                         typedefs : I_TypeDefinitions,
                         opdecls  : I_Declarations,
                         funDecls : I_FunDeclarations,
                         funDefns : I_FunDefinitions,
                         varDecls : I_Declarations,
                         mapDecls : I_FunDeclarations
                         }

  type I_TypeName = String * String
  type I_OpName   = String * String
  type I_VarName  = String * String    % var reference consists of a unit name and an identifier name

  type I_TypeDefinition = I_TypeName * I_Type * Bool % native?
  type I_TypeDefinitions = List I_TypeDefinition

  type I_Primitive = | I_Bool | I_Char | I_String | I_Nat | I_Int | I_Float

  type I_NameSpace = | Type | Struct | Enum | Union

  type I_Type = | I_Primitive   I_Primitive
                | I_BoundedNat  Nat               % Nats within inclusive bound  (e.g. 'unsigned short')
                | I_BoundedInt  Int * Int         % Ints within inclusive bounds (e.g. 'signed short')
                | I_Enum        I_EnumFields
                | I_Struct      I_StructFields
                | I_Union       I_UnionFields
                | I_Tuple       I_Types
                | I_BoundedList I_Type * Nat      % list with maximum length
                | I_List        I_Type
                | I_Base        I_TypeName * I_NameSpace 
                | I_FunOrMap    I_Types * I_Type
                | I_Ref         I_Type            % ptr type
                | I_Void
                | I_Any
                | I_Problem     String            % to avoid need for passing Option, error messages, etc.
 

  type I_Types = List I_Type

  type I_EnumField = String
  type I_EnumFields = List I_EnumField

  type I_StructField = String * I_Type
  type I_StructFields = List I_StructField

  type I_UnionField = String * I_Type  % constructor * typ
  type I_UnionFields = List I_UnionField

  type I_Declaration = I_OpName * I_Type * Option I_TypedExpr
  type I_Declarations = List I_Declaration

  type I_ParameterDeclaration = String * I_Type
  type I_ParameterDeclarations = List I_ParameterDeclaration

  type I_FunDefinition = {
                          decl : I_FunDeclaration,
                          body : I_FunBody
                          }
  type I_FunDefinitions = List I_FunDefinition

  type I_FunDeclaration = {
                           name       : I_OpName,
                           params     : I_ParameterDeclarations,
                           returntype : I_Type
                           }
  type I_FunDeclarations = List I_FunDeclaration

  type I_FunBody = | I_Stads I_StadsFunBody  % state-based
                   | I_Exp   I_TypedExpr    % functional

  type I_StadCode = {
                     initial?   : Bool,
                     showLabel? : Bool,
                     decls      : I_ImpUnit,
                     label      : String,
                     steps      : I_StepsCode
                     }
  type I_StadsFunBody = List I_StadCode

  type I_TypedExprs = List I_TypedExpr
  type I_TypedExpr  = {expr: I_Expr, typ : I_Type, cast? : Bool}

  type I_Expr = | I_Str            String
                | I_Int            Int
                | I_Float          Bool * Nat * Nat * Option (Bool * Nat) % -1.2E-3
                | I_Char           Char
                | I_Bool           Bool

                | I_Var            I_VarName
                | I_VarRef         I_VarName
                | I_VarDeref       I_VarName         

                | I_FunCall        I_OpName * (*projections*) List String * I_TypedExprs
                | I_FunCallDeref   I_OpName * (*projections*) List String * I_TypedExprs
                | I_MapAccess      I_OpName * I_Type * (*projections:*) List String * I_TypedExprs
                | I_MapAccessDeref I_OpName * I_Type * (*projections:*) List String * I_TypedExprs
                | I_IfExpr         I_TypedExpr * I_TypedExpr * I_TypedExpr
                | I_Comma          I_TypedExprs
                | I_Let            String * I_Type * (Option I_TypedExpr) * I_TypedExpr * Bool % Bool indicates mv return
                | I_UnionCaseExpr  I_TypedExpr * List I_UnionCase            % dispatch among variants of a coproduct/union
                | I_Embedded       I_Selector * I_TypedExpr                  % test for a variant of a coproduct/union
                | I_AssignUnion    I_Selector * Option I_TypedExpr           % set the variant field for a union
                | I_ConstrCall     I_OpName * I_Selector * List I_TypedExpr  % call a constructor as a function
                | I_Builtin        I_BuiltinExpression
                | I_TupleExpr      I_TypedExprs                              % create a structure using generated field names
                | I_StructExpr     I_StructExprFields                        % create a structure using given names
                | I_Project        I_TypedExpr * String                      % access a field   in a product/structure
                | I_Select         I_TypedExpr * String                      % access a variant in a coproduct/union 
                | I_Null                                                     % for functions that return void

                | I_Problem        String                                    % to avoid need for passing Option, error messages, etc.


  op I_True  : I_TypedExpr = {expr = I_Bool true,  typ = I_Primitive I_Bool, cast? = false} 
  op I_False : I_TypedExpr = {expr = I_Bool false, typ = I_Primitive I_Bool, cast? = false} 

  op I_Zero  : I_TypedExpr = {expr = I_Int 0, typ = I_Primitive I_Nat, cast? = false} 
  op I_One   : I_TypedExpr = {expr = I_Int 1, typ = I_Primitive I_Nat, cast? = false} 

  type I_Selector = {name  : String, index : Nat}

  % I_UnionCase is used to test and dispatch within I_UnionCaseExpr
  % It tests a given expression, which must have a union type, to see if it  
  % has a particular alternative type of the union, and if so, dispatches
  % to an expression to be evaluated.
  %
  % Note that I_Embedded is used for predicates that simply test such expressions 
  % directly, as in if statements.

  type I_UnionCase = | I_ConstrCase  Option I_Selector * List (Option String) * I_TypedExpr
                     | I_VarCase     String * I_Type                          * I_TypedExpr
                     | I_NatCase     Nat                                      * I_TypedExpr
                     | I_CharCase    Char                                     * I_TypedExpr

  type I_StructExprField = String * I_TypedExpr
  type I_StructExprFields = List I_StructExprField

  % a case is given by the constructor string, e.g. "Cons" or "Nil", the list of variable names
  % representing the arguments to the constructor (which can be omitted, in case they 
  % are not used in the expression), and the expression
  % that should be evaluated in case the corresping branch is
  % true. "None" as first part of the UnionCase means, that this case
  % matches everything; as a consequence, all cases following the one
  % with the wildcard constructor are not reachable.

  type I_BuiltinExpression = | I_Equals              I_TypedExpr * I_TypedExpr

                             | I_BoolNot             I_TypedExpr
                             | I_BoolAnd             I_TypedExpr * I_TypedExpr
                             | I_BoolOr              I_TypedExpr * I_TypedExpr
                             | I_BoolImplies         I_TypedExpr * I_TypedExpr
                             | I_BoolEquiv           I_TypedExpr * I_TypedExpr

                             | I_IntPlus             I_TypedExpr * I_TypedExpr
                             | I_IntMinus            I_TypedExpr * I_TypedExpr
                             | I_IntUnaryMinus       I_TypedExpr
                             | I_IntMult             I_TypedExpr * I_TypedExpr
                             | I_IntDiv              I_TypedExpr * I_TypedExpr
                             | I_IntRem              I_TypedExpr * I_TypedExpr
                             | I_IntLess             I_TypedExpr * I_TypedExpr
                             | I_IntGreater          I_TypedExpr * I_TypedExpr
                             | I_IntLessOrEqual      I_TypedExpr * I_TypedExpr
                             | I_IntGreaterOrEqual   I_TypedExpr * I_TypedExpr

                             | I_IntToFloat          I_TypedExpr
                             | I_StringToFloat       I_TypedExpr

                             | I_FloatPlus           I_TypedExpr * I_TypedExpr
                             | I_FloatMinus          I_TypedExpr * I_TypedExpr
                             | I_FloatUnaryMinus     I_TypedExpr
                             | I_FloatMult           I_TypedExpr * I_TypedExpr
                             | I_FloatDiv            I_TypedExpr * I_TypedExpr
                             | I_FloatLess           I_TypedExpr * I_TypedExpr
                             | I_FloatGreater        I_TypedExpr * I_TypedExpr
                             | I_FloatLessOrEqual    I_TypedExpr * I_TypedExpr
                             | I_FloatGreaterOrEqual I_TypedExpr * I_TypedExpr
                             | I_FloatToInt          I_TypedExpr
 
                             | I_StrLess             I_TypedExpr * I_TypedExpr
                             | I_StrEquals           I_TypedExpr * I_TypedExpr
                             | I_StrGreater          I_TypedExpr * I_TypedExpr

  %% These are the rules that can occur in the body of a transformation step.
  %% An UpdateBlock contains a list of assignments together with local declaration
  %% that are needed to realize the parallel update semantics
  %% e.g. for updates x:=y,y:=x we have to introduce a auxiliary variable z to store
  %% the value of one of x or y, e.g. int z:=x;x:=y;y:=z (assuming x,y of type Nat)

  type I_Rule = | I_Skip
                | I_UpdateBlock I_Declarations * I_Updates
                | I_Cond        I_TypedExpr * I_Rule
                | I_Update      I_Update
                | I_ProcCall    String * I_TypedExprs
  type I_Rules = List I_Rule

  type I_Update = Option I_TypedExpr * I_TypedExpr
  type I_Updates = List I_Update

  % a step consists of rules and a next state label.
  % the rules are supposed to be executed in parallel
  type I_StepCode = I_Rule * String
  type I_StepsCode = List I_StepCode

  % API ------------------------------------------------

  op iproc? (fpdef : I_FunDefinition) : Bool = fpdef.decl.returntype = I_Void
  op ifun?  (fpdef : I_FunDefinition) : Bool = ~(iproc? fpdef)
                    
  op mergeImpUnit (name : String, impunitlist : I_ImpUnits) : I_ImpUnit =
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

  op addInclude (iu : I_ImpUnit, includedImpUnit : I_ImpUnit) : I_ImpUnit =
   iu << {includes = iu.includes ++ [includedImpUnit]}

  op addFunDefinition (iu : I_ImpUnit, fdefn : I_FunDefinition) : I_ImpUnit =
   iu << {decls = {
                   typedefs = iu.decls.typedefs,
                   opdecls = iu.decls.opdecls,
                   funDecls = iu.decls.funDecls,
                   funDefns = iu.decls.funDefns ++ [fdefn],
                   varDecls = iu.decls.varDecls,
                   mapDecls = iu.decls.mapDecls
                  }}

  op emptyImpUnit (name : String) : I_ImpUnit =
   {
    name     = name,
    includes = [],
    decls    = {
                typedefs = [],
                opdecls  = [],
                funDecls = [],
                funDefns = [],
                varDecls = [],
                mapDecls = []
                }
   }

  % --------------------------------------------------------------------------------

  op substVarName (typed_expr : I_TypedExpr, (old1, old2) : I_VarName, newvar : I_VarName)
   : I_TypedExpr =
   mapExpression (fn e ->
                    case e of
                      | I_Var (id1,id2) ->
                        if (id1=old1)&&(id2=old2) then I_Var newvar else e

                      | I_VarRef (id1,id2) ->
                        if (id1=old1)&&(id2=old2) then I_VarRef newvar else e

                      | I_VarDeref (id1,id2) ->
                        if (id1=old1)&&(id2=old2) then I_VarDeref newvar else e

                      | I_FunCall ((id1,id2),p,x) ->
                        if (id1=old1)&&(id2=old2) then I_FunCall(newvar,p,x) else e

                      | I_FunCallDeref ((id1,id2),p,x) ->
                        if (id1=old1)&&(id2=old2) then I_FunCallDeref(newvar,p,x) else e

                      | _ -> e) 
                 typed_expr

  op substVarByExpr (typed_expr : I_TypedExpr, (v1,v2) : I_VarName, sexp : I_Expr) : I_TypedExpr =
   mapExpression (fn e ->
                    case e of
                      | I_Var (id1,id2) ->
                        if (id1=v1)&&(id2=v2) then sexp else e
                      | _ -> e) 
                 typed_expr

  % --------------------------------------------------------------------------------

  op sortTypeDefinitions (iu : I_ImpUnit) (typedefns : I_TypeDefinitions) : I_TypeDefinitions =
   quickSort (typeDefnMustFollow iu) typedefns 

  op typeDefnMustFollow (iu : I_ImpUnit) 
                        (td1 as (tname1 as (_,id1),_,_) : I_TypeDefinition,
                         td2 as (tname2 as (_,id2),_,_) : I_TypeDefinition)
   : Bool =
   let deps1 = typeDefinitionDepends (iu, td1) in
   let deps2 = typeDefinitionDepends (iu, td2) in
   let res = tname2 in? deps1 in
   %let _ = if res then writeLine(id1^" must follow "^id2) else
   %                    writeLine(id1^" does not depend on "^id2)
   %in
   res

  op typeDefinitionDepends (iu : I_ImpUnit, typedef as (tname,typ,_) : I_TypeDefinition)
   : List I_TypeName =
   typeDepends(iu,tname,typ)

  op typeDepends (iu : I_ImpUnit, t0name : I_TypeName, t0 : I_Type) : List I_TypeName =
   let 
     def typeDepends0 (iu, t, deps) =
       case t of

         | I_Base (tname as (_, id1), _) -> 
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

         | I_Struct fields -> foldl (fn (deps, (_, t)) -> typeDepends0 (iu, t, deps)) deps fields
         | I_Union  fields -> foldl (fn (deps, (_, t)) -> typeDepends0 (iu, t, deps)) deps fields
         | I_Tuple  types  -> foldl (fn (deps, t)      -> typeDepends0 (iu, t, deps)) deps types

         | I_BoundedList (t, _)  -> typeDepends0 (iu, t, deps)
         | I_Ref         t       -> typeDepends0 (iu, t, deps)

         | I_FunOrMap (types, t) -> foldl (fn (deps, t) -> typeDepends0 (iu, t, deps))
                                          (typeDepends0 (iu, t, deps))
                                          types
         | _ -> deps
    in
    typeDepends0 (iu, t0, [])

  op findTypeDefn (iu : I_ImpUnit, tname : I_TypeName) : Option I_Type =
   case findLeftmost (fn (tname0, _,_) -> tname0 = tname) iu.decls.typedefs of
     | Some (_,t,_) -> Some t
     | _ -> None
  

  op impUnitSortTypeDefinitions (iu : I_ImpUnit) : I_ImpUnit =
   let decls = iu.decls << {typedefs = sortTypeDefinitions iu iu.decls.typedefs} in
   iu << {decls = decls} 

  % --------------------------------------------------------------------------------

  op mapExpression (f : I_Expr -> I_Expr) (typed_expr : I_TypedExpr) : I_TypedExpr =
    typed_expr << {expr = mapExpr f typed_expr.expr}

  op mapExpr (f : I_Expr -> I_Expr) (e : I_Expr) : I_Expr =
   let mp = (fn typed_expr -> typed_expr << {expr = mapExpr f typed_expr.expr}) in
   %% process parent term before child terms
   let e = f e in
   case e of

      | I_FunCall (v, p,        exps) -> 
        I_FunCall (v, p, map mp exps)

      | I_FunCallDeref (v, p,        exps) ->
        I_FunCallDeref (v, p, map mp exps)

      | I_MapAccess (v, typ, projs,        exps) ->
        I_MapAccess (v, typ, projs, map mp exps) 

      | I_MapAccessDeref (v, typ, projs,        exps) ->
        I_MapAccessDeref (v, typ, projs, map mp exps) 

      | I_IfExpr (   e1,    e2,    e3) -> 
        I_IfExpr (mp e1, mp e2, mp e3)

      | I_Comma (       exps) -> 
        I_Comma (map mp exps)

      | I_Let (s, t,    e1,    e2, mv?) -> 
        I_Let (s, t, 
               case e1 of Some e1 -> Some (mp e1) | _ -> None,
               mp e2,
               mv?)

      | I_UnionCaseExpr (   e, ucl) -> 
        let ucl = 
            map (fn ucase ->
                   case ucase of 
                     | I_ConstrCase (x1, x2,    e) -> 
                       I_ConstrCase (x1, x2, mp e)

                     | I_VarCase (id, ityp,    e) -> 
                       I_VarCase (id, ityp, mp e)

                     | I_NatCase (n,     e) -> 
                       I_NatCase (n,  mp e)

                     | I_CharCase(c,     e) -> 
                       I_CharCase(c,  mp e))
                ucl
        in
        I_UnionCaseExpr (mp e, ucl)

      | I_Embedded (s,    t) ->
        I_Embedded (s, mp t) 

      | I_AssignUnion(s, optexp) -> 
        let optexp = case optexp of 
                       | None   -> None 
                       | Some e -> Some (mp e)
        in
        I_AssignUnion(s, optexp)

      | I_ConstrCall (varname, consid,        exps) -> 
        I_ConstrCall (varname, consid, map mp exps)

      | I_Builtin (             bexp) -> 
        I_Builtin (mapBuiltin f bexp)

      | I_TupleExpr (       exps) -> 
        I_TupleExpr (map mp exps)

      | I_StructExpr fields -> 
        let fields = map (fn(s,e) -> (s,mp e)) fields in
        I_StructExpr fields

      | I_Project (   exp, s) -> 
        I_Project (mp exp, s)

      | I_Select  (   exp, s) -> 
        I_Select  (mp exp, s)

      | _ -> 
        % I_Str, I_Int, I_Float, I_Char, I_Bool, I_Var, I_VarDeref, I_VarRef :
        e  

  op mapBuiltin (f : I_Expr -> I_Expr) (exp : I_BuiltinExpression) : I_BuiltinExpression =
    let mp = fn typed_expr -> typed_expr << {expr = mapExpr f typed_expr.expr} in
    case exp of

      | I_Equals              (   e1,    e2) ->
        I_Equals              (mp e1, mp e2)

      | I_BoolNot             (   e1) ->
        I_BoolNot             (mp e1)

      | I_BoolAnd             (   e1,    e2) ->
        I_BoolAnd             (mp e1, mp e2)

      | I_BoolOr              (   e1,    e2) ->
        I_BoolOr              (mp e1, mp e2)

      | I_BoolImplies         (   e1,    e2) ->
        I_BoolImplies         (mp e1, mp e2)

      | I_BoolEquiv           (   e1,    e2) ->
        I_BoolEquiv           (mp e1, mp e2)

      | I_IntPlus             (   e1,    e2) ->
        I_IntPlus             (mp e1, mp e2)

      | I_IntMinus            (   e1,    e2) ->
        I_IntMinus            (mp e1, mp e2)

      | I_IntUnaryMinus       (   e1) ->
        I_IntUnaryMinus       (mp e1)

      | I_IntMult             (   e1,    e2) ->
        I_IntMult             (mp e1, mp e2)

      | I_IntDiv              (   e1,    e2) ->
        I_IntDiv              (mp e1, mp e2)

      | I_IntRem              (   e1,    e2) ->
        I_IntRem              (mp e1, mp e2)

      | I_IntLess             (   e1,    e2) ->
        I_IntLess             (mp e1, mp e2)

      | I_IntGreater          (   e1,    e2) ->
        I_IntGreater          (mp e1, mp e2)

      | I_IntLessOrEqual      (   e1,    e2) ->
        I_IntLessOrEqual      (mp e1, mp e2)

      | I_IntGreaterOrEqual   (   e1,    e2) ->
        I_IntGreaterOrEqual   (mp e1, mp e2)

      | I_IntToFloat          (   e1) ->
        I_IntToFloat          (mp e1) 

      | I_StringToFloat       (   e1) ->
        I_StringToFloat       (mp e1) 

      | I_FloatPlus           (   e1,    e2) ->
        I_FloatPlus           (mp e1, mp e2)

      | I_FloatMinus          (   e1,    e2) ->
        I_FloatMinus          (mp e1, mp e2)

      | I_FloatUnaryMinus     (   e1) ->
        I_FloatUnaryMinus     (mp e1) 

      | I_FloatMult           (   e1,    e2) ->
        I_FloatMult           (mp e1, mp e2)

      | I_FloatDiv            (   e1,    e2) ->
        I_FloatDiv            (mp e1, mp e2)

      | I_FloatLess           (   e1,    e2) ->
        I_FloatLess           (mp e1, mp e2)

      | I_FloatGreater        (   e1,    e2) ->
        I_FloatGreater        (mp e1, mp e2)

      | I_FloatLessOrEqual    (   e1,    e2) ->
        I_FloatLessOrEqual    (mp e1, mp e2)

      | I_FloatGreaterOrEqual (   e1,    e2) ->
        I_FloatGreaterOrEqual (mp e1, mp e2)

      | I_FloatToInt          (   e1) ->
        I_FloatToInt          (mp e1) 

      | I_StrLess             (   e1,    e2) ->
        I_StrLess             (mp e1, mp e2)

      | I_StrEquals           (   e1,    e2) ->
        I_StrEquals           (mp e1, mp e2)

      | I_StrGreater          (   e1,    e2) ->
        I_StrGreater          (mp e1, mp e2)

  % --------------------------------------------------------------------------------
  op findStadCode (allstads : List I_StadCode, stadname : String) : Option I_StadCode =
   findLeftmost (fn stadcode -> stadcode.label = stadname) allstads

  op initial? (allstads : List I_StadCode, stadname : String) : Bool =
   case findStadCode (allstads,stadname) of
     | Some stc -> stc.initial?
     | _ -> false

  op final? (allstads : List I_StadCode, stadname : String) : Bool =
   case findStadCode (allstads,stadname) of
     | Some stadcode -> stadcode.steps = []
     | _ -> true

  op reachable? (allstads : List I_StadCode, stadname : String) : List String =
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
