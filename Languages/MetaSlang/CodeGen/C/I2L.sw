(*
 Intermediate Representation for Code Generation

 This file contains the definition of the intermediate imperative
 language (i2l) that is used for generating code in imperative
 languages.

*)
I2L qualifying spec {
  % import /Library/Legacy/DataStructures/MergeSort

  import CUtils % for qsort

  sort ImpUnit = {
		  name             : String,
		  includes         : List (ImpUnit),
		  decls            : ImpUnitDecls
		 }

  sort ImpUnitDecls = { 
		       typedefs         : TypeDefinitions,
		       opdecls          : Declarations,
		       funDecls         : FunDeclarations,
		       funDefns         : FunDefinitions,
		       varDecls         : Declarations,
		       mapDecls         : FunDeclarations
		      }

  sort ImpUnits = List ImpUnit

  sort TypeName = String * String

  sort TypeDefinition = TypeName * Type
  sort TypeDefinitions = List TypeDefinition

  sort Type = | Primitive     String
              | RestrictedNat Nat
              | Struct        StructFields
              | Union         UnionFields
              | Tuple         Types
              | BoundList     (Type*Nat)      % list with maximum length
              | List          Type
              | Base          TypeName        % reference to a type definition
              | FunOrMap      (Types*Type)
              | Ref           Type
              | Void
              | Any

  sort Types = List Type

  sort StructField = String * Type
  sort StructFields = List StructField

  sort UnionField = String * Type  % constructor * type
  sort UnionFields = List UnionField

  sort OpName = String * String

  sort Declaration = OpName * Type * Option(Expression)
  sort Declarations = List Declaration

  sort ParameterDeclaration = String * Type
  sort ParameterDeclarations = List ParameterDeclaration

  sort FunDefinition = {
			decl : FunDeclaration,
			body : FunBody
		       }
  sort FunDefinitions = List FunDefinition

  sort FunDeclaration = {
			 name       : OpName,
			 params     : ParameterDeclarations,
			 returntype : Type
			}

  sort FunBody = | Stads StadsFunBody  % state-based
                 | Exp   Expression    % functional

  sort StadsFunBody = List(StadCode)
  sort StadCode = {
		   isInitial     : Boolean,
		   showLabel     : Boolean,
		   decls         : ImpUnit,
		   label         : String,
		   steps         : StepsCode
		  }

  sort FunDeclarations = List FunDeclaration

  sort Expression = Expr * Type

  sort Expr =  | Str            String
              | Int            Integer
              | Float          String
              | Char           Char
              | Bool           Boolean
              | Var            VarName
              | VarDeref       VarName         
              | FunCall        (VarName * (*projections*) List(String) * Expressions)
              | FunCallDeref   (VarName * (*projections*) List(String) * Expressions)
              | MapAccess      (VarName * Type * (*projections:*) List(String) * Expressions)
              | MapAccessDeref (VarName * Type * (*projections:*) List(String) * Expressions)
              | VarRef         VarName
              | IfExpr         (Expression * Expression * Expression)
              | Comma          Expressions
              | Let            (String * Type * Expression * Expression)
              | UnionCaseExpr  (Expression * List(UnionCase))
              | AssignUnion    (String * Option(Expression))
              | ConstrCall     (VarName * String * List(Expression))
              | Builtin        BuiltinExpression
              | TupleExpr      Expressions
              | StructExpr     StructExprFields
              | Project        (Expression * String)

  % a variable reference consists of a unit name and an identifier name
  sort VarName = String * String

  % a UnionCase is used to test a given expression, which must have a
  % union type, which alternative of the union it represents.

  sort UnionCase = 
     | ConstrCase (Option(String) * Option(Type) * List(Option String) * Expression)
     | NatCase (Nat * Expression)
     | CharCase (Char * Expression)

  sort StructExprField = String * Expression
  sort StructExprFields = List StructExprField

  % a case is given by the constructor string, e.g. "Cons" or "Nil", the list of variable names
  % representing the arguments to the constructor (which can be omitted, in case they 
  % are not used in the expression), and the expression
  % that should be evaluated in case the corresping branch is
  % true. "None" as first part of the UnionCase means, that this case
  % matches everything; as a consequence, all cases following the one
  % with the wildcard constructor are not reachable.

  sort BuiltinExpression = | Equals              (Expression * Expression)
                           | StrEquals           (Expression * Expression)
                           | IntPlus             (Expression * Expression)
                           | IntMinus            (Expression * Expression)
                           | IntUnaryMinus       (Expression)
                           | IntMult             (Expression * Expression)
                           | IntDiv              (Expression * Expression)
                           | IntRem              (Expression * Expression)
                           | IntLess             (Expression * Expression)
                           | IntGreater          (Expression * Expression)
                           | IntLessOrEqual      (Expression * Expression)
                           | IntGreaterOrEqual   (Expression * Expression)
                           | IntToFloat          (Expression)
                           | StringToFloat       (Expression)
                           | FloatPlus           (Expression * Expression)
                           | FloatMinus          (Expression * Expression)
                           | FloatUnaryMinus     (Expression)
                           | FloatMult           (Expression * Expression)
                           | FloatDiv            (Expression * Expression)
                           | FloatLess           (Expression * Expression)
                           | FloatGreater        (Expression * Expression)
                           | FloatLessOrEqual    (Expression * Expression)
                           | FloatGreaterOrEqual (Expression * Expression)
                           | FloatToInt          (Expression)
                           | BoolNot             (Expression)
                           | BoolAnd             (Expression * Expression)
                           | BoolOr              (Expression * Expression)
                           | BoolImplies         (Expression * Expression)
                           | BoolEquiv           (Expression * Expression)


  sort Expressions = List Expression

  % These are the rules that can occur in the body of a transformation step.
  % An UpdateBlock contains a list of assignments together with local declaration
  % that are needed to realize the parallel update semantics
  % e.g. for updates x:=y,y:=x we have to introduce a auxiliary variable z to store
  % the value of one of x or y, e.g. int z:=x;x:=y;y:=z (assuming x,y of sort Nat)

  sort Rule =  | Skip
              | UpdateBlock (Declarations * Updates)
              | Cond        (Expression * Rule)
              | Update      Update
              | ProcCall    (String * Expressions)

  sort Rules = List Rule

  sort Update = Option(Expression) * Expression
  sort Updates = List Update

  % a step consists of rules and a next state label.
  % the rules are supposed to be executed in parallel
  sort StepCode = Rule * String
  sort StepsCode = List StepCode

  % API ------------------------------------------------

  op isProc: FunDefinition -> Boolean
  def isProc(fpdef) =
    fpdef.decl.returntype = Void

  op isFun: FunDefinition -> Boolean
  def isFun(fpdef) = ~(isProc(fpdef))


  op mergeImpUnit: String * List ImpUnit -> ImpUnit
  def mergeImpUnit(name,impunitlist) =
    case impunitlist of
      | [impunit] -> {
		      name=name,
		      includes=impunit.includes,
		      decls = impunit.decls
		     }
      | iu1::iu2::iulst -> let iu = {
				     name=name,
				     includes = concat(iu1.includes,iu2.includes),
				     decls = {
					      typedefs = concat(iu1.decls.typedefs,iu2.decls.typedefs),
					      opdecls = concat(iu1.decls.opdecls,iu2.decls.opdecls),
					      funDecls = concat(iu1.decls.funDecls,iu2.decls.funDecls),
					      funDefns = concat(iu1.decls.funDefns,iu2.decls.funDefns),
					      varDecls = concat(iu1.decls.varDecls,iu2.decls.varDecls),
					      mapDecls = concat(iu1.decls.mapDecls,iu2.decls.mapDecls)
					     }
				  }
			 in
			 mergeImpUnit(name,cons(iu,iulst))

  op addInclude: ImpUnit * ImpUnit -> ImpUnit
  def addInclude(iu,includedImpUnit) =
    {
     name = iu.name,
     includes = iu.includes ++ [includedImpUnit],
     decls = iu.decls
    }

  op addFunDefinition: ImpUnit * FunDefinition -> ImpUnit
  def addFunDefinition(iu,fdefn) =
    {
     name = iu.name,
     includes = iu.includes,
     decls = {
	      typedefs = iu.decls.typedefs,
	      opdecls = iu.decls.opdecls,
	      funDecls = iu.decls.funDecls,
	      funDefns = concat(iu.decls.funDefns,[fdefn]),
	      varDecls = iu.decls.varDecls,
	      mapDecls = iu.decls.mapDecls
	     }
    }

  op emptyImpUnit: String -> ImpUnit
  def emptyImpUnit(name) =
    {
     name = name,
     includes = [],
     decls = {
	      typedefs = [],
	      opdecls = [],
	      funDecls = [],
	      funDefns = [],
	      varDecls = [],
	      mapDecls = []
	     }
    }

  % --------------------------------------------------------------------------------

  op substVarName: Expression * VarName * VarName -> Expression
  def substVarName(expr,(old1,old2),newvar) =
    mapExpression (fn(e) ->
		   case e of
                     | Var(id1,id2) ->
		       if (id1=old1)&(id2=old2) then Var(newvar) else e
                     | VarRef(id1,id2) ->
		       if (id1=old1)&(id2=old2) then VarRef(newvar) else e
		     | VarDeref(id1,id2) ->
		       if (id1=old1)&(id2=old2) then VarDeref(newvar) else e
		     | FunCall((id1,id2),p,x) ->
		       if (id1=old1)&(id2=old2) then FunCall(newvar,p,x) else e
		     | FunCallDeref((id1,id2),p,x) ->
		       if (id1=old1)&(id2=old2) then FunCallDeref(newvar,p,x) else e
		     | _ -> e) expr
		     

  op substVarByExpr: Expression * VarName * Expr -> Expression
  def substVarByExpr(expr,(v1,v2),sexpr) =
    mapExpression (fn(e) ->
		   case e of
                     | Var(id1,id2) ->
		       if (id1=v1)&(id2=v2) then sexpr else e
		     | _ -> e) expr

  % --------------------------------------------------------------------------------

  op sortTypeDefinitions: ImpUnit -> TypeDefinitions -> TypeDefinitions
  def sortTypeDefinitions iu (typedefns) =
    qsort (typeDefnMustFollow iu) typedefns 

  op typeDefnMustFollow: ImpUnit -> TypeDefinition * TypeDefinition -> Boolean
  def typeDefnMustFollow iu (td1 as (tname1 as (_,id1),_),td2 as (tname2 as (_,id2),_)) =
    let deps1 = typeDefinitionDepends(iu,td1) in
    let deps2 = typeDefinitionDepends(iu,td2) in
    let res = (List.member(tname2,deps1)) in
    %let _ = if res then String.writeLine(id1^" must follow "^id2) else
    %                    String.writeLine(id1^" does not depend on "^id2)
    %in
    res

  op typeDefinitionDepends : ImpUnit * TypeDefinition -> List(TypeName)
  def typeDefinitionDepends(iu,typedef as (tname,typ)) =
    typeDepends(iu,tname,typ)

  op typeDepends: ImpUnit * TypeName * Type -> List(TypeName)
  def typeDepends(iu,t0name,t0) =
    let 
      def typeDepends0(iu,t,deps) =
	case t of
	  | Base (tname as (_,id1)) -> 
	                  let _ =
			  if t0name = tname then
			    System.fail("sorry, this version of the code generator"^
					" doesn't support recursive types: "
					^"\""^id1^"\"")
			  else ()
			  in
	                  if List.member(tname,deps) then deps
			  else
			    let deps = cons(tname,deps) in
			    (case findTypeDefn(iu,tname) of
			       | Some t -> typeDepends0(iu,t,deps)
			       | None -> deps
			    )
	  | Struct fields -> List.foldl (fn((_,t),deps) -> typeDepends0(iu,t,deps)) deps fields
	  | Union fields -> List.foldl (fn((_,t),deps) -> typeDepends0(iu,t,deps)) deps fields
	  | Tuple types -> List.foldl (fn(t,deps) -> typeDepends0(iu,t,deps)) deps types
	  | BoundList(t,_) -> typeDepends0(iu,t,deps)
	  | FunOrMap(types,t) -> List.foldl (fn(t,deps) -> typeDepends0(iu,t,deps)) 
	                         (typeDepends0(iu,t,deps)) types
	  | Ref t -> typeDepends0(iu,t,deps)
	  | _ -> deps
    in
    typeDepends0(iu,t0,[])

  op findTypeDefn: ImpUnit * TypeName -> Option Type
  def findTypeDefn(iu,tname) =
    case List.find (fn(tname0,_) -> tname0 = tname) iu.decls.typedefs of
      | Some (_,t) -> Some t
      | None -> None
  

  op impUnitSortTypeDefinitions: ImpUnit -> ImpUnit
  def impUnitSortTypeDefinitions(iu) =
    {
     name = iu.name,
     includes = iu.includes,
     decls = {
	      typedefs = sortTypeDefinitions iu iu.decls.typedefs,
	      opdecls = iu.decls.opdecls,
	      funDecls = iu.decls.funDecls,
	      funDefns = iu.decls.funDefns,
	      varDecls = iu.decls.varDecls,
	      mapDecls = iu.decls.mapDecls
	     }
    }

  % --------------------------------------------------------------------------------

  op mapExpression: (Expr -> Expr) -> Expression -> Expression
  def mapExpression f (e,t) =
    (mapExpr f e,t)

  op mapExpr: (Expr -> Expr) -> Expr -> Expr
  def mapExpr f e =
    let mp = (fn(e,t) -> (mapExpr f e,t)) in
    let e = f e in
    case e of
      | FunCall(v,p,exprs) -> let exprs = List.map mp exprs in
                           FunCall(v,p,exprs)
      | FunCallDeref(v,p,exprs) -> let exprs = List.map mp exprs in
                           FunCallDeref(v,p,exprs)
      | IfExpr(e1,e2,e3) -> IfExpr(mp e1,mp e2,mp e3)
      | Comma(exprs) -> let exprs = List.map mp exprs in
                           Comma(exprs)
      | Let(s,t,e1,e2) -> Let(s,t,mp e1,mp e2)
      | UnionCaseExpr(e,ucl) -> 
	UnionCaseExpr(mp e,List.map 
		      (fn(ucase) ->
		       case ucase of 
			 | ConstrCase(x1,x2,x3,e) -> ConstrCase(x1,x2,x3,mp e)
			 | NatCase(n,e) -> NatCase(n,mp e)
			 | CharCase(c,e) -> CharCase(c,mp e)
			) ucl)
      | AssignUnion(s,optexpr) -> AssignUnion(s,case optexpr of None -> None | Some e -> Some(mp e))
      | ConstrCall(varname,consid,exprs) -> let exprs = List.map mp exprs in
	                                    ConstrCall(varname,consid,exprs)
      | Builtin(bexp) -> Builtin(mapBuiltin f bexp)
      | TupleExpr(exprs) -> let exprs = List.map mp exprs in
			   TupleExpr(exprs)
      | StructExpr(fields) -> let fields = List.map (fn(s,e) -> (s,mp e)) fields in
			   StructExpr fields
      | Project(expr,s) -> Project(mp expr,s)
      | _ -> e

  op mapBuiltin: (Expr -> Expr) -> BuiltinExpression -> BuiltinExpression
  def mapBuiltin f e =
    let mp = (fn(e,t) -> (mapExpr f e,t)) in
    case e of
      | Equals(e1,e2) -> Equals(mp e1,mp e2)
      | StrEquals(e1,e2) -> StrEquals(mp e1,mp e2)
      | IntPlus(e1,e2) -> IntPlus(mp e1,mp e2)
      | IntMinus(e1,e2) -> IntMinus(mp e1,mp e2)
      | IntUnaryMinus(e1) -> IntUnaryMinus(mp e1)
      | IntMult(e1,e2) -> IntMult(mp e1,mp e2)
      | IntDiv(e1,e2) -> IntDiv(mp e1,mp e2)
      | IntRem(e1,e2) -> IntRem(mp e1,mp e2)
      | IntLess(e1,e2) -> IntLess(mp e1,mp e2)
      | IntGreater(e1,e2) -> IntGreater(mp e1,mp e2)
      | IntLessOrEqual(e1,e2) -> IntLessOrEqual(mp e1,mp e2)
      | IntGreaterOrEqual(e1,e2) -> IntGreaterOrEqual(mp e1,mp e2)
      | IntToFloat(e1) -> IntToFloat(mp e1) 
      | FloatPlus(e1,e2) -> FloatPlus(mp e1,mp e2)
      | FloatMinus(e1,e2) -> FloatMinus(mp e1,mp e2)
      | FloatUnaryMinus(e1) -> FloatUnaryMinus(mp e1) 
      | FloatMult(e1,e2) -> FloatMult(mp e1,mp e2)
      | FloatDiv(e1,e2) -> FloatDiv(mp e1,mp e2)
      | FloatLess(e1,e2) -> FloatLess(mp e1,mp e2)
      | FloatGreater(e1,e2) -> FloatGreater(mp e1,mp e2)
      | FloatLessOrEqual(e1,e2) -> FloatLessOrEqual(mp e1,mp e2)
      | FloatGreaterOrEqual(e1,e2) -> FloatGreaterOrEqual(mp e1,mp e2)
      | FloatToInt(e1) -> FloatToInt(mp e1) 
      | BoolNot(e1) -> BoolNot(mp e1)
      | BoolAnd(e1,e2) -> BoolAnd(mp e1,mp e2)
      | BoolOr(e1,e2) -> BoolOr(mp e1,mp e2)
      | BoolImplies(e1,e2) -> BoolImplies(mp e1,mp e2)
      | BoolEquiv(e1,e2) -> BoolEquiv(mp e1,mp e2)

  % --------------------------------------------------------------------------------
   
  op findStadCode: List(StadCode) * String -> Option(StadCode)
  def findStadCode(allstads,stadname) =
    List.find (fn(stadcode) -> stadcode.label = stadname) allstads

  op stadIsInitial: List(StadCode) * String -> Boolean
  def stadIsInitial(allstads,stadname) =
    case findStadCode(allstads,stadname) of
      | Some stc -> stc.isInitial
      | None -> false

  op stadIsFinal: List(StadCode) * String -> Boolean
  def stadIsFinal(allstads,stadname) =
    case findStadCode(allstads,stadname) of
      | Some stadcode -> stadcode.steps = []
      | None -> true

  op reachableStads: List(StadCode) * String -> List(String)
  def reachableStads(allstads,stadname) =
    let
      def reachableStads0(stadname,visited) =
	case findStadCode(allstads,stadname) of
	  | None -> []
	  | Some stc -> let targets = List.map (fn(_,trg) -> trg) stc.steps in
	                List.foldl
			  (fn(stadname,visited) ->
			   if List.member(stadname,visited) then visited
			   else
			     reachableStads0(stadname,cons(stadname,visited))
			    )
			  visited targets
    in
    reachableStads0(stadname,[])

   % --------------------------------------------------------------------------------



}
