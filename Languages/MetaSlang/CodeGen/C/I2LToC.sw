(**
 translation from the Intermediate Imperative Language to C
 *)

I2LToC qualifying spec {

  import C
  import I2L
  import CUtils
  import CGenOptions

  % import ESpecsCodeGenerationOptions

  import /Library/Legacy/DataStructures/ListPair

  type CgContext = {
		    xcspc : CSpec,                 % for incrementatl code generation, this field holds the existing cspec that is extended
		    useRefTypes : Boolean,
		    currentFunName: Option(String),
		    currentFunParams: CVarDecls
		   }

  op defaultCgContext: CgContext
  def defaultCgContext = {
			  xcspc = emptyCSpec(""),
			  useRefTypes = true,
			  currentFunName = None,
			  currentFunParams = []
			 }

  op setCurrentFunName: CgContext * String -> CgContext
  def setCurrentFunName(ctxt,id) =
    {xcspc=ctxt.xcspc,useRefTypes=ctxt.useRefTypes,currentFunName=Some id,currentFunParams=ctxt.currentFunParams}

  op setCurrentFunParams: CgContext * CVarDecls -> CgContext
  def setCurrentFunParams(ctxt,params) =
    {xcspc=ctxt.xcspc,useRefTypes=ctxt.useRefTypes,currentFunName=ctxt.currentFunName,currentFunParams=params}

  op generateC4ImpUnit: ImpUnit * CSpec * Boolean -> CSpec
  def generateC4ImpUnit(impunit, xcspc, useRefTypes) =
    %let _ = writeLine(";;   phase 2: generating C...") in
    let ctxt = {xcspc=xcspc,useRefTypes=useRefTypes,currentFunName=None,currentFunParams=[]} in
    let cspc = emptyCSpec(impunit.name) in
    let cspc = addBuiltIn(ctxt,cspc) in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4TypeDefinition(ctxt,cspc,typedef))
		cspc impunit.decls.typedefs
    in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4OpDecl(ctxt,cspc,typedef))
		cspc impunit.decls.opdecls
    in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4FunDecl(ctxt,cspc,typedef))
		cspc impunit.decls.funDecls
    in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4FunDefn(ctxt,cspc,typedef))
		cspc impunit.decls.funDefns
    in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4VarDecl(ctxt,cspc,typedef))
		cspc impunit.decls.varDecls
    in
    let cspc = List.foldl
                (fn(typedef,cspc) ->
		 c4MapDecl(ctxt,cspc,typedef))
		cspc impunit.decls.mapDecls
    in
    let cspc = postProcessCSpec cspc
    in
    cspc

  op postProcessCSpec: CSpec -> CSpec
  def postProcessCSpec(cspc) =
    let cspc = sortStructUnionTypeDefns cspc in
    let cspc = deleteUnusedTypes cspc in
    cspc

  op addBuiltIn: CgContext * CSpec -> CSpec
  def addBuiltIn(_ (* ctxt*), cspc) =
%    let cspc = addDefine(cspc,"COPRDCTSELSIZE 20") in
%    let cspc = addDefine(cspc,"FALSE 0") in
%    let cspc = addDefine(cspc,"TRUE 1") in
%    let cspc = addDefine(cspc,
%			 "SetConstructor(_X_,_SELSTR_) "^
%			 "strncpy(_X_.sel,_SELSTR_,COPRDCTSELSIZE)"
%			)
%    in
%    let cspc = addDefine(cspc,
%			 "ConstructorEq(_X_,_SELSTR_) "^
%			 "(strncmp(_X_.sel,_SELSTR_,COPRDCTSELSIZE)==0)"
%			)
%    in
%    let cspc = addDefine(cspc,
%			 "ConstructorArg(_X_,_CONSTR_) "^
%			 "_X_.alt._CONSTR_")
%    in
%    let cspc =
%          %if generateCodeForMotes then
%	  %  addDefine(cspc,"NONEXHAUSTIVEMATCH_ERROR 0")
%	  %else
%	    addDefine(cspc,"NONEXHAUSTIVEMATCH_ERROR "^
%		      "printf(\"Nonexhaustive match failure\\n\")")
%    in
%    let cspc = addInclude(cspc,"stdio.h") in
%    let cspc = addInclude(cspc,"string.h") in
    let cspc = addInclude(cspc,"SWC_Common.h") in
    cspc

  % --------------------------------------------------------------------------------

  op c4TypeDefinition: CgContext * CSpec * I2L.TypeDefinition -> CSpec
  def c4TypeDefinition(ctxt,cspc,(tname,typ)) =
    let tname = qname2id tname in
    let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
    let typedef = (tname,ctype) in
    let cspc = addTypeDefn(cspc,typedef) in
    %let cspc = if typ = Any then cspc else addDefine(cspc,"TypeDef_For_"^tname) in
    cspc

  op c4OpDecl:  CgContext * CSpec * I2L.Declaration -> CSpec
  def c4OpDecl(ctxt,cspc,decl) =
    c4OpDecl_internal(ctxt,cspc,decl,None)

  op c4OpDecl_internal:  CgContext * CSpec * I2L.Declaration * Option(String) -> CSpec
  def c4OpDecl_internal(ctxt,cspc,decl as (opname,typ,optexpr),optinitstr) =
    let vname = qname2id opname in
    let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
    case optexpr of
      | Some expr -> 
        let emptyblock = ([],[]) in
        let (cspc,block,cexpr) = c4InitializerExpression(ctxt,cspc,emptyblock,expr) in
	if (block = emptyblock) & constExpr?(cspc,cexpr) then
	  addVarDefn(cspc,(vname,ctype,cexpr))
	else
	  c4NonConstVarDef(ctxt,vname,ctype,cspc,block,cexpr)
	  %System.fail("code generation cannot handle the kind of definition terms as\n       "
	  %	      ^"the one you specified for op/var \""
	  %	      ^vname^"\".")
      | _ -> (case optinitstr of
		| None -> addVar(cspc,voidToInt(vname,ctype))
		| Some initstr -> addVarDefn(cspc,(vname,ctype,Var(initstr,Void))) % ok,ok, ... 
	     )

  op voidToInt: CVarDecl -> CVarDecl
  def voidToInt(vname,ctype) =
    if ctype = Void then (vname,Int) else (vname,ctype)

  (*
   * for each non-constant variable definition X an function get_X() and a
   * boolean variable _X_initialized is generated 
   *)
  op c4NonConstVarDef: CgContext * Id * CType * CSpec * CBlock * CExp -> CSpec
  def c4NonConstVarDef(ctxt,vname,ctype,cspc,block as (decls,stmts),cexpr) =
    let initfname = "get_"^vname in
    let valuevname = vname^"_value" in
    let cspc = addDefine(cspc,vname^" "^initfname^"()") in
    let cspc = addVarDefn(cspc,(valuevname,ctype,NULL)) in
    let condexp = Binary(Eq,Var(valuevname,ctype),NULL) in
    let setexp = Binary(Set,Var(valuevname,ctype),cexpr) in
    let body = Block(decls,stmts++[IfThen(condexp,Exp(setexp)),Return(Var(valuevname,ctype))]) in
    let fndefn = (initfname,[],ctype,body) in
    let cspc = addFnDefn(cspc,fndefn) in
    let cspc = addFn(cspc,(initfname,[],ctype)) in
    cspc

  op c4FunDecl: CgContext * CSpec * I2L.FunDeclaration -> CSpec
  def c4FunDecl(ctxt,cspc,fdecl) =
    let (cspc,fname,ctypes,rtype) = c4FunDecl_internal(ctxt,cspc,fdecl) in
    addFn(cspc,(fname,ctypes,rtype))

  op c4FunDecl_internal: CgContext * CSpec * I2L.FunDeclaration -> CSpec * String * CTypes * CType
  def c4FunDecl_internal(ctxt,cspc,fdecl) =
    let fname = qname2id(fdecl.name) in
    let paramtypes = List.map (fn(_,t) -> t) (fdecl.params) in
    let (cspc,ctypes) = c4Types(ctxt,cspc,paramtypes) in
    let (cspc,rtype) = c4Type(ctxt,cspc,fdecl.returntype) in
    (cspc,fname,ctypes,rtype)

  op c4FunDefn: CgContext * CSpec * I2L.FunDefinition -> CSpec
  def c4FunDefn(ctxt,cspc,fdefn) =
    let fdecl = fdefn.decl in
    let (cspc,fname,ctypes,rtype) = c4FunDecl_internal(ctxt,cspc,fdecl) in
    let ctxt = setCurrentFunName(ctxt,fname) in
    let body = fdefn.body in
    let parnames = List.map (fn(n,_) -> n) (fdecl.params) in
    let vardecls = zip(parnames,ctypes) in
    case body of
      | Stads stadsbody -> let returnstmt = ReturnVoid in
                           let (cspc,block,stmts) =
                             List.foldl
			     (fn(stadcode,(cspc,block,stmts)) -> 
			      let (cspc,block,stadstmts) = 
			             c4StadCode(ctxt,cspc,block,stadsbody,returnstmt,stadcode) in
			      let stmts = concat(stmts,stadstmts) in
			      (cspc,block,stmts)
			     ) (cspc,([],[]),[]) stadsbody
			   in
			   let stmt = addStmts(Block block,stmts) in
			   let fdefn = (fname,vardecls,rtype,stmt) in
			   addFnDefn(cspc,fdefn)
      | Exp expr ->
	let ctxt = setCurrentFunParams(ctxt,vardecls) in
        let (cspc,block as (decls,stmts),cexpr) = c4Expression(ctxt,cspc,([],[]),expr) in
	let (stmts1,cexpr1) = commaExprToStmts(ctxt,cexpr) in
	let stmts2 = conditionalExprToStmts(ctxt,cexpr1,(fn(e)->Return(e))) in
	%let stmts2 = [Return cexpr1] in
	let block = (decls,stmts++stmts1++stmts2) in
	let block = findBlockForDecls(block) in
	let stmt = Block block in
	let fdefn = (fname,vardecls,rtype,stmt) in
	addFnDefn(cspc,fdefn)

  op c4VarDecl: CgContext * CSpec * I2L.Declaration -> CSpec
  def c4VarDecl(ctxt,cspc,vdecl) =
    % check for records containing functions
    let
      def structCheck(cspc,typ,ids) =
	case typ of
	  | Struct fields -> let (cspc,initstr,initstrIsUseful) =
	                       List.foldl
	                       (fn((id,t),(cspc,initstr,useful)) -> 
				let (cspc,initstr0,useful0) = structCheck(cspc,t,cons(id,ids)) in
				let initstr = if initstr="" then initstr0 else initstr^","^initstr0 in
				(cspc,initstr,useful or useful0)
			       )
	                       (cspc,"",false) fields
			     in
			     (cspc,"{"^initstr^"}",initstrIsUseful)
	  | FunOrMap(types,rtype) ->
			     let fname = List.foldr (fn(id,s) -> if s="" then id else s^"_"^id) "" ids in
			     let (cspc,vardecl) = addMapForMapDecl(ctxt,cspc,fname,types,rtype) in
			     % todo: add a initializer for the field!
			     (addVar(cspc,voidToInt vardecl),"&"^fname,true)
	  | _ -> (cspc,"0",false)
    in
    let (vname,vtype,e) = vdecl in
    let vid = (qname2id vname) in
    let (cspc,initstr,initstrIsUseful) = structCheck(cspc,vtype,[vid]) in
    let optinitstr = if initstrIsUseful then Some initstr else None in
    c4OpDecl_internal(ctxt,cspc,vdecl,optinitstr)

  % --------------------------------------------------------------------------------

  op c4MapDecl: CgContext * CSpec * I2L.FunDeclaration -> CSpec
  def c4MapDecl(ctxt,cspc,mdecl) =
    let fid = (qname2id mdecl.name) in
    let paramtypes = List.map (fn(_,t)->t) mdecl.params in
    let (cspc,vardecl) = addMapForMapDecl(ctxt,cspc,fid,paramtypes,mdecl.returntype) in
    addVar(cspc,voidToInt vardecl)

  % addMapForMapDecl is responsible for creating the arrays and access functions for
  % n-ary vars. The inputs are the name of the var, the argument types and the return type.
  % outputs the updates cspec and a var decl for the array. The var decl is not inserted in the cspec
  % because it may also be used as a field of a record and has to be added there
  op addMapForMapDecl: CgContext * CSpec * String * I2L.Types * I2L.Type -> CSpec * CVarDecl
  def addMapForMapDecl(ctxt,cspc,fid,paramtypes,returntype) =
    let id = getMapName fid in
    let (cspc,paramctypes) = c4Types(ctxt,cspc,paramtypes) in
    case getRestrictedNatList(paramtypes) of
      | Some ns ->
	let nstrs = List.map Nat.toString ns in
	let (cspc,rtype) = c4Type(ctxt,cspc,returntype) in
	let arraytype = List.foldl (fn(nstr,arraytype) ->
				    ArrayWithSize(nstr,arraytype))
	                rtype nstrs
	in
        let vardecl = (id,arraytype) in
	% construct the access function
	let paramnames = List.map getParamName (getNumberListOfSameSize paramtypes) in
	let vardecls = zip (paramnames,paramctypes) in
	let arrayvarexpr = Var(id,Ptr(rtype)) in 
	let arrayrefs = List.foldr (fn(v,e2) -> ArrayRef(e2,Var v)) arrayvarexpr vardecls in
	let stmt = Return arrayrefs in
	let cspc = addFnDefn(cspc,(fid,vardecls,rtype,stmt)) in
	(cspc,vardecl)
      | _ -> System.fail("in this version of the code generator you can use either 0-ary vars\n"^
			 "or 1-ary vars of the form \"var "^id^": {n:Nat|n<C}\", where C must be\n"^
			 "an natural number.")

  op getRestrictedNatList: I2L.Types -> Option(List(Nat))
  def getRestrictedNatList(types) =
    case types of
      | [] -> None
      | _ ->
      let
        def getRestrictedNatList0(types) =
	  case types of
	    | [] -> Some []
	    | (RestrictedNat n)::types ->
	      (case getRestrictedNatList0(types) of
		 | Some ns -> Some (cons(n,ns))
		 | None -> None
		)
	    | _ -> None
      in
      getRestrictedNatList0(types)

  op coproductSelectorStringLength: String
  def coproductSelectorStringLength = "COPRDCTSELSIZE"


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                               TYPES                                 %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op c4Type: CgContext * CSpec * I2L.Type -> CSpec * CType
  def c4Type(ctxt,cspc,typ) =
    let
      def structUnionFields(cspc,fields) =
	case fields of
	  | [] -> (cspc,[])
	  | (fname,itype)::fields -> 
	    let (cspc,ctype) = c4Type(ctxt,cspc,itype) in
	    let ctype = if ctype = Void then Int else ctype in % no void fields allowed
	    let (cspc,sfields) = structUnionFields(cspc,fields) in
	    (cspc,List.cons((fname,ctype),sfields))

      def addFieldNamesToTupleTypes(types) =
	let fieldnames = getFieldNamesForTuple(types) in
	zip(fieldnames,types)

    in
    case c4TypeSpecial(ctxt,cspc,typ) of
      | Some res -> res
      | _ ->
    case typ of
      | Primitive S -> (cspc,c4PrimitiveType(ctxt,S))
      | Base(tname) -> (cspc,Base (qname2id tname))
      | Struct fields -> 
        let (cspc,sfields) = structUnionFields(cspc,fields) in
	let structname = genName(cspc,"Product",length(getStructDefns(cspc))) in
	let (cspc,structtype) = addNewStructDefn(cspc,ctxt.xcspc,(structname,sfields),ctxt.useRefTypes) in
	(cspc,structtype)
      | Tuple types ->
	let fields = addFieldNamesToTupleTypes(types) in
	c4Type(ctxt,cspc,Struct fields)
      | Union fields ->
	let (cspc,ufields) = structUnionFields(cspc,fields) in
	let unionname = genName(cspc,"CoProduct",length(getUnionDefns(cspc))) in
	let structname = genName(cspc,"CoProductS",length(getStructDefns(cspc))) in
	let (cspc,uniontype) = addNewUnionDefn(cspc,ctxt.xcspc,(unionname,ufields)) in
	%let uniontype = Union unionname in
	let sfields = [("sel",ArrayWithSize(coproductSelectorStringLength,Char)),
		       ("alt",uniontype)] in
	let (cspc,structtype) = addNewStructDefn(cspc,ctxt.xcspc,(structname,sfields),ctxt.useRefTypes) in
	(cspc,structtype)
      | Ref rtype ->
	let (cspc,ctype) = c4Type(ctxt,cspc,rtype) in
	(cspc,Ptr(ctype))

%      | FunOrMap([RestrictedNat n],typ) ->
%	let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
%	let nstr = Nat.toString(n) in
%	(cspc,ArrayWithSize(nstr,ctype))

      | FunOrMap(types,rtype) ->
	let (cspc,ctypes) = c4Types(ctxt,cspc,types) in
	let (cspc,ctype) = c4Type(ctxt,cspc,rtype) in
	let tname = genName(cspc,"fn",length(getTypeDefns(cspc))) in
	let (cspc,ctype) = addNewTypeDefn(cspc,ctxt.xcspc,(tname,Fn(ctypes,ctype))) in
	(cspc,ctype)

      %| Any -> (cspc,Ptr(Void))
      | Any -> (cspc,Base "Any")

      | Void -> (cspc,Void)

      | RestrictedNat n -> (cspc,Int)

      | BoundList(ltype,n) -> 
        let (cspc,ctype) = c4Type(ctxt,cspc,ltype) in
	let deflen = length(cspc.defines) in
	let constName = genName(cspc,"MAX",deflen) in
	let cspc = addDefine(cspc,constName^" "^Nat.toString(n)) in
	let arraytype = ArrayWithSize(constName,ctype) in
	let structname = genName(cspc,"BoundList",length(getStructDefns(cspc))) in
	let sfields = [("length",Int),("data",arraytype)] in
	let (cspc,structtype) = addNewStructDefn(cspc,ctxt.xcspc,(structname,sfields),ctxt.useRefTypes) in
	(cspc,structtype)

      | _ -> (System.print(typ);
	      %(cspc,Int)
	      System.fail("sorry, no code generation implemented for that type.")
	     )

  op c4Types: CgContext * CSpec * I2L.Types -> CSpec * CTypes
  def c4Types(ctxt,cspc,types) =
    List.foldl (fn(t,(cspc,ctypes)) ->
		let (cspc,ct) = c4Type(ctxt,cspc,t) in
		(cspc,List.concat(ctypes,[ct])))
    (cspc,[]) types

  op c4PrimitiveType: CgContext * String -> CType
  def c4PrimitiveType(_ (* ctxt *), s) =
    case s of
      | "Nat" -> Int
      | "Int" -> Int
      | "Integer" -> Int
      | "Char" -> Char
      | "String" -> Ptr(Char)
      | "Float" -> Float
      | "Boolean" -> Int
      | _ -> System.fail("no such primitive type: \""^s^"\"")


  % handle special cases of types:

  op c4TypeSpecial: CgContext * CSpec * I2L.Type -> Option(CSpec * CType)
  def c4TypeSpecial(_,cspc,typ) =
    if bitStringSpecial then
      case typ of
	| Base(_,"BitString") -> Some (cspc,UnsignedInt)
	| _ -> None
    else
      None

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                            EXPRESSIONS                              %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op c4Expression1 : CgContext * CSpec * CBlock * I2L.Expression * Boolean * Boolean -> CSpec * CBlock * CExp
  def c4Expression1 (ctxt,cspc,block as (decls,stmts),exp as (expr,typ),islhs,forInitializer) =
    let (cspc,block,cexpr) = c4Expression2(ctxt,cspc,block,exp,islhs,forInitializer) in
    let (cspc,block,cexpr) = mergeBlockIntoExpr(cspc,block,cexpr) in
    (cspc,block,cexpr)

  op c4Expression2 : CgContext * CSpec * CBlock * I2L.Expression * Boolean * Boolean -> CSpec * CBlock * CExp
  def c4Expression2(ctxt,cspc,block as (decls,stmts),exp as (expr,typ),islhs,forInitializer) =
    let
      def addProjections(cexpr,projections) =
	case projections of
	  | [] -> cexpr
	  | p::projections ->
	    let p = getProjectionFieldName p in
	    addProjections(StructRef(cexpr,p),projections)
    in
    let
      def processFunMap f (vname,projections,exprs) =
	let id = qname2id vname in
	let (cspc,block,cexprs) = c4Expressions(ctxt,cspc,block,exprs) in
	let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	let cexpr1 = addProjections(f(Var(id,ctype)),projections) in
	(cspc,block,Apply(cexpr1,cexprs))
    in
    let
      def processMapAccess f (vname,maptype,projections,exprs) =
	let id = qname2id vname in
	%let _ = String.writeLine("maptype for "^id^":") in
	%let _ = System.print(maptype) in
	(case maptype of
	   | FunOrMap(types,_) ->
	     (case getRestrictedNatList(types) of
		| Some ns ->
		  let (cspc,block,cexprs) = c4Expressions(ctxt,cspc,block,exprs) in
		  let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
		  % if we have projections, the map name must be the prefix of the last field name
		  % otherwise of the id itself
		  let (id,projections) =
			 (List.foldl (fn(p,s) -> s^"_"^(getProjectionFieldName p)) (getMapName(id)) projections,[])
		  in
		  let cexpr1 = addProjections(f(Var(id,ctype)),projections) in
		  let arrayrefs = List.foldr (fn(e1,e2) -> ArrayRef(e2,e1)) cexpr1 cexprs in
		  (cspc,block,arrayrefs)
		| _ -> System.fail("unsupported variable format, "^
				   "use 1-ary vars from restricted Nat")
	       )
	   | _ -> System.fail("unsupported variable format, use 1-ary vars from restricted Nat")
	)
    in
    case expr of
      | Str s -> (cspc,block,Const(String(s)))
      | Int n -> (cspc,block,Const(Int(true,n)))
      | Char c -> (cspc,block,Const(Char(c)))
      | Float f -> (cspc,block,Const(Float(f)))
      | Bool b -> (cspc,block,if b then ctrue else cfalse)

      | Builtin bexp -> c4BuiltInExpr(ctxt,cspc,block,bexp)

      | Let (id,typ,idexpr,expr) ->
        let (id,expr) = substVarIfDeclared(ctxt,id,decls,expr) in
        let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	let (cspc,(decls,stmts),idcexpr) = c4Expression(ctxt,cspc,block,idexpr) in
	let letvardecl = (id,ctype) in
	let optinit = None in %if ctxt.useRefTypes then getMallocApply(cspc,ctype) else None in
	let letvardecl1 = (id,ctype,optinit) in
	%let letvardecl1 = (id,ctype,Some idcexpr) in
	let letsetexpr = getSetExpr(ctxt,Var(letvardecl),idcexpr) in
	let block = (List.concat(decls,[letvardecl1]),stmts) in
	let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
	(cspc,block,Comma(letsetexpr,cexpr))

      | FunCall(vname,projections,exprs) ->
	processFunMap (fn(e)->e) (vname,projections,exprs)

      | FunCallDeref(vname,projections,exprs) ->
	processFunMap (fn(e)->Unary(Contents,e)) (vname,projections,exprs)

      | MapAccess(vname,maptype,projections,exprs) ->
	if islhs then
	  processMapAccess (fn(e)->e) (vname,maptype,projections,exprs)
	else
	  processFunMap (fn(e)->e) (vname,projections,exprs)

      | MapAccessDeref(vname,maptype,projections,exprs) ->
	if islhs then 
	  processMapAccess (fn(e)->Unary(Contents,e)) (vname,maptype,projections,exprs)
	else
	  processFunMap (fn(e)->Unary(Contents,e)) (vname,projections,exprs)

      | TupleExpr exprs ->
	let fieldnames = getFieldNamesForTuple(exprs) in
	c4StructExpr(ctxt,cspc,block,typ,exprs,fieldnames,forInitializer)

      | StructExpr fields ->
	let fieldnames = List.map (fn(n,_) -> n) fields in
	let exprs = List.map (fn(_,e) -> e) fields in
	c4StructExpr(ctxt,cspc,block,typ,exprs,fieldnames,forInitializer)

      | Project(expr,id) ->
	let (cspc,block,cexpr) = c4Expression1 (ctxt,cspc,block,expr,islhs,forInitializer) in
	let id = getProjectionFieldName id in
	let cexpr = if ctxt.useRefTypes then Unary(Contents,cexpr) else cexpr in
	(cspc,block,StructRef(cexpr,id))

      | ConstrCall(typename,consid,exprs) ->
	let consfun = getConstructorOpNameFromQName(typename,consid) in
	let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	%let varPrefix = getVarPrefix("_Vc",ctype) in
	%let xname = varPrefix^(Nat.toString(length(decls))) in
	%let decl = (xname,ctype) in
	let (cspc,block as (decls,stmt),constrCallExpr) =
	  let fnid = getConstructorOpNameFromQName(typename,consid) in
	  (case exprs of
	     | [] -> let fndecl = (fnid,[],ctype) in
		     (cspc,block,Apply(Fn(fndecl),[]))
             | _::_ -> let (cspc,ctypes) = foldl (fn((_,ty),(cspc,ctypes)) -> 
						  let (cspc,ctype) = c4Type(ctxt,cspc,ty) in
						  (cspc,concat(ctypes,[ctype]))
						 ) (cspc,[]) exprs in
		       let (cspc,block,cexprs) = c4Expressions(ctxt,cspc,block,exprs) in
		       let fndecl = (fnid,ctypes,ctype) in
		       (cspc,block,Apply(Fn(fndecl),cexprs))
	    )
	in
	%let decl1 = (xname,ctype,optinit) in
	%let decls = concat(decls,[decl1]) in
	%let block = (decls,stmts) in
	%let res = Var decl in
	(cspc,block,constrCallExpr)
	     
      | AssignUnion(selstr,optexpr) ->
	let (cspc,block as (decls,stmts),optcexpr) =
	  (case optexpr of
	     | Some expr -> let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
	                    (cspc,block,Some cexpr)
	     | None -> (cspc,block,None))
	in
	%let _ = (System.print("type: ");System.print(typ);String.writeLine("")) in
	let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	let varPrefix = getVarPrefix("_Vc",ctype) in
	let xname = varPrefix^(Nat.toString(length(decls))) in
	let decl = (xname,ctype) in
	%let optinit = if ctxt.useRefTypes then getMallocApply(cspc,ctype) else None in
	let optinit = getMallocApply(cspc,ctype) in
	let decl1 = (xname,ctype,optinit) in
	let selassign = [getSelAssignStmt(ctxt,selstr,xname,ctype)] in
	let altassign =
	    (case optcexpr of
	       | None -> []
	       | Some cexpr ->
	         %let sref = StructRef(Var(decl),"alt."^selstr) in
	         let sref0 = if ctxt.useRefTypes then Unary(Contents,Var(decl)) else Var(decl) in
	         let sref = StructRef(StructRef(sref0,"alt"),selstr) in
	         [Exp(getSetExpr(ctxt,sref,cexpr))]
	    )
	in
	let block = (concat(decls,[decl1]),concat(stmts,selassign ++ altassign)) in
	let res = Var decl in
	(cspc,block,res)

      | UnionCaseExpr(expr as (_,type0),unioncases) ->
	let (cspc0,block0 as (decls,stmts),cexpr0) = c4Expression(ctxt,cspc,block,expr) in
	% insert a variable for the discriminator in case cexpr0 isn't a variable, 
        % otherwise it can happen that the
	% C Compiler issues an "illegal lvalue" error
	let (block0 as (decls,stmts),disdecl,newdecl?) =
	     case cexpr0 of
	       | Var(decl) -> ((decls,stmts),decl,false)
	       | _ ->
	           let disname = "_dis_"^(Nat.toString(length(decls))) in
		   let (cspc,distype) = c4Type(ctxt,cspc,type0) in
		   let disdecl = (disname,distype) in
		   let disdecl0 = (disname,distype,None) in
		   let block0 = (decls++[disdecl0],stmts) in
		   (block0,disdecl,true)
	in
	% insert a dummy variable of the same type as the expression to be
	% used in the nonexhaustive match case in order to prevent typing 
	% errors of the C compiler
	let (cspc,xtype) = c4Type(ctxt,cspc,typ) in
	let xtype = if xtype = Void then Int else xtype in
	let varPrefix = getVarPrefix("_Vd_",xtype) in
	let xname = varPrefix^(Nat.toString(length(decls))) in
	let xdecl = (xname,xtype,None) in
	let funname4errmsg = case ctxt.currentFunName of Some id -> "(\"function '"^id^"'\")" | _ -> "(\"unknown function\")" in
	let errorCaseExpr = Comma(Var("NONEXHAUSTIVEMATCH_ERROR"^funname4errmsg,Int),Var(xname,xtype)) in
	%let errorCaseExpr = Var(xname,xtype) in
	let block0 = (decls ++ [xdecl], stmts) in
	%let def casecond(str) = getSelCompareExp(ctxt,cexpr0,str) in
	let def casecond(str) = getSelCompareExp(ctxt,Var(disdecl),str) in
	let (cspc,block,ifexpr) =
	List.foldr
	(fn(unioncase,(cspc,block as (decls,stmts),ifexp)) -> 
	 case unioncase of
	   | ConstrCase(optstr,opttype,vlist,expr) ->
	   (case optstr of
	      | None -> c4Expression(ctxt,cspc0,block0,expr)
	      | Some selstr ->
	      let condition = casecond(selstr) in
	      % insert the variables:
	      let (cspc,block,cexpr) =
	      case List.find (fn | None -> false | _ -> true) vlist of
		| None -> 
		let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
		(cspc,block,cexpr) % varlist contains only wildcards
		| _ ->
		let typ = (case opttype of
			      | Some t -> t
			      | None -> System.fail("internal error: type missing in union case"
						    ^ " for constructor \""^selstr^"\"")
			   )
		in
		  (case vlist of
		     | [Some id] -> % contains exactly one var
		     let (id,expr) = substVarIfDeclared(ctxt,id,decls,expr) in
		     let (cspc,idtype) = c4Type(ctxt,cspc,typ) in
		     let structref = if ctxt.useRefTypes then Unary(Contents,cexpr0) else cexpr0 in
		     let valexp = StructRef(StructRef(structref,"alt"),selstr) in
		     let decl = (id,idtype) in
		     let assign = getSetExpr(ctxt,Var(decl),valexp) in
		     % the assignment must be attached to the declaration, otherwise
		     % it may happen that the new variable is accessed in the term without
		     % being initialized
		     %let optinit = if ctxt.useRefTypes then getMallocApply(cspc,idtype) else None in
		     let optinit = None in
		     let decl1 = (id,idtype,optinit) in
		     %let decl1 = (id,idtype,Some valexp) in
		     let (cspc,block as (decls,stmts),cexpr) = c4Expression(ctxt,cspc,block,expr) in
		     %let (cspc,block as (decls,stmts),cexpr) = mergeBlockIntoExpr(cspc,block,cexpr) in
		     (cspc,(decls ++ [decl1],stmts),Comma(assign,cexpr))
		     | _ -> 
		     % the vlist consists of a list of variable names representing the fields
		     % of the record that is the argument of the constructor. We will introduce
		     % a fresh variable of that record type and substitute the variable in the vlist
		     % by corresponding StructRefs into the record.
		     let (cspc,idtype) = c4Type(ctxt,cspc,typ) in
		     let varPrefix = getVarPrefix("_Va",idtype) in
		     let id = varPrefix^(Nat.toString(length(decls))) in
		     let structref = if ctxt.useRefTypes then Unary(Contents,cexpr0) else cexpr0 in
		     let valexp = StructRef(StructRef(structref,"alt"),selstr) in
		     let decl = (id,idtype) in
		     %let optinit = if ctxt.useRefTypes then getMallocApply(cspc,idtype) else None in
		     let optinit = None in
		     let decl1 = (id,idtype,optinit) in
		     %let decl1 = (id,idtype,Some valexp) in
		     let assign = getSetExpr(ctxt,Var(decl),valexp) in
		     let (cspc,block as (decls,stmts),cexpr) = c4Expression(ctxt,cspc,block,expr) in
		     let cexpr = substVarListByFieldRefs(ctxt,vlist,Var(decl),cexpr) in
		     %let (cspc,block as (decls,stmts),cexpr) = mergeBlockIntoExpr(cspc,block,cexpr) in
		     %let decls = substVarListByFieldRefsInDecls(vlist,Var(decl),decls) in
		     (cspc,(decls ++ [decl1],stmts),Comma(assign,cexpr))
		    )
	      in
		(cspc,block,IfExp(condition,cexpr,ifexp))
	       )
	      | NatCase(n,exp) -> 
	        let (cspc,block,ce) = c4Expression(ctxt,cspc,block,exp) in
		let (cspc,block,const) = c4Expression(ctxt,cspc,block,((Int n),Primitive "Int")) in
		let cond = Binary(Eq,Var disdecl,const) in
		let ifexp = IfExp(cond,ce,ifexp) in
		(cspc,block,ifexp)
	      | CharCase(c,exp) ->
	        let (cspc,block,ce) = c4Expression(ctxt,cspc,block,exp) in
		let (cspc,block,const) = c4Expression(ctxt,cspc,block,((Char c),Primitive "Char")) in
		let cond = Binary(Eq,Var disdecl,const) in
		let ifexp = IfExp(cond,ce,ifexp) in
		(cspc,block,ifexp)
	      
	   ) (cspc0,block0,errorCaseExpr) unioncases 
	in
	(cspc,block,
	 if newdecl? then 
	   %% In general, cexpr0 may be too complex to appear in a C struct accessor form
	   %% such as (cexpr0 -> attr), so we need to replace such forms by (var -> attr).
	   %% As long as we're at it, we might just as well replace all the cexpr0 
	   %% occurrances by var, not just those appearing in struct accessors.
	   %% Yell at jlm if this latter assumption is faulty.
	   let var = Var disdecl in
	   let xx = Binary(Set,var,cexpr0) in
	   let newif = mapExp (fn expr -> if expr = cexpr0 then var else expr) ifexpr in
	   Comma(xx,newif)
	 else 
	   ifexpr)

      | IfExpr(e1,e2,e3) ->
	let (cspc,block,ce1) = c4Expression(ctxt,cspc,block,e1) in
	let (cspc,block,ce2) = c4Expression(ctxt,cspc,block,e2) in
	let (cspc,block,ce3) = c4Expression(ctxt,cspc,block,e3) in
	(cspc,block,IfExp(ce1,ce2,ce3))

      | Var id ->
        let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	let vname = qname2id id in
	let varexp = Var(vname,ctype) in
	(cspc,block,varexp)

      | VarDeref id ->
	let (cspc,block,cexp) = c4Expression(ctxt,cspc,block,(Var id,typ)) in
	(cspc,block,Unary(Contents,cexp))

      | VarRef id ->
	let (cspc,block,cexp) = c4Expression(ctxt,cspc,block,(Var id,typ)) in
	(cspc,block,Unary(Address,cexp))

      | Comma(exprs) ->
	(case exprs of
           | expr1::exprs1 ->
	     let (exprs,expr) = getLastElem(exprs) in
	     let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
	     List.foldr
	      (fn(expr1,(cspc,block,cexpr)) ->
	       let (cspc,block,cexpr1) = c4Expression(ctxt,cspc,block,expr1) in
	       (cspc,block,Comma(cexpr1,cexpr))
	      ) (cspc,block,cexpr) exprs
	   | _ -> System.fail("Comma expression with no expressions?!")
	      )

      | _ -> (System.print(expr);System.fail("unimplemented case for expression."))
	%(cspc,block,Const(Int(true,17)))

  % --------------------------------------------------------------------------------
  op c4Expression: CgContext * CSpec * CBlock * I2L.Expression -> CSpec * CBlock * CExp
  def c4Expression(ctxt,cspc,block,exp) =
    case c4SpecialExpr(ctxt,cspc,block,exp) of
      | Some res -> res
      | None -> c4Expression1 (ctxt,cspc,block,exp,false,false)

  op c4LhsExpression: CgContext * CSpec * CBlock * I2L.Expression -> CSpec * CBlock * CExp
  def c4LhsExpression(ctxt,cspc,block,exp) =
    c4Expression1 (ctxt,cspc,block,exp,true,false)

  op c4InitializerExpression: CgContext * CSpec * CBlock * I2L.Expression -> CSpec * CBlock * CExp
  def c4InitializerExpression(ctxt,cspc,block,exp) =
    c4Expression1 (ctxt,cspc,block,exp,false,true)


  % --------------------------------------------------------------------------------

  op c4Expressions: CgContext * CSpec * CBlock * Expressions -> CSpec * CBlock * CExps
  def c4Expressions(ctxt,cspc,block,exprs) =
    List.foldl (fn(expr,(cspc,block,cexprs)) ->
		let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
		(cspc,block,concat(cexprs,[cexpr])))
    (cspc,block,[]) exprs

  op c4InitializerExpressions: CgContext * CSpec * CBlock * Expressions -> CSpec * CBlock * CExps
  def c4InitializerExpressions(ctxt,cspc,block,exprs) =
    List.foldl (fn(expr,(cspc,block,cexprs)) ->
		let (cspc,block,cexpr) = c4InitializerExpression(ctxt,cspc,block,expr) in
		(cspc,block,concat(cexprs,[cexpr])))
    (cspc,block,[]) exprs

  % --------------------------------------------------------------------------------

  op c4StructExpr: CgContext * CSpec * CBlock * I2L.Type * Expressions * List(String) * Boolean -> CSpec * CBlock * CExp
  def c4StructExpr (ctxt,cspc,block,typ,exprs,fieldnames,_(*forInitializer*)) =
    % even inside initialization forms, we may need to allocate struct's
    % if forInitializer then
    %  c4StructExprForInitializer(ctxt,cspc,block,typ,exprs,fieldnames)
    % else
    c4StructExpr2(ctxt,cspc,block,typ,exprs,fieldnames)
      

  op c4StructExpr2: CgContext * CSpec * CBlock * I2L.Type * Expressions * List(String) -> CSpec * CBlock * CExp
  def c4StructExpr2(ctxt,cspc,block,typ,exprs,fieldnames) =
    %let types = List.map (fn(_,t) -> t) exprs in
    let (cspc,block as (decls,stmts),fexprs) = c4Expressions(ctxt,cspc,block,exprs) in
    %let (cspc,ftypes) = c4Types(ctxt,cspc,types) in
    let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
    let varPrefix = getVarPrefix("_Vb",ctype) in
    let xname = varPrefix^(Nat.toString(length(decls))) in
    let ctype = if ctype = Void then Int else ctype in
    let decl = (xname,ctype) in
    let optinit = if ctxt.useRefTypes then getMallocApply(cspc,ctype) else None in
    let decl1 = (xname,ctype,optinit) in
    let assignstmts = List.map 
                       (fn(field,fexpr) ->
			let variable = Var decl in
			let variable = if ctxt.useRefTypes then Unary(Contents,variable) else variable in
			let fieldref = StructRef(variable,field) in
			Exp (getSetExpr(ctxt,fieldref,fexpr))
		       ) (zip(fieldnames,fexprs))
    in
    let block = (List.concat(decls,[decl1]),List.concat(stmts,assignstmts)) in
    let res = Var decl in
    (cspc,block,res)

  op c4StructExprForInitializer: CgContext * CSpec * CBlock * I2L.Type * Expressions * List(String)
                                 -> CSpec * CBlock * CExp
  def c4StructExprForInitializer(ctxt,cspc,block,_,exprs,_)=
    let (cspc,block,cexprs) = c4InitializerExpressions(ctxt,cspc,block,exprs) in
    (cspc,block,Field cexprs)

  % --------------------------------------------------------------------------------

  op c4BuiltInExpr: CgContext * CSpec * CBlock * BuiltinExpression -> CSpec * CBlock * CExp
  def c4BuiltInExpr(ctxt,cspc,block,exp) =
    let def c4e(e) = c4Expression(ctxt,cspc,block,e) in
    let
      def c42e f e1 e2 = 
	let (cspc,block,ce1) = c4Expression(ctxt,cspc,block,e1) in
	let (cspc,block,ce2) = c4Expression(ctxt,cspc,block,e2) in
	(cspc,block,f(ce1,ce2))
    in
    let
      def c41e f e1 =
	let (cspc,block,ce1) = c4Expression(ctxt,cspc,block,e1) in
	(cspc,block,f(ce1))
    in
    let
      def strequal(ce1,ce2) =
	let strcmp = ("strcmp",[Ptr(Char),Ptr(Char)],Int:CType) in
	let strcmpcall = Apply(Fn strcmp,[ce1,ce2]) in
	Binary(Eq,strcmpcall,Const(Int(true,0)))
    in
    let
      def stringToFloat(e) =
	case c4e e of
	  | (cspc,block,Const(String(s))) -> (cspc,block,Const(Float(s)))
	  | _ -> System.fail("expecting string as argument to \"stringToFloat\"")
    in
    case exp of
      | Equals(e1,e2) -> c42e (fn(c1,c2) -> Binary(Eq,c1,c2)) e1 e2
      | StrEquals(e1,e2) -> c42e strequal e1 e2
      | IntPlus(e1,e2) -> c42e (fn(c1,c2) -> Binary(Add,c1,c2)) e1 e2
      | IntMinus(e1,e2) -> c42e (fn(c1,c2) -> Binary(Sub,c1,c2)) e1 e2
      | IntUnaryMinus(e1) -> c41e (fn(c1) -> Unary(Negate,c1)) e1
      | IntMult(e1,e2) -> c42e (fn(c1,c2) -> Binary(Mul,c1,c2)) e1 e2
      | IntDiv(e1,e2) -> c42e (fn(c1,c2) -> Binary(Div,c1,c2)) e1 e2
      | IntRem(e1,e2) -> c42e (fn(c1,c2) -> Binary(Mod,c1,c2)) e1 e2
      | IntLess(e1,e2) -> c42e (fn(c1,c2) -> Binary(Lt,c1,c2)) e1 e2
      | IntGreater(e1,e2) -> c42e (fn(c1,c2) -> Binary(Gt,c1,c2)) e1 e2
      | IntLessOrEqual(e1,e2) -> c42e (fn(c1,c2) -> Binary(Le,c1,c2)) e1 e2
      | IntGreaterOrEqual(e1,e2) -> c42e (fn(c1,c2) -> Binary(Ge,c1,c2)) e1 e2
      | IntToFloat(e1) -> c41e (fn(c1) -> Cast(Float,c1)) e1
      | StringToFloat(e1) -> stringToFloat(e1)
      | FloatPlus(e1,e2) -> c42e (fn(c1,c2) -> Binary(Add,c1,c2)) e1 e2
      | FloatMinus(e1,e2) -> c42e (fn(c1,c2) -> Binary(Sub,c1,c2)) e1 e2
      | FloatUnaryMinus(e1) -> c41e (fn(c1) -> Unary(Negate,c1)) e1
      | FloatMult(e1,e2) -> c42e (fn(c1,c2) -> Binary(Mul,c1,c2)) e1 e2
      | FloatDiv(e1,e2) -> c42e (fn(c1,c2) -> Binary(Div,c1,c2)) e1 e2
      | FloatLess(e1,e2) -> c42e (fn(c1,c2) -> Binary(Lt,c1,c2)) e1 e2
      | FloatGreater(e1,e2) -> c42e (fn(c1,c2) -> Binary(Gt,c1,c2)) e1 e2
      | FloatLessOrEqual(e1,e2) -> c42e (fn(c1,c2) -> Binary(Le,c1,c2)) e1 e2
      | FloatGreaterOrEqual(e1,e2) -> c42e (fn(c1,c2) -> Binary(Ge,c1,c2)) e1 e2
      | FloatToInt(e1) -> c41e (fn(c1) -> Cast(Int,c1)) e1
      | BoolNot(e1) -> c41e (fn(c1) -> Unary(LogNot,c1)) e1
      | BoolAnd(e1,e2) -> c42e (fn(c1,c2) -> Binary(LogAnd,c1,c2)) e1 e2
      | BoolOr(e1,e2) -> c42e (fn(c1,c2) -> Binary(LogOr,c1,c2)) e1 e2
      | BoolImplies(e1,e2) -> c42e (fn(c1,c2) -> IfExp(c1,c2,cfalse)) e1 e2
      | BoolEquiv(e1,e2) -> c42e (fn(c1,c2) -> Binary(Eq,c1,c2)) e1 e2

  op ctrue: CExp
  def ctrue = Var("TRUE",Int)
  op cfalse: CExp
  def cfalse = Var("FALSE",Int)

  % --------------------------------------------------------------------------------

  (**
   * code for handling special case, e.g. the bitstring operators
   *)

  op c4SpecialExpr: CgContext * CSpec * CBlock * I2L.Expression -> Option(CSpec * CBlock * CExp)
  def c4SpecialExpr(ctxt,cspc,block,(exp,_)) =
    let def c4e(e) = c4Expression(ctxt,cspc,block,e) in
    let
      def c42e f e1 e2 = 
	let (cspc,block,ce1) = c4Expression(ctxt,cspc,block,e1) in
	let (cspc,block,ce2) = c4Expression(ctxt,cspc,block,e2) in
	Some (cspc,block,f(ce1,ce2))
      def c41e f e1 =
	let (cspc,block,ce1) = c4Expression(ctxt,cspc,block,e1) in
	Some (cspc,block,f(ce1))
    in
    if ~bitStringSpecial then None
    else 
      case exp of
	| Var(_,"Zero") -> Some(cspc,block,Const(Int(true,0)))
	| Var(_,"One") -> Some(cspc,block,Const(Int(true,1)))
	| FunCall((_,"leftShift"),[],[e1,e2]) -> c42e (fn(c1,c2) -> Binary(ShiftLeft,c1,c2)) e1 e2
	| FunCall((_,"rightShift"),[],[e1,e2]) -> c42e (fn(c1,c2) -> Binary(ShiftRight,c1,c2)) e1 e2
	| FunCall((_,"andBits"),[],[e1,e2]) -> c42e (fn(c1,c2) -> Binary(BitAnd,c1,c2)) e1 e2
	| FunCall((_,"orBits"),[],[e1,e2]) -> c42e (fn(c1,c2) -> Binary(BitOr,c1,c2)) e1 e2
	| FunCall((_,"xorBits"),[],[e1,e2]) -> c42e (fn(c1,c2) -> Binary(BitXor,c1,c2)) e1 e2
	| FunCall((_,"complement"),[],[e]) -> c41e (fn(ce) -> Unary(BitNot,ce)) e
	| FunCall((_,"notZero"),[],[e]) -> Some(c4e e)
	| _ -> None

  % --------------------------------------------------------------------------------

  op constExpr?: CSpec * CExp -> Boolean
  def constExpr?(cspc,expr) =
    case expr of
      | Const _ -> true
      | Unary(_,e1) -> constExpr?(cspc,e1)
      | Binary(_,e1,e2) -> (constExpr?(cspc,e1)) & (constExpr?(cspc,e2))
% this isn't true in C:
%      | Var (vname,vdecl) ->
%        (case List.find (fn(id,_,_)->id=vname) cspc.varDefns of
%	  | Some (_,_,exp) -> constExpr?(cspc,exp)
%	  | _ -> false
%	  )
      | Var("TRUE",Int) -> true
      | Var("FALSE",Int) -> true
      | Field [] -> true
      | Field (e::es) -> (constExpr?(cspc,e)) & (constExpr?(cspc,Field es))
      | _ -> false


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                               STADS                                 %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  op c4StadCode: CgContext * CSpec * CBlock * List(StadCode) * CStmt * StadCode -> CSpec * CBlock * CStmts
  def c4StadCode(ctxt,cspc,block,allstads,returnstmt,stadcode) =
    % decls are empty, so the following 2 lines have no effect:
    let declscspc = generateC4ImpUnit(stadcode.decls,ctxt.xcspc,ctxt.useRefTypes) in
    let cspc = mergeCSpecs([cspc,declscspc]) in
    let (cspc,block,stepstmts) =
       List.foldl
       (fn(stp,(cspc,block,stmts)) ->
	let (cspc,block,stpstmts) = c4StepCode(ctxt,cspc,block,allstads,returnstmt,stp) in
	(cspc,block,concat(stmts,stpstmts))
       ) (cspc,block,[]) stadcode.steps
    in
    let lblstmt = if stadcode.showLabel then [Label stadcode.label] else [] in
    (cspc,block,lblstmt ++ stepstmts ++ [returnstmt])

  op c4StepCode: CgContext * CSpec * CBlock * List(StadCode) * CStmt * StepCode -> CSpec * CBlock * CStmts
  def c4StepCode(ctxt,cspc,block,allstads,returnstmt,(rule,gotolbl)) =
    let gotostmt = if stadIsFinal(allstads,gotolbl) then returnstmt else Goto gotolbl in
    let (cspc,block,rules_stmts) = c4StepRule(ctxt,cspc,block,Some gotostmt,rule) in
    %List.foldl 
    %                               (fn(rule,(cspc,block,rulestmts)) -> 
    %				    let (cspc,block,rule1stmts) = c4StepRule(ctxt,cspc,block,rule) in
    %				    (cspc,block,concat(rulestmts,rule1stmts))
    %				   ) (cspc,block,[]) rules
    %in
    (cspc,block,rules_stmts)

  op c4StepRule:CgContext * CSpec * CBlock * Option(CStmt) * Rule -> CSpec * CBlock * CStmts
  def c4StepRule(ctxt,cspc,block as (decls,stmts),optgotostmt,rule) =
    let gotostmts = case optgotostmt of | Some stmt -> [stmt] | None -> [] in
    case rule of
      | Skip -> (cspc,block,gotostmts)
      | Cond(expr,rule) ->
        let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
	let (cspc,block0,rulestmts) = c4StepRule(ctxt,cspc,([],[]),optgotostmt,rule) in
	(cspc,block,[IfThen(cexpr,addStmts(Block block0,rulestmts))])
      | Update(optexpr1,expr2) ->
	let (cspc,block0 as (decls0,stmts0),cexpr2) = c4Expression(ctxt,cspc,([],[]),expr2) in
	(case optexpr1 of
           | Some expr1 ->
	     let (cspc,block0 as (decls0,stmts0),cexpr1) = c4LhsExpression(ctxt,cspc,block0,expr1) in
	     let stmts = stmts0++[Exp(getSetExpr(ctxt,cexpr1,cexpr2))]++gotostmts in
	     let stmts = if decls0 = [] then stmts else [Block(decls0,stmts)] in
	     (cspc,block,stmts)
	   | None -> 
	     let stmts = stmts0++[Exp cexpr2]++gotostmts in
	     let stmts = if decls0 = [] then stmts else [Block(decls0,stmts)] in
	     (cspc,block,stmts)
	 )
      | UpdateBlock(upddecls,updates) ->
	let (cspc,block,declstmts) =
	    List.foldl
	    (fn(((_,id),typ,optexpr),(cspc,block,updstmts)) ->
	     let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
	     let iddecl = (id,ctype) in
	     let optinit = if ctxt.useRefTypes then getMallocApply(cspc,ctype) else None in
	     let iddecl1 = (id,ctype,optinit) in
	     let (cspc,block as (decls1,stmts1),assignidstmts) = 
	         case optexpr of
	           | None -> (cspc,block,[])
	           | Some expr ->
		     let (cspc,block,cexpr) = c4Expression(ctxt,cspc,block,expr) in
		     (cspc,block,[Exp(getSetExpr(ctxt,Var(iddecl),cexpr))])
	     in
	     let block = (decls1 ++ [iddecl1],stmts1) in
	     (cspc,block,updstmts ++ assignidstmts)
	    ) (cspc,block,[]) upddecls
	in
	let (cspc,block,updatestmts) =
	    List.foldl (fn(update,(cspc,block,updatestmts)) ->
			let (cspc,block,stmts) = c4StepRule(ctxt,cspc,block,None,Update update) in
			(cspc,block,concat(updatestmts,stmts))
		       ) (cspc,block,[]) updates
	in
	(cspc,block,declstmts++updatestmts++gotostmts)
      | _ -> (cspc,block,gotostmts)

  % --------------------------------------------------------------------------------


  op getFieldNamesForTuple: fa(X) List(X) -> List(String)
  def getFieldNamesForTuple(l) =
    let
      def getFieldNamesForTuple0(l,n) =
	case l of
          | [] -> []
          | _::l -> List.cons("field"^Nat.toString(n),
			      getFieldNamesForTuple0(l,n+1))
    in
    getFieldNamesForTuple0(l,0)

  % --------------------------------------------------------------------------------

  % returns the statement for assigning the value for the selector string used in AssignUnion
  % expressions.
  op getSelAssignStmt: CgContext * String * String * CType -> CStmt
  def getSelAssignStmt(ctxt,selstr,varname,vartype) =
    let selstrncpy = Fn("SetConstructor",[Ptr(Char),Ptr(Char)],Void) in
    let variable = Var(varname,vartype) in
    let variable = if ctxt.useRefTypes then Unary(Contents,variable) else variable in
    Exp(Apply(selstrncpy,[variable,Const(String(selstr))]))

  op getSelCompareExp: CgContext * CExp * String -> CExp
  def getSelCompareExp(ctxt,expr,selstr) =
    let strncmp = Fn("strncmp",[Ptr(Char),Ptr(Char),Int],Int) in
    let hasConstructor = Fn("hasConstructor",[Ptr(Void),Ptr(Char)],Int) in
    let expr = if ctxt.useRefTypes then Unary(Contents,expr) else expr in
    case expr of
      | Unary(Contents,expr) -> Apply(hasConstructor,[expr,Const(String(selstr))])
      | _ -> 
        let apply = Apply(strncmp,[StructRef(expr,"sel"),Const(String(selstr)),Var("COPRDCTSELSIZE",Int)]) in
	Binary(Eq,apply,Const(Int(true,0)))

  op getSelCompareExp0: CgContext * CExp * String -> CExp
  def getSelCompareExp0(ctxt,expr,selstr) =
    let strcmp = Fn("strcmp",[Ptr(Char),Ptr(Char)],Int) in
    let expr = if ctxt.useRefTypes then Unary(Contents,expr) else expr in
    let apply = Apply(strcmp,[StructRef(expr,"sel"),Const(String(selstr))]) in
    Binary(Eq,apply,Const(Int(true,0)))

  % --------------------------------------------------------------------------------

  % checks whether id is already declared in var decls; if yes, a new name is generated
  % and id is substituted in expression
  op substVarIfDeclared: CgContext * String * CVarDecls1 * Expression -> String * Expression
  def substVarIfDeclared(ctxt,id,decls,expr) =
    let
      def isDeclared(id) =
	case List.find (fn(vname,_,_) -> vname = id) decls of
	  | Some _ -> true
	  | None ->
	    case List.find (fn(vname,_) -> vname = id) ctxt.currentFunParams of
	      | Some _ -> true
	      | None -> false
    in
    let
      def determineId(id) =
	if isDeclared(id) then determineId(id^"_")
	else id
    in
    let newid = determineId(id) in
    if newid = id then (id,expr)
    else (newid,substVarName(expr,("",id),("",newid)))

  % --------------------------------------------------------------------------------

  op substVarListByFieldRefs: CgContext * List(Option String) * CExp * CExp -> CExp
  def substVarListByFieldRefs(ctxt,vlist,structexpr,expr) =
    let
      def subst(vlist,expr,n) =
	case vlist of
	  | [] -> expr
	  | None::vlist -> subst(vlist,expr,n+1)
	  | (Some v)::vlist ->
	    let field = "field"^(Nat.toString(n)) in
	    let structexpr = if ctxt.useRefTypes then Unary(Contents,structexpr) else structexpr in
	    let expr = substVarInExp(expr,v,StructRef(structexpr,field)) in
	    subst(vlist,expr,n+1)
    in
    subst(vlist,expr,0)

  op substVarListByFieldRefsInDecl: CgContext * List(Option String) * CExp * CVarDecl1 -> CVarDecl1
  def substVarListByFieldRefsInDecl(ctxt,vlist,structexpr,(vname,vtype,optexpr)) =
    case optexpr of
      | Some e -> (vname,vtype,Some (substVarListByFieldRefs(ctxt,vlist,structexpr,e)))
      | None -> (vname,vtype,None)

  op substVarListByFieldRefsInDecls: CgContext * List(Option String) * CExp * CVarDecls1 -> CVarDecls1
  def substVarListByFieldRefsInDecls(ctxt,vlist,structexpr,decls) =
    List.map (fn(decl) -> substVarListByFieldRefsInDecl(ctxt,vlist,structexpr,decl)) decls

  % --------------------------------------------------------------------------------

  op mergeBlockIntoExpr: CSpec * CBlock * CExp -> CSpec * CBlock * CExp
  def mergeBlockIntoExpr(cspc,block as (decls,stmts),cexpr) =
    case stmts of
      | [] -> (cspc,block,cexpr)
      | stmt::stmts ->
        let (cspc,block as (decls,stmts),cexpr) = mergeBlockIntoExpr(cspc,(decls,stmts),cexpr) in
	let (cexpr,stmts) = (case stmt of
                               | Exp(e) -> (Comma(e,cexpr),stmts)
		               | _ -> (cexpr,cons(stmt,stmts))
			    )
	in
	(cspc,(decls,stmts),cexpr)

  % --------------------------------------------------------------------------------

  op commaExprToStmts: CgContext * CExp -> CStmts * CExp
  def commaExprToStmts(_(* ctxt *),exp) =
    let
      def commaExprToStmts0(stmts,exp) =
	case exp of
	  | Binary(Set,e0,Comma(e1,e2)) ->
	                    let (stmts,e1) = commaExprToStmts0(stmts,e1) in
			    let stmts = concat(stmts,[Exp(e1)]) in
			    let (stmts,e2) = commaExprToStmts0(stmts,e2) in
			    commaExprToStmts0(stmts,Binary(Set,e0,e2))
			    
%	  | Comma(Binary(Set,e0,e1),e2) ->
%	                    let (stmts,e1) = commaExprToStmts0(stmts,e1) in
%			    let stmts = concat(stmts,[Exp(Binary(Set,e0,e1)):CStmt]) in
%			    commaExprToStmts0(stmts,e2)
	  | Comma(e1,e2) -> let (stmts,e1) = commaExprToStmts0(stmts,e1) in
			    let stmts = List.concat(stmts,[(Exp e1):CStmt]) in
	                    commaExprToStmts0(stmts,e2)
	  | _ -> (stmts,exp)
    in
    commaExprToStmts0([],exp)

  % --------------------------------------------------------------------------------

  op conditionalExprToStmts: CgContext * CExp * (CExp -> CStmt) -> CStmts
  def conditionalExprToStmts(ctxt,exp,e2sFun) =
    let (stmts,exp) = commaExprToStmts(ctxt,exp) in
    case exp of
      | IfExp(condExp,thenExp,elseExp) ->
        let isReturn = (case e2sFun exp of
			  | Return _ -> true
			  | _ -> false)
	in
        let thenStmts = conditionalExprToStmts(ctxt,thenExp,e2sFun) in
        let elseStmts = conditionalExprToStmts(ctxt,elseExp,e2sFun) in
	if isReturn then
	  let ifStmt = IfThen(condExp,Block([],thenStmts)) in
	  List.concat(stmts,List.cons(ifStmt,elseStmts))
	else
	  let ifStmt = If(condExp,Block([],thenStmts),Block([],elseStmts)) in
	  List.concat(stmts,[ifStmt])
      | _ ->
	let finalStmt = e2sFun(exp) in
	List.concat(stmts,[finalStmt])

  % --------------------------------------------------------------------------------

  % returns the expression for ce1 = ce2
  op getSetExpr: CgContext * CExp * CExp -> CExp
  def getSetExpr(_ (* ctxt *), ce1, ce2) =
    let lhs = ce1 in
    Binary(Set,lhs,ce2)

  % --------------------------------------------------------------------------------

  op genName: CSpec * String * Nat -> String
  def genName(cspc,prefix,suffixn) =
    cString(cspc.name^prefix^(Nat.toString(suffixn)))

  % --------------------------------------------------------------------------------

  op getMapName: String -> String
  def getMapName(f) = "_map_"^f

  op getParamName: Nat -> String
  def getParamName(n) = "index"^(Nat.toString(n))

  op getNumberListOfSameSize: fa(X) List(X) -> List(Nat)
  def getNumberListOfSameSize(l) =
    let
      def getNumberList(l,n) =
	case l of
          | [] -> []
	  | _::l -> cons(n,getNumberList(l,n+1))
    in
    getNumberList(l,0)

  % --------------------------------------------------------------------------------

  op qname2id: String * String -> String
  def qname2id(qualifier,id) =
    let quali = if qualifier = UnQualified or qualifier = "" or qualifier = "#return#" 
		  then "" else qualifier^"_" in
    cString (quali^id)
    %cString(id)

  op getConstructorOpNameFromQName: (String * String) * String -> String
  def getConstructorOpNameFromQName(qname,consid) =
    % the two _'s are important: that how the constructor op names are
    % distinguished from other opnames (hack)
    let sep = "__" in
    let s = qname2id qname in
    s^sep^consid



  op getLastElem: fa(X) List(X) -> List(X) * X
  def getLastElem(l) =
    case l of
      | [e] -> ([],e)
      | e::l -> 
      let (pref,last) = getLastElem(l) in
      (cons(e,pref),last)

  % --------------------------------------------------------------------------------

  op getProjectionFieldName: String -> String
  def getProjectionFieldName(p) =
    let pchars = String.explode(p) in
    if List.all isNum pchars then
      let num = stringToNat(p) in
      "field"^(Nat.toString(num-1))
    else
      p

  op getPredefinedFnDecl: String -> CFnDecl
  def getPredefinedFnDecl(fname) =
    case fname of
      | "swc_malloc" -> ("swc_malloc",[Int:CType],Ptr(Void))
      | "sizeof" -> ("sizeof",[Void],Int:CType)
      | "New" -> ("New",[Void],Ptr(Void)) % this is defined in SWC_common.h
      | _ -> System.fail("no predefined function \""^fname^"\" found.")

  % --------------------------------------------------------------------------------

  % returns the "malloc" expression for the given ctype
  % the op unfolds the type in the spec in order to determine
  % the struct to which it points to
  op getMallocApply: CSpec * CType -> Option CExp
  def getMallocApply(cspc,t) =
    let t0 = unfoldType(cspc,t) in
    case t0 of
      | Ptr(t1) -> let fdecl = getPredefinedFnDecl("New") in
		   let typename = ctypeToString t1 in
		   let exp = Apply(Fn fdecl,[Var(typename,Void)]):CExp in
		   Some exp
      | _ -> %let typename = ctypeToString t0 in
             %let _ = writeLine("***** no malloc for type "^typename) in
	     None     

  % --------------------------------------------------------------------------------

  % generates "meaningful" variable names by checking whether
  % the type is a base type. In that case, the type name is
  % used to generate the variable prefix, otherwise a generic
  % variable prefix is used.
  op getVarPrefix: String * CType -> String
  def getVarPrefix(gen,typ) =
    case typ of
      | Base s -> String.map Char.toLowerCase s
      | _ -> gen
  
}
