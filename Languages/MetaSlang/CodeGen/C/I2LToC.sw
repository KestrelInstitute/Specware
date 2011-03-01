(**
 translation from the Intermediate Imperative Language to C
 *)

I2LToC qualifying spec 
{
  import C
  import I2L
  import CUtils
  import CGenOptions

  % import ESpecsCodeGenerationOptions

  import /Library/Legacy/DataStructures/ListPair

  type CgContext = {
		    xcspc            : CSpec,    % for incrementatl code generation, xcspc holds the existing cspec that is extended
		    useRefTypes      : Bool,
		    currentFunName   : Option String,
		    currentFunParams : CVarDecls
		   }

  op defaultCgContext : CgContext =
   {
    xcspc            = emptyCSpec "",
    useRefTypes      = true,
    currentFunName   = None,
    currentFunParams = []
    }

  op setCurrentFunName (ctxt : CgContext, id : String) : CgContext =
    ctxt << {currentFunName = Some id}

  op setCurrentFunParams (ctxt : CgContext, params : CVarDecls) : CgContext =
    ctxt << {currentFunParams = params}                        

  op generateC4ImpUnit (impunit : IImpUnit, xcspc : CSpec, useRefTypes : Bool) : CSpec =
   %let _ = writeLine(";;   phase 2: generating C...") in
    let ctxt = {xcspc            = xcspc,
                useRefTypes      = useRefTypes,
                currentFunName   = None,
                currentFunParams = []}
    in
    let cspc = emptyCSpec impunit.name in
    let cspc = addBuiltIn (ctxt, cspc) in
    let cspc = foldl (fn (cspc, typedef) -> c4TypeDefinition (ctxt, cspc, typedef)) cspc impunit.decls.typedefs in
    let cspc = foldl (fn (cspc, typedef) -> c4OpDecl         (ctxt, cspc, typedef)) cspc impunit.decls.opdecls  in
    let cspc = foldl (fn (cspc, typedef) -> c4FunDecl        (ctxt, cspc, typedef)) cspc impunit.decls.funDecls in
    let cspc = foldl (fn (cspc, typedef) -> c4FunDefn        (ctxt, cspc, typedef)) cspc impunit.decls.funDefns in
    let cspc = foldl (fn (cspc, typedef) -> c4VarDecl        (ctxt, cspc, typedef)) cspc impunit.decls.varDecls in
    let cspc = foldl (fn (cspc, typedef) -> c4MapDecl        (ctxt, cspc, typedef)) cspc impunit.decls.mapDecls in
    let cspc = postProcessCSpec cspc
    in
    cspc

  op postProcessCSpec (cspc : CSpec) : CSpec =
    let cspc = sortStructUnionTypeDefns cspc in
    let cspc = deleteUnusedTypes cspc in
    cspc

  op addBuiltIn (_ : CgContext, cspc : CSpec) : CSpec =
    %%    let cspc = addDefine(cspc,"COPRDCTSELSIZE 20") in
    %%    let cspc = addDefine(cspc,"FALSE 0") in
    %%    let cspc = addDefine(cspc,"TRUE 1") in
    %%    let cspc = addDefine(cspc,
    %%			 "SetConstructor(_X_,_SELSTR_) "^
    %%			 "strncpy(_X_.sel,_SELSTR_,COPRDCTSELSIZE)"
    %%			)
    %%    in
    %%    let cspc = addDefine(cspc,
    %%			 "ConstructorEq(_X_,_SELSTR_) "^
    %%			 "(strncmp(_X_.sel,_SELSTR_,COPRDCTSELSIZE)==0)"
    %%			)
    %%    in
    %%    let cspc = addDefine(cspc,
    %%			 "ConstructorArg(_X_,_CONSTR_) "^
    %%			 "_X_.alt._CONSTR_")
    %%    in
    %%    let cspc =
    %%          %if generateCodeForMotes then
    %%	  %  addDefine(cspc,"NONEXHAUSTIVEMATCH_ERROR 0")
    %%	  %else
    %%	    addDefine(cspc,"NONEXHAUSTIVEMATCH_ERROR "^
    %%		      "printf(\"Nonexhaustive match failure\\n\")")
    %%    in
    %%    let cspc = addInclude(cspc,"stdio.h") in
    %%    let cspc = addInclude(cspc,"string.h") in
    let cspc = addInclude (cspc, "SWC_Common.h") in
    cspc

  % --------------------------------------------------------------------------------

  op c4TypeDefinition (ctxt : CgContext, cspc : CSpec, (tname,typ) : ITypeDefinition) : CSpec =
    let tname        = qname2id tname            in
    let (cspc,ctype) = c4Type(ctxt,cspc,typ)     in
    let typedef      = (tname,ctype)             in
    let cspc         = addTypeDefn(cspc,typedef) in
   %let cspc = if typ = Any then cspc else addDefine(cspc,"TypeDef_For_"^tname) in
    cspc

  op c4OpDecl (ctxt :  CgContext, cspc : CSpec, decl : IDeclaration) : CSpec =
    c4OpDecl_internal (ctxt, cspc, decl, None)

  op c4OpDecl_internal (ctxt                         : CgContext, 
                        cspc                         : CSpec, 
                        decl as (opname,typ,optexpr) : IDeclaration, 
                        optinitstr                   : Option String) 
    : CSpec =
    let vname        = qname2id opname       in
    let (cspc,ctype) = c4Type(ctxt,cspc,typ) in
    case optexpr of
      | Some expr -> 
        let emptyblock         = ([],[]) in
        let (cspc,block,cexpr) = c4InitializerExpression (ctxt, cspc, emptyblock, expr) in
        if (block = emptyblock) && constExpr?(cspc,cexpr) then
          addVarDefn(cspc, (vname, ctype, cexpr))
        else
          c4NonConstVarDef (ctxt, vname, ctype, cspc, block, cexpr)
          % fail("code generation cannot handle the kind of definition terms as\n       "
          %	 ^"the one you specified for op/var \""
          %	 ^vname^"\".")
      | _ -> 
        case optinitstr of
          | None         -> addVar     (cspc, voidToInt (vname, ctype))
          | Some initstr -> addVarDefn (cspc, (vname, ctype, CVar (initstr, CVoid))) % ok,ok, ... 
            
  op voidToInt ((vname, ctype) : CVarDecl) : CVarDecl =
    (vname, if ctype = CVoid then CInt else ctype)

  (*
   * for each non-constant variable definition X an function get_X() and a
   * boolean variable _X_initialized is generated 
   *)
  op c4NonConstVarDef (ctxt : CgContext, vname : Id, ctype : CType, cspc : CSpec, block as (decls, stmts) : CBlock, cexpr : CExp) 
    : CSpec =
    let initfname  = "get_" ^ vname   in
    let valuevname = vname ^ "_value" in
    let cspc       = addDefine  (cspc, vname ^ " " ^ initfname ^ "()") in
    let cspc       = addVarDefn (cspc, (valuevname, ctype, NULL))      in
    let condexp    = CBinary    (CEq,  CVar(valuevname, ctype), NULL)  in
    let setexp     = CBinary    (CSet, CVar(valuevname, ctype), cexpr) in
    let body       = CBlock     (decls, stmts ++ [CIfThen (condexp, CExp setexp), 
                                                  CReturn (CVar (valuevname, ctype))]) 
    in
    let fndefn     = (initfname, [], ctype, body)             in
    let cspc       = addFnDefn (cspc, fndefn)                 in
    let cspc       = addFn     (cspc, (initfname, [], ctype)) in
    cspc

  op c4FunDecl (ctxt : CgContext, cspc : CSpec, fdecl : IFunDeclaration) : CSpec =
    let (cspc, fname, ctypes, rtype) = c4FunDecl_internal (ctxt, cspc, fdecl) in
    addFn (cspc, (fname, ctypes, rtype))

  op c4FunDecl_internal (ctxt : CgContext, cspc : CSpec, fdecl : IFunDeclaration) 
    : CSpec * String * CTypes * CType =
    let fname          = qname2id fdecl.name                    in
    let paramtypes     = map (fn (_, t) -> t) fdecl.params      in
    let (cspc, ctypes) = c4Types (ctxt, cspc, paramtypes)       in
    let (cspc, rtype)  = c4Type  (ctxt, cspc, fdecl.returntype) in
    (cspc, fname, ctypes, rtype)

  op c4FunDefn (ctxt : CgContext, cspc : CSpec, fdefn : IFunDefinition) : CSpec =
    let fdecl                        = fdefn.decl                             in
    let (cspc, fname, ctypes, rtype) = c4FunDecl_internal (ctxt, cspc, fdecl) in
    let ctxt                         = setCurrentFunName  (ctxt, fname)       in
    let body                         = fdefn.body                             in
    let parnames                     = map (fn (n, _) -> n) fdecl.params      in
    let vardecls                     = zip (parnames, ctypes)                 in
    case body of

      | IStads stadsbody -> 
        let returnstmt           = CReturnVoid in
        let (cspc, block, stmts) = foldl (fn ((cspc, block, stmts), stadcode) -> 
                                            let (cspc, block, stadstmts) = 
                                            c4StadCode (ctxt, cspc, block, stadsbody, returnstmt, stadcode) in
                                            let stmts = stmts++stadstmts in
                                            (cspc, block, stmts))
                                         (cspc, ([], []), []) 
                                         stadsbody
        in
        let stmt  = addStmts (CBlock block, stmts) in
        let fdefn = (fname, vardecls, rtype, stmt) in
        addFnDefn (cspc, fdefn)

      | IExp expr ->
	let ctxt                                   = setCurrentFunParams (ctxt, vardecls)      in
        let (cspc, block as (decls, stmts), cexpr) = c4Expression (ctxt, cspc, ([], []), expr) in
	let (stmts1, cexpr1)                       = commaExprToStmts (ctxt, cexpr)            in
	let stmts2                                 = conditionalExprToStmts (ctxt, cexpr1, (fn e -> CReturn e)) in
	let block                                  = (decls, stmts++stmts1++stmts2)            in
	let block                                  = findBlockForDecls block                   in
	let stmt                                   = CBlock block                              in
	let fdefn                                  = (fname, vardecls, rtype, stmt)            in
	addFnDefn (cspc, fdefn)

  op c4VarDecl (ctxt : CgContext, cspc : CSpec, vdecl : IDeclaration) : CSpec =
    % check for records containing functions
    let
      def structCheck (cspc, typ, ids) =
        case typ of

          | IStruct fields ->
            let (cspc, initstr, initstrIsUseful) =
            foldl (fn ( (cspc, initstr, useful), (id, t)) -> 
                     let (cspc, initstr0, useful0) = structCheck (cspc, t, id::ids) in
                     let initstr = if initstr = "" then initstr0 else initstr ^ ", " ^ initstr0 in
                     (cspc, initstr, useful || useful0))
                  (cspc, "", false) 
                  fields
            in
            (cspc, "{" ^ initstr ^ "}", initstrIsUseful)
           
          | IFunOrMap (types, rtype) ->
            let fname = foldr (fn (id, s) -> if s="" then id else s^"_"^id) "" ids in
            let (cspc, vardecl) = addMapForMapDecl (ctxt, cspc, fname, types, rtype) in
            % todo: add a initializer for the field!
            (addVar (cspc, voidToInt vardecl), "&" ^ fname, true)
            
          | _ -> (cspc, "0", false)
    in
    let (vname, vtype, e)                = vdecl in
    let vid                              = (qname2id vname) in
    let (cspc, initstr, initstrIsUseful) = structCheck (cspc, vtype, [vid]) in
    let optinitstr                       = if initstrIsUseful then Some initstr else None in
    c4OpDecl_internal (ctxt, cspc, vdecl, optinitstr)

  % --------------------------------------------------------------------------------

  op c4MapDecl (ctxt : CgContext, cspc : CSpec, mdecl : IFunDeclaration) : CSpec =
    let fid             = qname2id mdecl.name in
    let paramtypes      = map (fn (_, t)->t) mdecl.params in
    let (cspc, vardecl) = addMapForMapDecl (ctxt, cspc, fid, paramtypes, mdecl.returntype) in
    addVar (cspc, voidToInt vardecl)

  % addMapForMapDecl is responsible for creating the arrays and access functions for
  % n-ary vars. The inputs are the name of the var, the argument types and the return t_ype.
  % outputs the updates cspec and a var decl for the array. The var decl is not inserted in the cspec
  % because it may also be used as a field of a record and has to be added there
  op addMapForMapDecl (ctxt : CgContext, cspc : CSpec, fid : String, paramtypes : ITypes, returntype : IType)
    : CSpec * CVarDecl =
    let id                  = getMapName fid in
    let (cspc, paramctypes) = c4Types (ctxt, cspc, paramtypes) in
    case getRestrictedNatList paramtypes of
      
      | Some ns ->
        let nstrs         = map show ns in
        let (cspc, rtype) = c4Type (ctxt, cspc, returntype) in
        let arraytype     = foldl (fn (arraytype, nstr) -> CArrayWithSize (nstr, arraytype))
                                  rtype 
                                  nstrs
        in
        let vardecl       = (id, arraytype) in
        % construct the access function
        let paramnames    = map getParamName (getNumberListOfSameSize paramtypes) in
        let vardecls      = zip (paramnames, paramctypes) in
        let arrayvarexpr  = CVar (id, CPtr rtype) in 
        let arrayrefs     = foldr (fn (v, e2) -> CArrayRef (e2, CVar v)) arrayvarexpr vardecls in
        let stmt          = CReturn arrayrefs in
        let cspc          = addFnDefn (cspc, (fid, vardecls, rtype, stmt)) in
        (cspc, vardecl)
        
      | _ -> 
        fail ("in this version of the code generator you can use either 0-ary vars\n"^
                "or 1-ary vars of the form \"var "^id^": {n:Nat|n<C}\", where C must be\n"^
                "an natural number.")

  op getRestrictedNatList (types : ITypes) : Option (List Nat) =
    case types of
      | [] -> None
      | _ ->
        let
          def getRestrictedNatList0 types =
            case types of
              | [] -> Some []
              | (IRestrictedNat n)::types ->
                (case getRestrictedNatList0 types of
                   | Some ns -> Some (n::ns)
                   | None -> None)
              | _ -> None
        in
        getRestrictedNatList0 types

  op coproductSelectorStringLength : String = "COPRDCTSELSIZE"


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                               TYPES                                 %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op c4Type (ctxt : CgContext, cspc : CSpec, typ : IType) : CSpec * CType =
    let
      def structUnionFields (cspc, fields) =
        case fields of
          | [] -> (cspc, [])
          | (fname, itype)::fields -> 
            let (cspc, ctype)   = c4Type (ctxt, cspc, itype)            in
            let ctype           = if ctype = CVoid then CInt else ctype in % no void fields allowed
            let (cspc, sfields) = structUnionFields (cspc, fields)      in
            (cspc, Cons ((fname, ctype), sfields))

      def addFieldNamesToTupleTypes (types) =
        let fieldnames = getFieldNamesForTuple types in
        zip (fieldnames, types)

    in
    case c4TypeSpecial (cspc, typ) of
      | Some res -> res
      | _ ->
        case typ of

          | IPrimitive p -> (cspc, c4PrimitiveType p)

          | IBase tname  -> (cspc, CBase (qname2id tname))

          | IStruct fields -> 
            let (cspc, sfields)    = structUnionFields (cspc, fields)                                             in
            let structname         = genName (cspc, "Product", length (getStructDefns cspc))                      in
            let (cspc, structtype) = addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields), ctxt.useRefTypes) in
            (cspc, structtype)
            
          | ITuple types ->
            let fields = addFieldNamesToTupleTypes types in
            c4Type (ctxt, cspc, IStruct fields)
            
          | IUnion fields ->
            let (cspc, ufields)    = structUnionFields (cspc, fields)                                             in
            let unionname          = genName (cspc, "CoProduct",  length (getUnionDefns  cspc))                   in
            let structname         = genName (cspc, "CoProductS", length (getStructDefns cspc))                   in
            let (cspc, uniontype)  = addNewUnionDefn (cspc, ctxt.xcspc, (unionname, ufields))                     in
            let sfields            = [("sel", CArrayWithSize (coproductSelectorStringLength, CChar)), 
                                      ("alt", uniontype)] 
            in
            let (cspc, structtype) = addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields), ctxt.useRefTypes) in
            (cspc, structtype)
            
          | IRef rtype ->
            let (cspc, ctype) = c4Type (ctxt, cspc, rtype) in
            (cspc, CPtr ctype)
           
          | IFunOrMap (types, rtype) ->
            let (cspc, ctypes) = c4Types (ctxt, cspc, types)                                      in
            let (cspc, ctype)  = c4Type  (ctxt, cspc, rtype)                                      in
            let tname          = genName (cspc, "fn", length (getTypeDefns cspc))                 in
            let (cspc, ctype)  = addNewTypeDefn (cspc, ctxt. xcspc, (tname, CFn (ctypes, ctype))) in
            (cspc, ctype)
           
          | IAny -> (cspc, CBase "Any")
           
          | IVoid -> (cspc, CVoid)
            
          | IRestrictedNat n -> (cspc, CInt)
            
          | IBoundList (ltype, n) -> 
            let (cspc, ctype)      = c4Type (ctxt, cspc, ltype)                                                   in
            let deflen             = length cspc.defines                                                          in
            let constName          = genName (cspc, "MAX", deflen)                                                in
            let cspc               = addDefine (cspc, constName ^ " " ^ show n)                                   in
            let arraytype          = CArrayWithSize (constName, ctype)                                            in
            let structname         = genName (cspc, "BoundList", length (getStructDefns cspc))                    in
            let sfields            = [("length", CInt), ("data", arraytype)]                                      in
            let (cspc, structtype) = addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields), ctxt.useRefTypes) in
            (cspc, structtype)
            
          | _ -> 
            (print typ;
             % (cspc, Int)
             fail ("sorry, no code generation implemented for that type."))
            
  op c4Types (ctxt : CgContext, cspc : CSpec, types : ITypes) : CSpec * CTypes =
    foldl (fn ((cspc, ctypes), typ) ->
             let (cspc, ct) = c4Type (ctxt, cspc, typ) in
             (cspc, ctypes ++ [ct]))
          (cspc, []) 
          types

  op c4PrimitiveType (prim : IPrimitive) : CType =
    case prim of
      | IBool   -> CInt
      | INat    -> CInt
      | IInt    -> CInt
      | IChar   -> CChar
      | IString -> CPtr CChar
      | IFloat  -> CFloat

  % handle special cases of types:

  op c4TypeSpecial (cspc : CSpec, typ : IType) : Option (CSpec * CType) =
    if bitStringSpecial then
      case typ of
        | IBase (_, "BitString") -> Some (cspc, CUnsignedInt)
        | _ -> None
    else
      None

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                            EXPRESSIONS                              %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op c4Expression1 (ctxt                    : CgContext, 
                    cspc                    : CSpec, 
                    block as (decls, stmts) : CBlock,  
                    exp   as (expr, typ)    : ITypedExpr,
                    lhs?                    : Bool, 
                    forInitializer?         : Bool)
    : CSpec * CBlock * CExp =
    let (cspc, block, cexpr) = c4Expression2 (ctxt, cspc, block, exp, lhs?, forInitializer?) in
    let (cspc, block, cexpr) = mergeBlockIntoExpr (cspc, block, cexpr)                       in
    (cspc, block, cexpr)

  op c4Expression2 (ctxt                    : CgContext,
                    cspc                    : CSpec,
                    block as (decls, stmts) : CBlock,
                    exp   as (expr, typ)    : ITypedExpr,
                    lhs?                    : Bool,
                    forInitializer?         : Bool)
    : CSpec * CBlock * CExp =
    let
      def addProjections (cexpr, projections) =
        case projections of
          | [] -> cexpr
          | p :: projections ->
            let p = getProjectionFieldName p in
            addProjections (CStructRef (cexpr, p), projections)
    in
    let
      def processFunMap f (vname, projections, exprs) =
        let id                    = qname2id vname                                     in
        let (cspc, block, cexprs) = c4Expressions (ctxt, cspc, block, exprs)           in
        let (cspc, ctype)         = c4Type (ctxt, cspc, typ)                           in
        let cexpr1                = addProjections (f (CVar (id, ctype)), projections) in
        (cspc, block, CApply (cexpr1, cexprs))
    in
    let
      def processMapAccess f (vname, maptype, projections, exprs) =
        let id = qname2id vname in
        case maptype of

          | IFunOrMap (types, _) ->
            (case getRestrictedNatList (types) of

               | Some ns ->
                 let (cspc, block, cexprs) = c4Expressions (ctxt, cspc, block, exprs)      in
                 let (cspc, ctype)         = c4Type (ctxt, cspc, typ)                      in
                 % if we have projections, the map name must be the prefix of the last field name
                 % otherwise of the id itself
                 let id = foldl (fn (s, p) -> s ^ "_" ^ getProjectionFieldName p)
                                (getMapName id) 
                                projections
                 in
                 let projections = []                                                      in
                 let cexpr1      = addProjections (f (CVar (id, ctype)), projections)      in
                 let arrayrefs   = foldr (fn (e1, e2) -> CArrayRef (e2, e1)) cexpr1 cexprs in
                 (cspc, block, arrayrefs)

               | _ -> 
                 fail "unsupported variable format, use 1-ary vars from restricted Nat")
          | _ -> 
            fail "unsupported variable format, use 1-ary vars from restricted Nat"
    in
    case expr of
      | IStr   s -> (cspc, block, CConst (CString s))
      | IInt   n -> (cspc, block, CConst (CInt    (true, n)))
      | IChar  c -> (cspc, block, CConst (CChar   c))
      | IFloat f -> (cspc, block, CConst (CFloat  f))
      | IBool  b -> (cspc, block, if b then ctrue else cfalse)
        
      | IBuiltin bexp -> c4BuiltInExpr (ctxt, cspc, block, bexp)
        
      | ILet (id, typ, idexpr, expr) ->
        let (id, expr)                      = substVarIfDeclared (ctxt, id, decls, expr)    in
        let (cspc, ctype)                   = c4Type (ctxt, cspc, typ)                      in
        let (cspc, (decls, stmts), idcexpr) = c4Expression (ctxt, cspc, block, idexpr)      in
        let letvardecl                      = (id, ctype)                                   in
        let optinit                         = None                                          in % if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None in
        let letvardecl1                     = (id, ctype, optinit)                          in
        let letsetexpr                      = getSetExpr (ctxt, CVar (letvardecl), idcexpr) in
        let block                           = (decls++[letvardecl1], stmts)                 in
        let (cspc, block, cexpr)            = c4Expression (ctxt, cspc, block, expr)        in
        (cspc, block, CComma (letsetexpr, cexpr))
        
      | IFunCall (vname, projections, exprs) ->
        processFunMap (fn e -> e) (vname, projections, exprs)
        
      | IFunCallDeref (vname, projections, exprs) ->
        processFunMap (fn e -> CUnary (CContents, e)) (vname, projections, exprs)
        
      | IMapAccess (vname, maptype, projections, exprs) ->
        if lhs? then
          processMapAccess (fn e -> e) (vname, maptype, projections, exprs)
        else
          processFunMap (fn e -> e) (vname, projections, exprs)
          
      | IMapAccessDeref (vname, maptype, projections, exprs) ->
        if lhs? then 
          processMapAccess (fn e -> CUnary (CContents, e)) (vname, maptype, projections, exprs)
        else
          processFunMap (fn e -> CUnary (CContents, e)) (vname, projections, exprs)
            
      | ITupleExpr exprs ->
        let fieldnames = getFieldNamesForTuple (exprs) in
        c4StructExpr (ctxt, cspc, block, typ, exprs, fieldnames, forInitializer?)

      | IStructExpr fields ->
        let fieldnames = map (fn (n, _) -> n) fields in
        let exprs      = map (fn (_, e) -> e) fields in
        c4StructExpr (ctxt, cspc, block, typ, exprs, fieldnames, forInitializer?)
        
      | IProject (expr, id) ->
        let (cspc, block, cexpr) = c4Expression1 (ctxt, cspc, block, expr, lhs?, forInitializer?) in
        let id                   = getProjectionFieldName id                                      in
        let cexpr                = if ctxt.useRefTypes then CUnary (CContents, cexpr) else cexpr  in
        (cspc, block, CStructRef (cexpr, id))
        
      | IConstrCall (typename, consid, exprs) ->
        let consfun       = getConstructorOpNameFromQName (typename, consid) in
        let (cspc, ctype) = c4Type (ctxt, cspc, typ) in
        let (cspc, block as (decls, stmt), constrCallExpr) =
        let fnid = getConstructorOpNameFromQName (typename, consid) in
        case exprs of
          | [] -> 
            let fndecl = (fnid, [], ctype) in
            (cspc, block, CApply (CFn fndecl, []))
          | _ :: _ -> 
            let (cspc, ctypes) = foldl (fn ((cspc, ctypes), (_, ty)) -> 
                                          let (cspc, ctype) = c4Type (ctxt, cspc, ty) in
                                          (cspc, ctypes++[ctype]))
                                       (cspc, []) 
                                       exprs 
            in
            let (cspc, block, cexprs) = c4Expressions (ctxt, cspc, block, exprs) in
            let fndecl = (fnid, ctypes, ctype) in
            (cspc, block, CApply (CFn fndecl, cexprs))
        in
        (cspc, block, constrCallExpr)
	     
      | IAssignUnion (selstr, optexpr) ->
        let (cspc, block as (decls, stmts), optcexpr) =
            case optexpr of
              | Some expr -> 
                let (cspc, block, cexpr) = c4Expression (ctxt, cspc, block, expr) in
                (cspc, block, Some cexpr)
              | None -> 
                (cspc, block, None)
        in
        let (cspc, ctype) = c4Type (ctxt, cspc, typ)                        in
        let varPrefix     = getVarPrefix ("_Vc", ctype)                     in
        let xname         = varPrefix ^ (show (length decls))               in
        let decl          = (xname, ctype)                                  in
        let optinit       = getMallocApply (cspc, ctype)                    in
        let decl1         = (xname, ctype, optinit)                         in
        let selassign     = [getSelAssignStmt (ctxt, selstr, xname, ctype)] in
        let altassign     = case optcexpr of
                              | None -> []
                              | Some cexpr ->
                                let var   = CVar decl                                                 in
                                let sref0 = if ctxt.useRefTypes then CUnary (CContents, var) else var in
                                let sref  = CStructRef (CStructRef (sref0, "alt"), selstr)            in
                                [CExp (getSetExpr (ctxt, sref, cexpr))]
        in
        let block = (decls ++ [decl1], stmts ++ selassign ++ altassign) in
        let res   = CVar decl in
        (cspc, block, res)
        
      | IUnionCaseExpr (expr as (_, type0), unioncases) ->
        let (cspc0, block0 as (decls, stmts), cexpr0) = c4Expression (ctxt, cspc, block, expr) in
        % insert a variable for the discriminator in case cexpr0 isn't a variable, 
        % otherwise it can happen that the
        % C Compiler issues an "illegal lvalue" error
        let (block0 as (decls, stmts), disdecl, newdecl?) =
            case cexpr0 of
              | CVar decl -> ((decls, stmts), decl, false)
              | _ ->
                let disname         = "_dis_" ^ show (length decls) in
                let (cspc, distype) = c4Type (ctxt, cspc, type0)    in
                let disdecl         = (disname, distype)            in
                let disdecl0        = (disname, distype, None)      in
                let block0          = (decls++[disdecl0], stmts)    in
                (block0, disdecl, true)
        in
        % insert a dummy variable of the same type as the expression to be
        % used in the nonexhaustive match case in order to prevent typing 
        % errors of the C compiler
        let (cspc, xtype)      = c4Type (ctxt, cspc, typ)              in
        let xtype              = if xtype = CVoid then CInt else xtype in
        let varPrefix          = getVarPrefix ("_Vd_", xtype)          in
        let xname              = varPrefix ^ show (length decls)       in
        let xdecl              = (xname, xtype, None)                  in
        let funname4errmsg     = case ctxt.currentFunName of 
                                   | Some id -> " (\"function '"^id^"'\")" 
                                   | _ -> " (\"unknown function\")"         
        in
        let errorCaseExpr      = CComma (CVar ("NONEXHAUSTIVEMATCH_ERROR"^funname4errmsg, CInt), 
                                         CVar (xname, xtype)) 
        in
        let block0             = (decls ++ [xdecl], stmts)             in
        let 
          def casecond str = 
            getSelCompareExp (ctxt, CVar disdecl, str) 
        in
        let (cspc, block, ifexpr) =
            foldr (fn (unioncase, (cspc, block as (decls, stmts), ifexp)) -> 
                     case unioncase of
                       
                       | IConstrCase (optstr, opttype, vlist, expr) ->
                         (case optstr of
                            
                            | None -> c4Expression (ctxt, cspc0, block0, expr)
                              
                            | Some selstr ->
                              let condition = casecond (selstr) in
                              % insert the variables:
                              let (cspc, block, cexpr) =
                                  case findLeftmost (fn | None -> false | _ -> true) vlist of
                                
                                    | None -> 
                                      let (cspc, block, cexpr) = c4Expression (ctxt, cspc, block, expr) in
                                      (cspc, block, cexpr) % varlist contains only wildcards
                                      
                                    | _ ->
                                      let typ = 
                                      case opttype of
                                        | Some t -> t
                                        | None -> 
                                          fail ("internal error: type missing in union case for constructor \""^selstr^"\"")
                                      in
                                      case vlist of
                                        
                                        | [Some id] -> % contains exactly one var
                                          let (id, expr)     = substVarIfDeclared (ctxt, id, decls, expr)                      in
                                          let (cspc, idtype) = c4Type (ctxt, cspc, typ)                                        in
                                          let structref      = if ctxt.useRefTypes then CUnary (CContents, cexpr0) else cexpr0 in
                                          let valexp         = CStructRef (CStructRef (structref, "alt"), selstr)              in
                                          let decl           = (id, idtype)                                                    in
                                          let assign         = getSetExpr (ctxt, CVar decl, valexp)                            in
                                          % the assignment must be attached to the declaration, otherwise
                                          % it may happen that the new variable is accessed in the term without
                                          % being initialized
                                          let optinit        = None                                                            in
                                          let decl1          = (id, idtype, optinit)                                           in
                                          let (cspc, block as (decls, stmts), cexpr) = c4Expression (ctxt, cspc, block, expr)  in
                                          (cspc, (decls ++ [decl1], stmts), CComma (assign, cexpr))
                                          
                                        | _ -> 
                                          % the vlist consists of a list of variable names representing the fields
                                          % of the record that is the argument of the constructor. We will introduce
                                          % a fresh variable of that record type and substitute the variable in the vlist
                                          % by corresponding StructRefs into the record.
                                          let (cspc, idtype) = c4Type (ctxt, cspc, typ)                                        in
                                          let varPrefix      = getVarPrefix ("_Va", idtype)                                    in
                                          let id             = varPrefix^ (show (length decls))                                in
                                          let structref      = if ctxt.useRefTypes then CUnary (CContents, cexpr0) else cexpr0 in
                                          let valexp         = CStructRef (CStructRef (structref, "alt"), selstr)              in
                                          let decl           = (id, idtype)                                                    in
                                          let optinit        = None                                                            in
                                          let decl1          = (id, idtype, optinit)                                           in
                                          let assign         = getSetExpr (ctxt, CVar decl, valexp)                            in
                                          let (cspc, block as (decls, stmts), cexpr) = c4Expression (ctxt, cspc, block, expr)  in
                                          let cexpr          = substVarListByFieldRefs (ctxt, vlist, CVar decl, cexpr)         in
                                          (cspc, (decls ++ [decl1], stmts), CComma (assign, cexpr))
                              in
                              (cspc, block, CIfExp (condition, cexpr, ifexp)))

                       | INatCase (n, exp) -> 
                         let (cspc, block, ce)    = c4Expression (ctxt, cspc, block, exp)                       in
                         let (cspc, block, const) = c4Expression (ctxt, cspc, block, (IInt n, IPrimitive IInt)) in
                         let cond                 = CBinary (CEq, CVar disdecl, const)                          in
                         let ifexp                = CIfExp  (cond, ce, ifexp)                                   in
                         (cspc, block, ifexp)

                       | ICharCase (c, exp) ->
                         let (cspc, block, ce)    = c4Expression (ctxt, cspc, block, exp)                         in
                         let (cspc, block, const) = c4Expression (ctxt, cspc, block, (IChar c, IPrimitive IChar)) in
                         let cond                 = CBinary (CEq, CVar disdecl, const)                            in
                         let ifexp                = CIfExp  (cond, ce, ifexp)                                     in
                         (cspc, block, ifexp))
                  (cspc0, block0, errorCaseExpr) 
                  unioncases 
 	 in
         (cspc, 
          block, 
          if newdecl? then 
            %% In general, cexpr0 may be too complex to appear in a C struct accessor form
            %% such as (cexpr0 -> attr), so we need to replace such forms by (var -> attr).
            %% As long as we're at it, we might just as well replace all the cexpr0 
            %% occurrances by var, not just those appearing in struct accessors.
            %% Yell at jlm if this latter assumption is faulty.
            let var   = CVar disdecl                                                   in
            let xx    = CBinary (CSet, var, cexpr0)                                    in
            let newif = mapExp (fn expr -> if expr = cexpr0 then var else expr) ifexpr in
            CComma (xx, newif)
          else 
            ifexpr)

      | IIfExpr (e1, e2, e3) ->
        let (cspc, block, ce1) = c4Expression (ctxt, cspc, block, e1) in
        let (cspc, block, ce2) = c4Expression (ctxt, cspc, block, e2) in
        let (cspc, block, ce3) = c4Expression (ctxt, cspc, block, e3) in
        (cspc, block, CIfExp (ce1, ce2, ce3))
        
      | IVar id ->
        let (cspc, ctype) = c4Type (ctxt, cspc, typ) in
        let vname         = qname2id id              in
        let varexp        = CVar (vname, ctype)      in
        (cspc, block, varexp)
        
      | IVarDeref id ->
        let (cspc, block, cexp) = c4Expression (ctxt, cspc, block, (IVar id, typ)) in
        (cspc, block, CUnary (CContents, cexp))
        
      | IVarRef id ->
        let (cspc, block, cexp) = c4Expression (ctxt, cspc, block, (IVar id, typ)) in
        (cspc, block, CUnary (CAddress, cexp))
        
      | IComma (exprs) ->
        (case exprs of

           | expr1::exprs1 ->
             let (exprs, expr)        = getLastElem (exprs) in
             let (cspc, block, cexpr) = c4Expression (ctxt, cspc, block, expr) in
             foldr (fn (expr1, (cspc, block, cexpr)) ->
                      let (cspc, block, cexpr1) = c4Expression (ctxt, cspc, block, expr1) in
                      (cspc, block, CComma (cexpr1, cexpr)))
                   (cspc, block, cexpr) 
                   exprs

           | _ -> fail "Comma expression with no expressions?!")

      | _ -> 
        (print expr;
         fail  "unimplemented case for expression.")

  % --------------------------------------------------------------------------------

  op c4LhsExpression         (ctxt : CgContext, cspc : CSpec, block : CBlock, exp : ITypedExpr) : CSpec * CBlock * CExp =
    c4Expression1 (ctxt, cspc, block, exp, true, false)

  op c4InitializerExpression (ctxt : CgContext, cspc : CSpec, block : CBlock, exp : ITypedExpr) : CSpec * CBlock * CExp =
    c4Expression1 (ctxt, cspc, block, exp, false, true)

  op c4Expression            (ctxt : CgContext, cspc : CSpec, block : CBlock, exp : ITypedExpr) : CSpec * CBlock * CExp =
    case c4SpecialExpr (ctxt, cspc, block, exp) of
      | Some res -> res
      | None -> c4Expression1 (ctxt, cspc, block, exp, false, false)

  % --------------------------------------------------------------------------------

  op c4Expressions (ctxt : CgContext, cspc : CSpec, block : CBlock, exprs : ITypedExprs) : CSpec * CBlock * CExps =
    foldl (fn ((cspc, block, cexprs), expr) ->
             let (cspc, block, cexpr) = c4Expression (ctxt, cspc, block, expr) in
             (cspc, block, cexprs++[cexpr]))
          (cspc, block, []) 
          exprs

  op c4InitializerExpressions (ctxt : CgContext, cspc : CSpec, block : CBlock, exprs : ITypedExprs) : CSpec * CBlock * CExps =
    foldl (fn ((cspc, block, cexprs), expr) ->
             let (cspc, block, cexpr) = c4InitializerExpression (ctxt, cspc, block, expr) in
             (cspc, block, cexprs++[cexpr]))
          (cspc, block, []) 
          exprs

  % --------------------------------------------------------------------------------

  op c4StructExpr (ctxt : CgContext, cspc : CSpec, block : CBlock, typ : IType, exprs : ITypedExprs, fieldnames : List String, _ : Bool)
    : CSpec * CBlock * CExp =
    % even inside initialization forms, we may need to allocate struct's
    % if forInitializer? then
    %  c4StructExprForInitializer (ctxt, cspc, block, typ, exprs, fieldnames)
    % else
    c4StructExpr2 (ctxt, cspc, block, typ, exprs, fieldnames)
      

  op c4StructExpr2 (ctxt : CgContext, cspc : CSpec, block : CBlock, typ : IType, exprs : ITypedExprs, fieldnames : List String)
    : CSpec * CBlock * CExp =
    let (cspc, block as (decls, stmts), fexprs) = c4Expressions (ctxt, cspc, block, exprs)                        in
    let (cspc, ctype)                           = c4Type (ctxt, cspc, typ)                                        in
    let varPrefix                               = getVarPrefix ("_Vb", ctype)                                     in
    let xname                                   = varPrefix^ (show (length decls))                                in
    let ctype                                   = if ctype = CVoid then CInt else ctype                           in
    let decl                                    = (xname, ctype)                                                  in
    let optinit                                 = if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None in
    let decl1                                   = (xname, ctype, optinit)                                         in
    let assignstmts = map (fn (field, fexpr) ->
                             let variable = CVar decl in
                             let variable = if ctxt.useRefTypes then CUnary (CContents, variable) else variable in
                             let fieldref = CStructRef (variable, field) in
                             CExp (getSetExpr (ctxt, fieldref, fexpr)))
                          (zip (fieldnames, fexprs))
    in
    let block       = (decls++[decl1], stmts++assignstmts) in
    let res         = CVar decl                            in
    (cspc, block, res)

  op c4StructExprForInitializer (ctxt : CgContext, cspc : CSpec, block : CBlock, _ : IType, exprs : ITypedExprs, _ : List String)
    : CSpec * CBlock * CExp =
    let (cspc, block, cexprs) = c4InitializerExpressions (ctxt, cspc, block, exprs) in
    (cspc, block, CField cexprs)

  % --------------------------------------------------------------------------------

  op c4BuiltInExpr (ctxt : CgContext, cspc : CSpec, block : CBlock, exp : IBuiltinExpression) : CSpec * CBlock * CExp =
    let 
      def c4e e = c4Expression (ctxt, cspc, block, e) 
    in
    let
      def c42e f e1 e2 = 
	let (cspc, block, ce1) = c4Expression (ctxt, cspc, block, e1) in
	let (cspc, block, ce2) = c4Expression (ctxt, cspc, block, e2) in
        (cspc, block, f (ce1, ce2))
    in
    let
      def c41e f e1 =
	let (cspc, block, ce1) = c4Expression (ctxt, cspc, block, e1) in
        (cspc, block, f (ce1))
    in
    let
      def strequal (ce1, ce2) =
	let strcmp     = ("strcmp", [CPtr CChar, CPtr CChar], CInt:CType) in
	let strcmpcall = CApply (CFn strcmp, [ce1, ce2])                  in
	CBinary (CEq, strcmpcall, CConst (CInt (true, 0)))
    in
    let
      def stringToFloat e =
	case c4e e of
	  | (cspc, block, CConst (CString s)) -> (cspc, block, CConst (CFloat s))
	  | _ -> fail "expecting string as argument to \"stringToFloat\""
    in
    case exp of
      | IEquals              (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CEq, c1, c2))     e1 e2
      | IStrEquals           (e1, e2) -> c42e strequal e1 e2
      | IIntPlus             (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CAdd, c1, c2))    e1 e2
      | IIntMinus            (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CSub, c1, c2))    e1 e2
      | IIntUnaryMinus       (e1)     -> c41e (fn (c1)     -> CUnary  (CNegate, c1))     e1
      | IIntMult             (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CMul, c1, c2))    e1 e2
      | IIntDiv              (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CDiv, c1, c2))    e1 e2
      | IIntRem              (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CMod, c1, c2))    e1 e2
      | IIntLess             (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLt, c1, c2))     e1 e2
      | IIntGreater          (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CGt, c1, c2))     e1 e2
      | IIntLessOrEqual      (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLe, c1, c2))     e1 e2
      | IIntGreaterOrEqual   (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CGe, c1, c2))     e1 e2
      | IIntToFloat          (e1)     -> c41e (fn (c1)     -> CCast   (CFloat, c1))      e1
      | IStringToFloat       (e1)     -> stringToFloat e1
      | IFloatPlus           (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CAdd, c1, c2))    e1 e2
      | IFloatMinus          (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CSub, c1, c2))    e1 e2
      | IFloatUnaryMinus     (e1)     -> c41e (fn (c1)     -> CUnary  (CNegate, c1))     e1
      | IFloatMult           (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CMul, c1, c2))    e1 e2
      | IFloatDiv            (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CDiv, c1, c2))    e1 e2
      | IFloatLess           (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLt, c1, c2))     e1 e2
      | IFloatGreater        (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CGt, c1, c2))     e1 e2
      | IFloatLessOrEqual    (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLe, c1, c2))     e1 e2
      | IFloatGreaterOrEqual (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CGe, c1, c2))     e1 e2
      | IFloatToInt          (e1)     -> c41e (fn (c1)     -> CCast   (CInt, c1))        e1
      | IBoolNot             (e1)     -> c41e (fn (c1)     -> CUnary  (CLogNot, c1))     e1
      | IBoolAnd             (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLogAnd, c1, c2)) e1 e2
      | IBoolOr              (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CLogOr, c1, c2))  e1 e2
      | IBoolImplies         (e1, e2) -> c42e (fn (c1, c2) -> CIfExp  (c1, c2, cfalse))  e1 e2
      | IBoolEquiv           (e1, e2) -> c42e (fn (c1, c2) -> CBinary (CEq, c1, c2))     e1 e2

  op ctrue  : CExp = CVar ("TRUE",  CInt)
  op cfalse : CExp = CVar ("FALSE", CInt)

  % --------------------------------------------------------------------------------

  (**
   * code for handling special case, e.g. the bitstring operators
   *)

  op c4SpecialExpr (ctxt : CgContext, cspc : CSpec, block : CBlock, (exp, _) : ITypedExpr) 
    : Option (CSpec * CBlock * CExp) =
    let 
      def c4e e = 
        c4Expression (ctxt, cspc, block, e) 

      def c42e f e1 e2 = 
	let (cspc, block, ce1) = c4Expression (ctxt, cspc, block, e1) in
	let (cspc, block, ce2) = c4Expression (ctxt, cspc, block, e2) in
	Some (cspc, block, f (ce1, ce2))

      def c41e f e1 =
	let (cspc, block, ce1) = c4Expression (ctxt, cspc, block, e1) in
	Some (cspc, block, f (ce1))
    in
    if ~bitStringSpecial then 
      None
    else 
      case exp of
	| IVar     (_, "Zero")                       -> Some (cspc, block, CConst (CInt (true, 0)))
	| IVar     (_, "One")                        -> Some (cspc, block, CConst (CInt (true, 1)))
	| IFunCall ((_, "leftShift"),  [], [e1, e2]) -> c42e (fn (c1, c2) -> CBinary (CShiftLeft,  c1, c2)) e1 e2
	| IFunCall ((_, "rightShift"), [], [e1, e2]) -> c42e (fn (c1, c2) -> CBinary (CShiftRight, c1, c2)) e1 e2
	| IFunCall ((_, "andBits"),    [], [e1, e2]) -> c42e (fn (c1, c2) -> CBinary (CBitAnd,     c1, c2)) e1 e2
	| IFunCall ((_, "orBits"),     [], [e1, e2]) -> c42e (fn (c1, c2) -> CBinary (CBitOr,      c1, c2)) e1 e2
	| IFunCall ((_, "xorBits"),    [], [e1, e2]) -> c42e (fn (c1, c2) -> CBinary (CBitXor,     c1, c2)) e1 e2
	| IFunCall ((_, "complement"), [], [e])      -> c41e (fn ce -> CUnary (CBitNot, ce)) e
	| IFunCall ((_, "notZero"),    [], [e])      -> Some (c4e e)
	| _ -> None

  % --------------------------------------------------------------------------------

  op constExpr? (cspc : CSpec, expr : CExp) : Bool =
    case expr of
      | CConst  _               -> true
      | CUnary  (_, e1)         -> constExpr? (cspc, e1)
      | CBinary (_, e1, e2)     -> (constExpr? (cspc, e1)) && (constExpr? (cspc, e2))
        % this isn't true in C:
        % | CVar (vname, vdecl) ->
        %   (case findLeftmost (fn (id, _, _)->id=vname) cspc.varDefns of
        % | Some (_, _, exp) -> constExpr? (cspc, exp)
        % | _ -> false)
      | CVar    ("TRUE",  CInt) -> true
      | CVar    ("FALSE", CInt) -> true
      | CField  []              -> true
      | CField  (e::es)         -> (constExpr? (cspc, e)) && (constExpr? (cspc, CField es))
      | _ -> false


  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %                                                                     %
  %                               STADS                                 %
  %                                                                     %
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  op c4StadCode (ctxt       : CgContext, 
                 cspc       : CSpec,
                 block      : CBlock, 
                 allstads   : List IStadCode, 
                 returnstmt : CStmt,
                 stadcode   : IStadCode) 
    : CSpec * CBlock * CStmts =
    % decls are empty, so the following 2 lines have no effect:
    let declscspc = generateC4ImpUnit (stadcode.decls, ctxt.xcspc, ctxt.useRefTypes) in
    let cspc      = mergeCSpecs [cspc, declscspc] in
    let (cspc, block, stepstmts) =
        foldl (fn ((cspc, block, stmts), stp) ->
                 let (cspc, block, stpstmts) = c4StepCode (ctxt, cspc, block, allstads, returnstmt, stp) in
                 (cspc, block, stmts++stpstmts))
              (cspc, block, []) 
              stadcode.steps
    in
    let lblstmt = if stadcode.showLabel? then [CLabel stadcode.label] else [] in
    (cspc, block, lblstmt ++ stepstmts ++ [returnstmt])

  op c4StepCode (ctxt            : CgContext, 
                 cspc            : CSpec,
                 block           : CBlock,
                 allstads        : List IStadCode, 
                 returnstmt      : CStmt, 
                 (rule, gotolbl) : IStepCode) 
    : CSpec * CBlock * CStmts =
    let gotostmt                   = if final? (allstads, gotolbl) then returnstmt else CGoto gotolbl in
    let (cspc, block, rules_stmts) = c4StepRule (ctxt, cspc, block, Some gotostmt, rule)              in
    %foldl (fn ((cspc, block, rulestmts), rule) -> 
    %	     let (cspc, block, rule1stmts) = c4StepRule (ctxt, cspc, block, rule) in
    %        (cspc, block, rulestmts++rule1stmts))
    %	   (cspc, block, [])
    %      rules
    %in
    (cspc, block, rules_stmts)

  op c4StepRule (ctxt                    : CgContext,
                 cspc                    : CSpec,
                 block as (decls, stmts) : CBlock,
                 optgotostmt             : Option CStmt,
                 rule                    : IRule)
    : CSpec * CBlock * CStmts =
    let gotostmts = case optgotostmt of | Some stmt -> [stmt] | None -> [] in
    case rule of

      | ISkip -> 
        (cspc, block, gotostmts)

      | ICond (expr, rule) ->
        let (cspc, block,  cexpr)     = c4Expression (ctxt, cspc, block, expr)                 in
	let (cspc, block0, rulestmts) = c4StepRule   (ctxt, cspc, ([], []), optgotostmt, rule) in
        (cspc, block, [CIfThen (cexpr, addStmts (CBlock block0, rulestmts))])

      | IUpdate (optexpr1, expr2) ->
	let (cspc, block0 as (decls0, stmts0), cexpr2) = c4Expression (ctxt, cspc, ([], []), expr2) in
        (case optexpr1 of

           | Some expr1 ->
	     let (cspc, block0 as (decls0, stmts0), cexpr1) = c4LhsExpression (ctxt, cspc, block0, expr1) in
	     let stmts = stmts0++[CExp (getSetExpr (ctxt, cexpr1, cexpr2))]++gotostmts                    in
	     let stmts = if decls0 = [] then stmts else [CBlock (decls0, stmts)]                          in
	     (cspc, block, stmts)

	   | None -> 
	     let stmts = stmts0 ++ [CExp cexpr2] ++ gotostmts                    in
	     let stmts = if decls0 = [] then stmts else [CBlock (decls0, stmts)] in
	     (cspc, block, stmts))

      | IUpdateBlock (upddecls, updates) ->
	let (cspc, block, declstmts) =
	    foldl (fn ((cspc, block, updstmts), ((_, id), typ, optexpr)) ->
                     let (cspc, ctype) = c4Type (ctxt, cspc, typ)                                        in
                     let iddecl        = (id, ctype)                                                     in
                     let optinit       = if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None in
                     let iddecl1       = (id, ctype, optinit)                                            in
                     let (cspc, block as (decls1, stmts1), assignidstmts) = 
                     case optexpr of

                       | None -> 
                         (cspc, block, [])

                       | Some expr ->
                         let (cspc, block, cexpr) = c4Expression (ctxt, cspc, block, expr) in
                         (cspc, block, [CExp (getSetExpr (ctxt, CVar iddecl, cexpr))])

                     in
                     let block = (decls1 ++ [iddecl1], stmts1) in
                     (cspc, block, updstmts ++ assignidstmts))
                  (cspc, block, []) 
                  upddecls
	in
	let (cspc, block, updatestmts) =
	    foldl (fn ((cspc, block, updatestmts), update) ->
                     let (cspc, block, stmts) = c4StepRule (ctxt, cspc, block, None, IUpdate update) in
                     (cspc, block, updatestmts++stmts))
                  (cspc, block, []) 
                  updates
	in
        (cspc, block, declstmts ++ updatestmts ++ gotostmts)

      | _ -> 
        (cspc, block, gotostmts)

  % --------------------------------------------------------------------------------


  op [X] getFieldNamesForTuple (l : List X) : List String =
    let
      def getFieldNamesForTuple0 (l, n) =
	case l of
          | []   -> []
          | _::l -> ("field" ^ show n) :: getFieldNamesForTuple0 (l, n+1)
    in
    getFieldNamesForTuple0 (l, 0)

  % --------------------------------------------------------------------------------

  % returns the statement for assigning the value for the selector string used in AssignUnion
  % expressions.
  op getSelAssignStmt (ctxt : CgContext, selstr : String, varname : String, vartype : CType) 
    : CStmt =
    let selstrncpy = CFn ("SetConstructor", [CPtr CChar, CPtr CChar], CVoid)             in
    let variable   = CVar (varname, vartype)                                             in
    let variable   = if ctxt.useRefTypes then CUnary (CContents, variable) else variable in
    CExp (CApply (selstrncpy, [variable, CConst (CString selstr)]))

  op getSelCompareExp (ctxt : CgContext, expr : CExp, selstr : String) : CExp =
    let strncmp        = CFn ("strncmp",        [CPtr CChar, CPtr CChar, CInt], CInt) in
    let hasConstructor = CFn ("hasConstructor", [CPtr CVoid, CPtr CChar],       CInt) in
    let expr = if ctxt.useRefTypes then CUnary (CContents, expr) else expr in
    case expr of

      | CUnary (Contents, expr) -> 
        CApply (hasConstructor, [expr, CConst (CString selstr)])

      | _ -> 
        let apply = CApply (strncmp, [CStructRef (expr, "sel"), 
                                      CConst (CString selstr), 
                                      CVar ("COPRDCTSELSIZE", CInt)])
        in
	CBinary (CEq, apply, CConst (CInt (true, 0)))

  op getSelCompareExp0 (ctxt : CgContext, expr : CExp, selstr : String) : CExp =
    let strcmp = CFn ("strcmp", [CPtr CChar, CPtr CChar], CInt)                       in
    let expr   = if ctxt.useRefTypes then CUnary (CContents, expr) else expr          in
    let apply  = CApply (strcmp, [CStructRef (expr, "sel"), CConst (CString selstr)]) in
    CBinary (CEq, apply, CConst (CInt (true, 0)))

  % --------------------------------------------------------------------------------

  % checks whether id is already declared in var decls; if yes, a new name is generated
  % and id is substituted in expression
  op substVarIfDeclared (ctxt : CgContext, id : String, decls : CVarDecls1, expr : ITypedExpr)
    : String * ITypedExpr =
    let
      def isDeclared id =
	case findLeftmost (fn (vname, _, _) -> vname = id) decls of
	  | Some _ -> true
	  | None ->
	    case findLeftmost (fn (vname, _) -> vname = id) ctxt.currentFunParams of
	      | Some _ -> true
	      | None -> false
    in
    let
      def determineId id =
	if isDeclared id then 
          determineId (id^"_")
	else 
          id
    in
    let newid = determineId id in
    if newid = id then 
      (id, expr)
    else 
      (newid, substVarName (expr, ("", id), ("", newid)))

  % --------------------------------------------------------------------------------

  op substVarListByFieldRefs (ctxt : CgContext, vlist : List (Option String), structexpr : CExp, expr : CExp) 
    : CExp =
    let
      def subst (vlist, expr, n) =
	case vlist of
	  | [] -> expr
	  | None::vlist -> subst (vlist, expr, n+1)
	  | (Some v)::vlist ->
	    let field      = "field" ^ show n                                                        in
	    let structexpr = if ctxt.useRefTypes then CUnary (CContents, structexpr) else structexpr in
	    let expr       = substVarInExp (expr, v, CStructRef (structexpr, field))                 in
	    subst (vlist, expr, n+1)
    in
    subst (vlist, expr, 0)

  op substVarListByFieldRefsInDecl (ctxt                    : CgContext, 
                                    vlist                   : List (Option String), 
                                    structexpr              : CExp, 
                                    (vname, vtype, optexpr) : CVarDecl1) 
    : CVarDecl1 =
    case optexpr of
      | Some e -> (vname, vtype, Some (substVarListByFieldRefs (ctxt, vlist, structexpr, e)))
      | None   -> (vname, vtype, None)

  op substVarListByFieldRefsInDecls (ctxt       : CgContext,
                                     vlist      : List (Option String),
                                     structexpr : CExp,
                                     decls      : CVarDecls1)
    : CVarDecls1 =
    map (fn decl -> 
           substVarListByFieldRefsInDecl (ctxt, vlist, structexpr, decl)) 
        decls

  % --------------------------------------------------------------------------------

  op mergeBlockIntoExpr (cspc : CSpec, block as (decls, stmts) : CBlock, cexpr : CExp)
    : CSpec * CBlock * CExp =
    case stmts of
      | [] -> (cspc, block, cexpr)
      | stmt::stmts ->
        let (cspc, block as (decls, stmts), cexpr) = mergeBlockIntoExpr (cspc, (decls, stmts), cexpr) in
	let (cexpr, stmts) = 
            case stmt of
              | CExp e -> (CComma (e, cexpr), stmts)
              | _ -> (cexpr, stmt::stmts)
	in
	 (cspc, (decls, stmts), cexpr)

  % --------------------------------------------------------------------------------

  op commaExprToStmts (_ : CgContext, exp : CExp) : CStmts * CExp =
    let
      def commaExprToStmts0 (stmts, exp) =
	case exp of

	  | CBinary (CSet, e0, CComma (e1, e2)) ->
            let (stmts, e1) = commaExprToStmts0 (stmts, e1) in
            let stmts       = stmts ++ [CExp e1]            in
            let (stmts, e2) = commaExprToStmts0 (stmts, e2) in
            commaExprToStmts0 (stmts, CBinary (CSet, e0, e2))
                        
%	  | CComma (CBinary (CSet, e0, e1), e2) ->
%	    let (stmts, e1) = commaExprToStmts0 (stmts, e1) in
%	    let stmts = stmts ++ [CExp (CBinary (CSet, e0, e1)) : CStmt] in
%	    commaExprToStmts0 (stmts, e2)

	  | CComma (e1, e2) ->
            let (stmts, e1) = commaExprToStmts0 (stmts, e1) in
	    let stmts      = stmts ++ [(CExp e1) : CStmt]   in
	    commaExprToStmts0 (stmts, e2)

	  | _ -> (stmts, exp)
    in
    commaExprToStmts0 ([], exp)

  % --------------------------------------------------------------------------------

  op conditionalExprToStmts (ctxt : CgContext, exp : CExp, e2sFun : CExp -> CStmt) 
    : CStmts =
    let (stmts, exp) = commaExprToStmts (ctxt, exp) in
    stmts ++ (case exp of

               | CIfExp (condExp, thenExp, elseExp) ->
                 let return? = 
                     case e2sFun exp of
                       | CReturn _ -> true
                       | _ -> false
                 in
                 let thenStmts = conditionalExprToStmts (ctxt, thenExp, e2sFun) in
                 let elseStmts = conditionalExprToStmts (ctxt, elseExp, e2sFun) in
                 if return? then
                   let ifStmt = CIfThen (condExp, CBlock ([], thenStmts)) in
                   (ifStmt::elseStmts)
                 else
                   let ifStmt = CIf (condExp, CBlock ([], thenStmts), CBlock ([], elseStmts)) in
                   [ifStmt]

              | _ ->
                let finalStmt = e2sFun exp in
                [finalStmt])

  % --------------------------------------------------------------------------------

  % returns the expression for ce1 = ce2
  op getSetExpr (_ : CgContext, ce1 : CExp, ce2 : CExp) : CExp =
    let lhs = ce1 in
    CBinary (CSet, lhs, ce2)

  % --------------------------------------------------------------------------------

  op genName (cspc : CSpec, prefix :String, suffixn : Nat) : String =
    cString (cspc.name ^ prefix ^ show suffixn)

  % --------------------------------------------------------------------------------

  op getMapName    (f : String) : String = "_map_" ^ f
  op getParamName  (n : Nat)    : String = "index" ^ show n

  op [X] getNumberListOfSameSize (l : List X) : List Nat =
    let
      def getNumberList (l, n) =
	case l of
          | [] -> []
	  | _::l -> n :: getNumberList (l, n+1)
    in
    getNumberList (l, 0)

  % --------------------------------------------------------------------------------

  op qname2id (qualifier : String, id : String) : String =
    let quali = if qualifier = UnQualified || qualifier = "" || qualifier = "#return#" then 
                  "" 
                else 
                  qualifier ^ "_" 
    in
    cString (quali ^ id)

  op getConstructorOpNameFromQName (qname : String * String, consid : String) : String =
    % the two _'s are important: that is how the constructor op names are
    % distinguished from other opnames (hack)
    (qname2id qname) ^ "__" ^ consid



  op [X] getLastElem (l : List X) : List X * X =
    case l of
      | [e] -> ([], e)
      | e::l -> 
        let (pref, last) = getLastElem l in
        (e::pref, last)

  % --------------------------------------------------------------------------------

  op getProjectionFieldName (pname : String) : String =
    let pchars = explode pname in
    if forall? isNum pchars then
      let num = stringToNat pname in
      "field" ^ show (num - 1)
    else
      pname

  op getPredefinedFnDecl (fname : String) : CFnDecl =
    case fname of
      | "swc_malloc" -> ("swc_malloc", [CInt:CType], CPtr CVoid)
      | "sizeof"     -> ("sizeof",     [CVoid],      CInt)
      | "New"        -> ("New",        [CVoid],      CPtr CVoid) % this is defined in SWC_common.h
      | _ -> fail ("no predefined function \""^fname^"\" found.")

  % --------------------------------------------------------------------------------

  % returns the "malloc" expression for the given ctype
  % the op unfolds the type in the spec in order to determine
  % the struct to which it points to
  op getMallocApply (cspc : CSpec, t : CType) : Option CExp =
    let t0 = unfoldType (cspc, t) in
    case t0 of

      | CPtr t1 -> 
        let fdecl    = getPredefinedFnDecl "New" in
        let typename = ctypeToString t1 in
        let exp      = CApply (CFn fdecl, [CVar (typename, CVoid)]) in
        Some exp

      | _ -> 
        %let typename = ctypeToString t0 in
        %let _ = writeLine ("***** no malloc for type "^typename) in
        None     

  % --------------------------------------------------------------------------------

  % generates "meaningful" variable names by checking whether
  % the type is a base type. In that case, the type name is
  % used to generate the variable prefix, otherwise a generic
  % variable prefix is used.
  op getVarPrefix (gen : String, typ : CType) : String =
    case typ of
      | CBase s -> map toLowerCase s
      | _ -> gen
  
}
