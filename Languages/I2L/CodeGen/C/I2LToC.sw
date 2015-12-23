(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
 translation from the Intermediate Imperative Language to C
 *)

I2LToC qualifying spec 

import /Languages/MetaSlang/CodeGen/Generic/LanguageMorphism
import /Languages/MetaSlang/CodeGen/Generic/SliceSpec

import /Languages/I2L/I2L
import /Languages/I2L/CodeGen/C/CGenOptions

import /Languages/C/C
import /Languages/C/CUtils

% import ESpecsCodeGenerationOptions

import /Library/Legacy/DataStructures/ListPair

type CurrentContext = | TypeDef String 
                      | OpDecl  String % ops with non-arrow types
                      | FunDecl String % ops with arrow types
                      | FunDefn String 
                      | VarDecl String 
                      | MapDecl String 
                      | Unknown

op printCurrentContext (cc : CurrentContext) : String =
 case cc of
   | TypeDef s -> "Type Definition " ^ s 
   | OpDecl  s -> "Op Declaration  " ^ s 
   | FunDecl s -> "Function Declaration " ^ s 
   | FunDefn s -> "Function Definition  " ^ s 
   | VarDecl s -> "Variable Declaration " ^ s 
   | MapDecl s -> "Map Declaration " ^ s 
   | _ -> "<unknown>"

op setCurrentContext (ctxt : I2C_Context, new : CurrentContext) : I2C_Context =
 let old = ctxt.currentContext in
 % let _ = writeLine ("Changing from " ^ printCurrentContext old ^ " to " ^ printCurrentContext new) in
 ctxt << {currentContext = new}
 
type I2C_Context = {
                    slice            : Slice,
                    voidToUIntType   : C_Type,    % varies with different versions of C
                    xcspc            : C_Spec,    % for incremental code generation, xcspc holds existing cspec being extended
                    currentContext   : CurrentContext,
                    currentFunParams : C_VarDecls
                    }

op setCurrentFunParams (ctxt : I2C_Context, params : C_VarDecls) : I2C_Context =
 ctxt << {currentFunParams = params}                        

op generateC4ImpUnit (impunit : I_ImpUnit, slice : Slice) : C_Spec =
 %let _ = writeLine(";;   phase 2: generating C...") in
 let xcspc    = emptyCSpec "" in
 let lm_data  = slice.lm_data in
 let hincludes     = extractHImports  lm_data.lms  in
 let cincludes     = extractCImports  lm_data.lms  in
 let hinclude_strs = map printImport  hincludes    in
 let cinclude_strs = map printImport  cincludes    in
 let hverbatims    = extractHVerbatims lm_data.lms in
 let cverbatims    = extractCVerbatims lm_data.lms in
 let type_defines  = foldl (fn (defines, trans) ->
                              case trans.target of 
                                | Name _ -> defines
                                | term -> 
                                  defines ++ [(printName trans.source,
                                               printTerm term)])
                           []
                           lm_data.type_translations
 in
 let op_defines    = foldl (fn (defines, trans) ->
                              case trans.target of 
                                | Name _ -> defines
                                | term -> 
                                  defines ++ [(printName trans.source,
                                               printTerm term)])
                           []
                           lm_data.op_translations
 in
 let defines = type_defines ++ op_defines in

 let ctxt = {slice            = slice,
             xcspc            = xcspc,
             voidToUIntType   = C_Int32,  % TODO: see above
             currentContext   = Unknown,
             currentFunParams = []}
 in

 let cspc = emptyCSpec impunit.name in
 let cspc = addBuiltIn (ctxt, cspc) in
 let cspc = foldl (fn (cspc, include)  -> addHInclude      (cspc, include))       cspc hinclude_strs          in
 let cspc = foldl (fn (cspc, include)  -> addCInclude      (cspc, include))       cspc cinclude_strs          in
 let cspc = foldl (fn (cspc, verbatim) -> addHVerbatim     (cspc, verbatim))      cspc hverbatims.pre         in
 let cspc = foldl (fn (cspc, verbatim) -> addCVerbatim     (cspc, verbatim))      cspc cverbatims.pre         in
 let cspc = foldl (fn (cspc, define)   -> addDefine        (cspc, define))        cspc defines                in
 let cspc = foldl (fn (cspc, typedef)  -> c4TypeDefinition (ctxt, cspc, typedef)) cspc impunit.decls.typedefs in
 let cspc = foldl (fn (cspc, opdecl)   -> c4OpDecl         (ctxt, cspc, opdecl))  cspc impunit.decls.opdecls  in
 let cspc = foldl (fn (cspc, fundecl)  -> c4FunDecl        (ctxt, cspc, fundecl)) cspc impunit.decls.funDecls in
 let cspc = foldl (fn (cspc, fundefn)  -> c4FunDefn        (ctxt, cspc, fundefn)) cspc impunit.decls.funDefns in
 let cspc = foldl (fn (cspc, vardecl)  -> c4VarDecl        (ctxt, cspc, vardecl)) cspc impunit.decls.varDecls in
 let cspc = foldl (fn (cspc, mapdecl)  -> c4MapDecl        (ctxt, cspc, mapdecl)) cspc impunit.decls.mapDecls in
 let cspc = foldl (fn (cspc, verbatim) -> addHVerbatim     (cspc, verbatim))      cspc hverbatims.post        in
 let cspc = foldl (fn (cspc, verbatim) -> addHVerbatim     (cspc, verbatim))      cspc cverbatims.post        in % for now, always empty
 let cspc = postProcessCSpec cspc   in
 cspc
 
op postProcessCSpec (cspc : C_Spec) : C_Spec =
 let cspc = typeStructUnionTypeDefns cspc in
 let cspc = deleteUnusedTypes cspc in
 cspc

op addBuiltIn (_ : I2C_Context, cspc : C_Spec) : C_Spec =
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
  %%    let cspc = addInclude (cspc, "SWC_Common.h") in  %% deprecated 
  cspc

% --------------------------------------------------------------------------------

op c4TypeDefinition (ctxt                  : I2C_Context, 
                     cspc                  : C_Spec, 
                     (tname, typ, native?) : I_TypeDefinition) 
 : C_Spec =
 if native? then
   let _ = writeLine("ignoring type def for native type: " ^ anyToString  tname) in
   cspc
 else
 let
   def structUnionFields (cspc, fields) =
     case fields of
       | [] -> (cspc, [])
       | (fname, itype) :: fields -> 
         let (cspc, ctype)   = c4Type (ctxt, cspc, itype)                 in
         let ctype           = if ctype = C_Void then C_UInt32 else ctype in % no void fields allowed
         let (cspc, sfields) = structUnionFields (cspc, fields)           in
         (cspc, (cString fname, ctype) :: sfields)
 in
 let tname = qname2id tname in
 let ctxt  = setCurrentContext (ctxt, TypeDef tname) in
 if tname in? ["Option_Option", "List_List"] then
   cspc
 else
   case typ of
     | I_Enum options ->
       addEnumDefn (cspc, (tname, options))

     | I_Struct fields -> 
       let (cspc, sfields) = structUnionFields (cspc, fields)                           in
       %% defining var in struct namespace as a struct 
       addStructDefn (cspc, (tname, sfields))

     | I_Union fields -> 
       fail ("I_Union not yet implemented")

     | _ ->
       let (cspc,ctype) = c4Type (ctxt, cspc, typ) in
       let typedef      = (tname, ctype)           in
       %% defining var in type namesapce as whatever
       addTypeDefn (cspc, typedef) 


op c4OpDecl (ctxt : I2C_Context, 
             cspc : C_Spec, 
             decl : I_Declaration) 
 : C_Spec =
 %% decl for an op with a non-arrow type
 c4OpDecl_internal (ctxt, cspc, decl, None)

op c4OpDecl_internal (ctxt                         : I2C_Context, 
                      cspc                         : C_Spec, 
                      decl as (opname,typ,optexpr) : I_Declaration, 
                      optinitstr                   : Option String) 
 : C_Spec =
 let vname        = qname2id opname                        in
 let ctxt         = setCurrentContext (ctxt, OpDecl vname) in
 let (cspc,ctype) = c4Type(ctxt,cspc,typ)                  in
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
       | None         -> addVar     (cspc, voidToUInt (ctxt, (vname, ctype)))
       | Some initstr -> addVarDefn (cspc, (vname, ctype, C_Var (initstr, C_Void))) % ok,ok, ... 
         
op voidToUInt (ctxt: I2C_Context, (vname, ctype) : C_VarDecl) : C_VarDecl =
 %% TODO: precise type (C_UInt16, C_UInt32, C_UInt64) depends on target machine
 (vname, if ctype = C_Void then ctxt.voidToUIntType else ctype)

(*
 * for each non-constant variable definition X an function get_X() and a
 * boolean variable _X_initialized is generated 
 *)

op c4NonConstVarDef (ctxt                          : I2C_Context, 
                     vname                         : Id, 
                     ctype as C_Base (name, space) : C_Type, 
                     cspc                          : C_Spec, 
                     block as (decls, stmts)       : C_Block, 
                     cexpr                         : C_Exp) 
 : C_Spec =
 let initfname  = "get_" ^ vname                                           in
 let valuevname = vname ^ "_value"                                         in
 let cspc       = addDefine  (cspc, (vname, initfname ^ "()"))             in
 let null_value = case cexpr of
                    | C_Var (_, typ as C_Ptr _) -> 
                      C_Var ("NULL", typ)
                    | _ -> 
                      C_Cast (ctype, C_Const (C_Int (true, 0)))
 in  
 % cast null to actual desired type
 let cspc       = addVarDefn (cspc, (valuevname, ctype, null_value))       in
 let condexp    = C_Binary   (C_Eq,  C_Var(valuevname, ctype), null_value) in
 let setexp     = C_Binary   (C_Set, C_Var(valuevname, ctype), cexpr)      in
 let new_ifthen = C_IfThen   (condexp, C_Exp setexp)                       in
 let new_return = if ctype = C_Void then
                    C_ReturnVoid
                  else
                    C_Return   (C_Var (valuevname, ctype))   
 in
 let body       = C_Block    (decls, stmts ++ [new_ifthen, new_return])    in
 let fndefn     = (initfname, [], ctype, body)                             in
 let cspc       = addFnDefn  (cspc, fndefn)                                in
 let cspc       = addFn      (cspc, (initfname, [], ctype))                in
 cspc

op c4FunDecl (ctxt  : I2C_Context, 
              cspc  : C_Spec, 
              fdecl : I_FunDeclaration) 
 : C_Spec =
 %% decl for an op with an arrow type
 let (cspc, fname, ctypes, rtype) = c4FunDecl_internal (ctxt, cspc, fdecl) in
 addFn (cspc, (fname, ctypes, rtype))

op c4FunDecl_internal (ctxt  : I2C_Context, 
                       cspc  : C_Spec, 
                       fdecl : I_FunDeclaration) 
 : C_Spec * String * C_Types * C_Type =
 let fname          = qname2id fdecl.name                     in
 let ctxt           = setCurrentContext (ctxt, FunDecl fname) in
 let paramtypes     = map (fn (_, t) -> t) fdecl.params       in
 let (cspc, ctypes) = c4Types (ctxt, cspc, paramtypes)        in
 let (cspc, rtype)  = c4Type  (ctxt, cspc, fdecl.returntype)  in
 (cspc, fname, ctypes, rtype)

op convertExprToReturnStmt (rtype : C_Type) (e : C_Exp) : C_Stmt =
 if rtype = C_Void then
   if e = C_Ignore then
     C_ReturnVoid
   else
     C_Block ([], [C_Exp e, C_ReturnVoid])
 else
   C_Return e

op c4FunDefn (ctxt  : I2C_Context,
              cspc  : C_Spec, 
              fdefn : I_FunDefinition) 
 : C_Spec =
 let fdecl                        = fdefn.decl                              in
 let (cspc, fname, ctypes, rtype) = c4FunDecl_internal (ctxt, cspc, fdecl)  in
 let ctxt                         = setCurrentContext (ctxt, FunDefn fname) in
 let body                         = fdefn.body                              in
 let parnames                     = map (fn (n, _) -> n) fdecl.params       in
 let vardecls                     = zip (parnames, ctypes)                  in

 case body of
   
   | I_Stads stadsbody -> 
     let returnstmt           = C_ReturnVoid in
     let (cspc, block, stmts) = foldl (fn ((cspc, block, stmts), stadcode) -> 
                                         let (cspc, block, stadstmts) = 
                                         c4StadCode (ctxt, cspc, block, stadsbody, returnstmt, stadcode) in
                                         let stmts = stmts++stadstmts in
                                         (cspc, block, stmts))
                                      (cspc, ([], []), []) 
                                      stadsbody
     in
     let stmt  = addStmts (C_Block block, stmts) in
     let stmt  = moveFailAwayFromEnd stmt        in
     let fdefn = (fname, vardecls, rtype, stmt)  in
     addFnDefn (cspc, fdefn)

   | I_Exp expr ->
     let ctxt                                   = setCurrentFunParams (ctxt, vardecls)         in
     let (cspc, block as (decls, stmts), cexpr) = c4RhsExpression (ctxt, cspc, ([], []), expr) in
     let stmts2                                 = conditionalExprToStmts (ctxt, cexpr, rtype)  in
     let block                                  = (decls, stmts ++ stmts2)                     in
     let block                                  = findBlockForDecls block                      in
     let stmt                                   = C_Block block                                in
     let stmt                                   = moveFailAwayFromEnd stmt                     in
     let fdefn                                  = (fname, vardecls, rtype, stmt)               in
     addFnDefn (cspc, fdefn)

op moveFailAwayFromEnd (stmt : C_Stmt) : C_Stmt =
 case stmt of
   | C_Block (vdecls, stmts) ->
     (case reverse stmts of
        | (C_Return (original_final_exp as C_Apply (C_Var (final_fn, _), _))) ::
          (C_IfThen (pred, original_penultimate_stmt))                        ::
          stmts 
        | final_fn in? ["TranslationBuiltIn_mkFail", "fail"] ->
          let reversed_test = C_IfThen (C_Unary (C_LogNot, pred), 
                                        C_Exp original_final_exp)
          in
          C_Block (vdecls, reverse (original_penultimate_stmt :: reversed_test :: stmts))
        | _ -> stmt)
   | _ -> stmt
     
op c4VarDecl (ctxt  : I2C_Context, 
              cspc  : C_Spec, 
              vdecl : I_Declaration)
 : C_Spec =
 % check for records containing functions
 let
   def structCheck (cspc, typ, ids) =
     case typ of
       
       | I_Struct fields ->
         let (cspc, initstr, initstrIsUseful) =
         foldl (fn ( (cspc, initstr, useful), (id, t)) -> 
                  let (cspc, initstr0, useful0) = structCheck (cspc, t, id::ids)                               in
                  let initstr                   = if initstr = "" then initstr0 else initstr ^ ", " ^ initstr0 in
                  (cspc, initstr, useful || useful0))
               (cspc, "", false) 
               fields
         in
         (cspc, "{" ^ initstr ^ "}", initstrIsUseful)
         
       | I_FunOrMap (types, rtype) ->
         let fname           = foldr (fn (id, s) -> if s = "" then id else s ^ "_" ^ id) "" ids in
         let (cspc, vardecl) = addMapForMapDecl (ctxt, cspc, fname, types, rtype)               in
         % todo: add a initializer for the field!
         (addVar (cspc, voidToUInt (ctxt, vardecl)), "&" ^ fname, true)
         
       | _ -> (cspc, "0", false)
 in
 let (vname, vtype, e)                = vdecl                                          in
 let vid                              = qname2id vname                                 in
 let ctxt                             = setCurrentContext (ctxt, VarDecl vid)          in
 let (cspc, initstr, initstrIsUseful) = structCheck (cspc, vtype, [vid])               in
 let optinitstr                       = if initstrIsUseful then Some initstr else None in
 c4OpDecl_internal (ctxt, cspc, vdecl, optinitstr)

% --------------------------------------------------------------------------------

op c4MapDecl (ctxt  : I2C_Context, 
              cspc  : C_Spec, 
              mdecl : I_FunDeclaration) 
 : C_Spec =
 let fid             = qname2id mdecl.name                                              in
 let ctxt            = setCurrentContext (ctxt, MapDecl fid)                            in
 let paramtypes      = map (fn (_, t)->t) mdecl.params                                  in
 let (cspc, vardecl) = addMapForMapDecl (ctxt, cspc, fid, paramtypes, mdecl.returntype) in
 addVar (cspc, voidToUInt (ctxt, vardecl))
 
%% addMapForMapDecl is responsible for creating the arrays and access functions for n-ary vars. 
%% The inputs are the name of the var, the argument types and the return t_ype.
%% It outputs an updated cspec and a var decl for the array. 
%% The var decl is not inserted in the cspec because it may also be used as a field 
%% of a record and has to be added there.

op addMapForMapDecl (ctxt       : I2C_Context, 
                     cspc       : C_Spec, 
                     fid        : String, 
                     paramtypes : I_Types, 
                     returntype : I_Type)
 : C_Spec * C_VarDecl =
 let id                  = getMapName fid in
 let (cspc, paramctypes) = c4Types (ctxt, cspc, paramtypes) in
 case getBoundedNatList paramtypes of
   
   | Some bounds ->
     let (cspc, rtype) = c4Type (ctxt, cspc, returntype)                                      in
     let arraytype     = C_ArrayWithSize (bounds, rtype)                                      in
     let vardecl       = (id, arraytype)                                                      in
     % construct the access function
     let paramnames    = map getParamName (getNumberListOfSameSize paramtypes)                in
     let vardecls      = zip (paramnames, paramctypes)                                        in
     let arrayvarexpr  = C_Var (id, C_Ptr rtype)                                              in 
     let arrayrefs     = foldr (fn (v, e2) -> C_ArrayRef (e2, C_Var v)) arrayvarexpr vardecls in
     let stmt          = C_Return arrayrefs                                                   in
     let cspc          = addFnDefn (cspc, (fid, vardecls, rtype, stmt))                       in
     (cspc, vardecl)
     
   | _ -> 
     fail ("in this version of the code generator you can use either 0-ary vars\n"^
           "or 1-ary vars of the form \"var "^id^": {n:Nat|n<C}\", where C must be\n"^
           "an natural number.")

op getBoundedNatList (types : I_Types) : Option C_Exps =
 case types of
   | [] -> None
   | _ ->
     let
       def getBoundedNatList0 types =
         case types of
           | [] -> Some []
           | (I_BoundedNat n) :: types ->
             (case getBoundedNatList0 types of
                | Some bounds -> 
                  let bound = C_Const (C_Int (true, n)) in
                  Some (bound::bounds)
                | _ -> None)
           | _ -> None
     in
     getBoundedNatList0 types

op coproductSelectorStringLength : C_Exp = C_Const (C_Macro "COPRDCTSELSIZE")

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                     %%
%%                               TYPES                                 %%
%%                                                                     %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op maybe_warn (ctxt : I2C_Context, msg : String) : () =
 %% we don't need to worry about typing problems that would complicate
 %% the calculation of a type (e.g. predicates used within a subtype), 
 %% since we never do that at runtime
 let cc = ctxt.currentContext in
 case cc of
   | TypeDef _ -> ()
   | _ -> writeLine ("I2LToC Warning: " ^ msg ^ " in " ^ printCurrentContext cc)

op c4Type (ctxt : I2C_Context, 
           cspc : C_Spec, 
           typ  : I_Type) 
 : C_Spec * C_Type =
 let
   def structUnionFields (cspc, fields) =
     case fields of
       | [] -> (cspc, [])
       | (fname, itype) :: fields -> 
         let (cspc, ctype)   = c4Type (ctxt, cspc, itype)                 in
         let ctype           = if ctype = C_Void then C_UInt32 else ctype in % no void fields allowed
         let (cspc, sfields) = structUnionFields (cspc, fields)           in
         (cspc, (cString fname, ctype) :: sfields)

   def addFieldNamesToTupleTypes (types) =
     let fieldnames = getFieldNamesForTuple types in
     zip (fieldnames, types)
     
 in
 case c4TypeSpecial (cspc, typ) of
   | Some res -> res
   | _ ->
     case typ of
       
       | I_Primitive p -> 
         (cspc, c4PrimitiveType (ctxt, p))

       | I_Base (tname, ispace) ->
         let cname = qname2id tname in
         let cspace = case ispace of 
                        | Type   -> Type
                        | Struct -> Struct
                        | Union  -> Union
                        | Enum   -> Enum
         in
         (cspc, C_Base (cname, cspace))

       | I_Struct [] -> 
         (cspc, C_Void)
         
       | I_Struct fields -> 
         let (cspc, sfields)    = structUnionFields (cspc, fields)                           in
         let structname         = genName (cspc, "Product", length (getStructDefns cspc))    in
         addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields))
         
       | I_Tuple types ->
         let fields = addFieldNamesToTupleTypes types in
         c4Type (ctxt, cspc, I_Struct fields)
         
       | I_Union fields ->
         let (cspc, ufields)    = structUnionFields (cspc, fields)                           in
         let unionname          = genName (cspc, "CoProduct",  length (getUnionDefns  cspc)) in
         let structname         = genName (cspc, "CoProductS", length (getStructDefns cspc)) in
         let (cspc, uniontype)  = addNewUnionDefn (cspc, ctxt.xcspc, (unionname, ufields))   in
         let sfields            = [("sel", C_Selector), ("alt", uniontype)]                  in
         let (cspc, structtype) = addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields)) in
         (cspc, structtype)
         
       | I_Ref rtype ->
         let (cspc, ctype) = c4Type (ctxt, cspc, rtype) in
         (cspc, C_Ptr ctype)
         
       | I_FunOrMap (types, rtype) ->
         let (cspc, ctypes) = c4Types (ctxt, cspc, types)                                       in
         let (cspc, ctype)  = c4Type  (ctxt, cspc, rtype)                                       in
         let tname          = genName (cspc, "fn", length (getTypeDefns cspc))                  in
         let (cspc, ctype)  = addNewTypeDefn (cspc, ctxt. xcspc, (tname, C_Fn (ctypes, ctype))) in
         (cspc, ctype)
         
       | I_Any -> (cspc, C_Base ("Any", Type))
         
       | I_Void -> (cspc, C_Void)
         
       | I_BoundedNat n -> % inclusive bound
         let c_type =
             if n < 2**8  then C_UInt8  else
             if n < 2**16 then C_UInt16 else
             if n < 2**32 then C_UInt32 else
             if n < 2**64 then C_UInt64 else
             let _ = maybe_warn (ctxt, "Nat maximum exceeds 2**64 - 1: " ^ anyToString n ^ ", using C_UIntInf") in
             C_UIntInf
         in
         (cspc, c_type)
         
       | I_BoundedInt (m, n) -> % inclusive bounds
         let c_type =
             if        0 <= m && n < 2**8  then C_UInt8  else % (-1, 2**8) = [0, 2**8 - 1]
             if        0 <= m && n < 2**16 then C_UInt16 else 
             if        0 <= m && n < 2**32 then C_UInt32 else
             if        0 <= m && n < 2**64 then C_UInt64 else
             if -(2** 7) <= m && n < 2**7  then C_Int8   else
             if -(2**15) <= m && n < 2**15 then C_Int16  else
             if -(2**31) <= m && n < 2**31 then C_Int32  else
             if -(2**63) <= m && n < 2**63 then C_Int64  else
             let _ = maybe_warn (ctxt, "Int range exceeds [-2**63, 2**63 -1]: [" ^ anyToString m ^ ", " ^ anyToString n ^ "], using C_IntInf") in
             C_IntInf
         in
         (cspc, c_type)
         
       | I_BoundedList (ltype, list_length) -> 
         let (cspc, ctype)      = c4Type (ctxt, cspc, ltype)                                 in
         let deflen             = length cspc.defines                                        in
         let constName          = genName (cspc, "MAX", deflen)                              in
         let cspc               = addDefine (cspc, (constName, show list_length))            in
         let arraytype          = C_ArrayWithSize ([C_Const (C_Macro constName)], ctype)     in
         let structname         = genName (cspc, "BoundList", length (getStructDefns cspc))  in
         let sfields            = [("length", C_Int32), ("data", arraytype)]                 in
         let (cspc, structtype) = addNewStructDefn (cspc, ctxt.xcspc, (structname, sfields)) in
         (cspc, structtype)
         
       | _ -> 
         let x = "no code generation implemented for type " ^ anyToString typ in
         (cspc, C_Problem x)


op c4Types (ctxt  : I2C_Context, 
            cspc  : C_Spec, 
            types : I_Types) 
 : C_Spec * C_Types =
 foldl (fn ((cspc, ctypes), typ) ->
          let (cspc, ct) = c4Type (ctxt, cspc, typ) in
          (cspc, ctypes ++ [ct]))
       (cspc, []) 
       types

op c4PrimitiveType (ctxt : I2C_Context, prim : I_Primitive) : C_Type =
 case prim of
   | I_Bool   -> C_Int32
   | I_Nat    -> let _ = maybe_warn (ctxt, "unbounded Nat, using C_UIntInf") in C_UIntInf
   | I_Int    -> let _ = maybe_warn (ctxt, "unbounded Int, using C_IntInf")  in C_IntInf
   | I_Char   -> C_Char
   | I_String -> C_String
   | I_Float  -> C_Float

% handle special cases of types:

op c4TypeSpecial (cspc : C_Spec, typ : I_Type) 
 : Option (C_Spec * C_Type) =
 if bitStringSpecial? then
   case typ of
     | I_Base ((_, "BitString"), _) -> Some (cspc, C_UInt32)
     | _ -> None
 else
   None

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                     %
%                            EXPRESSIONS                              %
%                                                                     %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% --------------------------------------------------------------------------------

op c4RhsExpressions (ctxt  : I2C_Context,
                     cspc  : C_Spec,
                     block : C_Block,
                     exprs : I_TypedExprs) 
 : C_Spec * C_Block * C_Exps =
 foldl (fn ((cspc, block, cexprs), expr) ->
          let (cspc, block, cexpr) = c4RhsExpression (ctxt, cspc, block, expr) in
          (cspc, block, cexprs++[cexpr]))
       (cspc, block, []) 
       exprs

op c4RhsExpression (ctxt  : I2C_Context,
                    cspc  : C_Spec,
                    block : C_Block,
                    exp   : I_TypedExpr) 
 : C_Spec * C_Block * C_Exp =
 c4Expression1 (ctxt, cspc, block, exp, false, false)
     
% --------------------------------------------------------------------------------

op c4LhsExpression (ctxt  : I2C_Context,
                    cspc  : C_Spec,
                    block : C_Block,
                    exp   : I_TypedExpr) 
 : C_Spec * C_Block * C_Exp =
 c4Expression1 (ctxt, cspc, block, exp, true, false)

% --------------------------------------------------------------------------------

op c4InitializerExpressions (ctxt  : I2C_Context,
                             cspc  : C_Spec,
                             block : C_Block,
                             exprs : I_TypedExprs) 
 : C_Spec * C_Block * C_Exps =
 foldl (fn ((cspc, block, cexprs), expr) ->
          let (cspc, block, cexpr) = c4InitializerExpression (ctxt, cspc, block, expr) in
          (cspc, block, cexprs++[cexpr]))
       (cspc, block, []) 
       exprs

op c4InitializerExpression (ctxt  : I2C_Context,
                            cspc  : C_Spec,
                            block : C_Block,
                            exp   : I_TypedExpr) 
 : C_Spec * C_Block * C_Exp =
 c4Expression1 (ctxt, cspc, block, exp, false, true)

% --------------------------------------------------------------------------------

op c4Expression1 (ctxt            : I2C_Context, 
                  cspc            : C_Spec, 
                  block           : C_Block,  
                  exp             : I_TypedExpr,
                  lhs?            : Bool, 
                  forInitializer? : Bool)
 : C_Spec * C_Block * C_Exp =
 let (cspc, block, cexpr) = c4Expression2 (ctxt, cspc, block, exp, lhs?, forInitializer?) in
 let cexpr = 
     let {expr=_,typ,cast?} = exp in
     if cast? then
       let (cspc, ctype) = c4Type (ctxt, cspc, typ) in
       C_Cast (ctype, cexpr)
     else
       cexpr
 in
 let (cspc, block, cexpr) = mergeBlockIntoExpr (cspc, block, cexpr)                       in
 (cspc, block, cexpr)

op c4Expression2 (ctxt                      : I2C_Context,
                  cspc                      : C_Spec,
                  block as (decls, stmts)   : C_Block,
                  exp as {expr, typ, cast?} : I_TypedExpr,
                  lhs?                      : Bool,
                  forInitializer?           : Bool)
 : C_Spec * C_Block * C_Exp = 
 case c4SpecialExpr (ctxt, cspc, block, exp) of
   | Some x -> x
   | _ ->
 let     

   def addProjections (cexpr, projections) =
     case projections of
       | [] -> cexpr
       | p :: projections ->
         addProjections (mkCStructRef (cexpr, p), projections)

   def processFunMap f (vname, projections, exprs) =
     let id                    = qname2id vname                                      in
     let (cspc, block, cexprs) = c4RhsExpressions (ctxt, cspc, block, exprs)         in
     let (cspc, ctype)         = c4Type (ctxt, cspc, typ)                            in
     let cexpr1                = addProjections (f (C_Var (id, ctype)), projections) in
     (cspc, block, C_Apply (cexpr1, cexprs))
     
   def processMapAccess f (vname, maptype, projections, exprs) =
     let id = qname2id vname in
     case maptype of
       
       | I_FunOrMap (types, _) ->
         (case getBoundedNatList (types) of
            
            | Some ns ->
              let (cspc, block, cexprs) = c4RhsExpressions (ctxt, cspc, block, exprs) in
              let (cspc, ctype)         = c4Type (ctxt, cspc, typ)                    in
              % if we have projections, the map name must be the prefix of the last field name
              % otherwise of the id itself
              let id = foldl (fn (s, p) -> 
                                s ^ "_" ^ getProjectionFieldName p)
                             (getMapName id) 
                             projections
              in
              let projections = []                                                       in
              let cexpr1      = addProjections (f (C_Var (id, ctype)), projections)      in
              let arrayrefs   = foldr (fn (e1, e2) -> C_ArrayRef (e2, e1)) cexpr1 cexprs in
              (cspc, block, arrayrefs)
              
            | _ -> 
              fail "unsupported variable format, use 1-ary vars from bounded Nat")
       | _ -> 
         fail "unsupported variable format, use 1-ary vars from bounded Nat"
         
 in
 case expr of
   | I_Str   s -> (cspc, block, C_Const (C_Str   s))
   | I_Int   n -> (cspc, block, C_Const (C_Int   (true, n))) % TODO: Should we ignore type here?
   | I_Char  c -> (cspc, block, C_Const (C_Char  c))
   | I_Float f -> (cspc, block, C_Const (C_Float f))
   | I_Bool  b -> (cspc, block, if b then ctrue else cfalse)
     
   | I_Builtin bexp -> c4BuiltInExpr (ctxt, cspc, block, bexp)
     
   | I_Let (id, typ, opt_idexpr, expr, mv_return?) ->
     let (cspc, ctype) = c4Type (ctxt, cspc, typ)                       in
     let letvardecl    = (id, ctype)                                    in
     let optinit       = None                                           in % if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None  ??   
     let (id, expr)    = substVarIfDeclared (ctxt, id, decls, expr)     in
     let letvardecl1   = (id, ctype, optinit)                           in
     (case opt_idexpr of
        | Some idexpr ->
          let (cspc, (decls, stmts), idcexpr) = c4RhsExpression (ctxt, cspc, block, idexpr) in
          let lhs_var                         = C_Var letvardecl                            in
          let lhs                             = if mv_return? then 
                                                  C_Unary (C_Contents, lhs_var)   
                                                else
                                                  lhs_var
          in
          let assignment                      = getSetExpr (ctxt, lhs, idcexpr)             in
          let decls                           = if mv_return? then 
                                                  decls 
                                                else 
                                                  decls++[letvardecl1]
          in
          let block                           = (decls, stmts)                              in
          let (cspc, block, cexpr)            = c4RhsExpression (ctxt, cspc, block, expr)   in
          (cspc, block, C_Comma (assignment, cexpr))
        | _ ->
          %% When we're processing a multiple-value let binding,
          %% the variables are declared here, but are not set here.
          %% Instead, refs to those vars are passed to a called function which sets them.
          let block                           = (decls++[letvardecl1], stmts)               in
          let (cspc, block, cexpr)            = c4RhsExpression (ctxt, cspc, block, expr)   in
          (cspc, block, cexpr))

   | I_FunCall (vname, projections, exprs) ->
     processFunMap (fn e -> e) (vname, projections, exprs)
     
   | I_FunCallDeref (vname, projections, exprs) ->
     processFunMap (fn e -> C_Unary (C_Contents, e)) (vname, projections, exprs)
     
   | I_MapAccess (vname, maptype, projections, exprs) ->
     if lhs? then
       processMapAccess (fn e -> e) (vname, maptype, projections, exprs)
     else
       processFunMap (fn e -> e) (vname, projections, exprs)
       
   | I_MapAccessDeref (vname, maptype, projections, exprs) ->
     if lhs? then 
       processMapAccess (fn e -> C_Unary (C_Contents, e)) (vname, maptype, projections, exprs)
     else
       processFunMap (fn e -> C_Unary (C_Contents, e)) (vname, projections, exprs)
            
   | I_TupleExpr exprs ->
     let fieldnames = getFieldNamesForTuple (exprs) in
     c4StructExpr (ctxt, cspc, block, typ, exprs, fieldnames, forInitializer?)
     
   | I_StructExpr fields ->
     let fieldnames = map (fn (n, _) -> cString n) fields in
     let exprs      = map (fn (_, e) -> e)         fields in
     c4StructExpr (ctxt, cspc, block, typ, exprs, fieldnames, forInitializer?)
     
   | I_Project (expr, id) ->
     let (cspc, block, cexpr) = c4Expression1 (ctxt, cspc, block, expr, lhs?, forInitializer?)  in
     (cspc, block, mkCStructRef (cexpr, id))
     
   | I_Select (expr, id) ->
     % Union types are currently implemented something like this:
     %
     % union  CoProduct0  { struct Product0* Cons; uint32_t Nil; };
     % struct CoProductS1 { char sel[(COPRDCTSELSIZE)];  union CoProduct0 alt; };
     % 
     % We select a variant by first using a struct ref to get the "alt" field: 'x.alt' or 'x->alt'.
     % then doing a union ref to get a properly typed pointer at the variant: 'x.alt.Cons' or 'x->alt.Cons'.
     % (Fow now, the union ref is direct: we don't implement 'x.alt->Cons' or 'x->alt->Cons'.)
     %
     % Note: The following I_Project abuses I2L notation to refer to something that is 
     %       not intrinsic to I2L, but exists only for the sake of the C implementation.
     %       Abetting this abuse of notation, we take the I_Union type from the argument 
     %       expression (which will be implemented as a C-struct) and also assign it to 
     %       the "alt" projection (which will be implemented as an associated C-union).
     let alt_expr             = expr << {expr = I_Project (expr, "alt")}                           in % benign abuse of I2L notation
     let (cspc, block, cexpr) = c4Expression1 (ctxt, cspc, block, alt_expr, lhs?, forInitializer?) in % exploit I2L machinery
     let cexpr                = if false then C_Unary (C_Contents, cexpr) else cexpr               in % indirection not an option
     (cspc, block, mkCUnionRef (cexpr, id))
     
   | I_ConstrCall (typename, selector, exprs) ->
     let consfun       = getConstructorOpNameFromQName (typename, selector.name) in
     let (cspc, ctype) = c4Type (ctxt, cspc, typ)                                in
     let (cspc, block as (decls, stmt), constrCallExpr) =
     let fnid = getConstructorOpNameFromQName (typename, selector.name) in
     case exprs of
       | [] -> 
         let fndecl = (fnid, [], ctype) in
         (cspc, block, C_Fn fndecl)
       | _ :: _ -> 
         let (cspc, ctypes) = 
             foldl (fn ((cspc, ctypes), typed_expr) -> 
                      let (cspc, ctype) = c4Type (ctxt, cspc, typed_expr.typ) in
                      (cspc, ctypes++[ctype]))
                   (cspc, []) 
                   exprs 
         in
         let (cspc, block, cexprs) = c4RhsExpressions (ctxt, cspc, block, exprs) in
         let fndecl = (fnid, ctypes, ctype) in
         (cspc, block, C_Apply (C_Fn fndecl, cexprs))
     in
     (cspc, block, constrCallExpr)
     
   | I_AssignUnion (selector, optexpr) ->
     (case typ of
        | I_Enum _ -> 
          let res = C_EnumRef selector.name in
          (cspc, block, res)
        | _ ->
          let (cspc, block as (decls, stmts), optcexpr) =
              case optexpr of
                | Some expr -> 
                  let (cspc, block, cexpr) = c4RhsExpression (ctxt, cspc, block, expr) in
                  (cspc, block, Some cexpr)
                | None -> 
                  (cspc, block, None)
          in
          let (cspc, ctype) = c4Type (ctxt, cspc, typ)                          in
          let varPrefix     = getVarPrefix ("_coproduct", ctype)                in
          let xname         = freshVarName (varPrefix, ctxt, block)             in
          let decl          = (xname, ctype)                                    in
          let optinit       = getMallocApply (cspc, ctype)                      in
          let decl1         = (xname, ctype, optinit)                           in
          let selassign     = [getSelAssignStmt (ctxt, selector, xname, ctype)] in
          let altassign     = case optcexpr of
                                | None -> []
                                | Some cexpr ->
                                  let sref  = mkCUnionRef (mkCStructRef (C_Var decl, "alt"), 
                                                           selector.name) 
                                  in
                                  [C_Exp (getSetExpr (ctxt, sref, cexpr))]
          in
          let block = (decls ++ [decl1], stmts ++ selassign ++ altassign) in
          let res   = C_Var decl in
          (cspc, block, res))
     
   | I_UnionCaseExpr (typed_expr, unioncases) ->
     let I_Union union_fields                      = typed_expr.typ                                  in
     let (cspc0, block0 as (decls, stmts), cexpr0) = c4RhsExpression (ctxt, cspc, block, typed_expr) in
     
     % Insert a variable for the discriminator in case cexpr0 isn't a variable.
     % Otherwise the C Compiler might issue an "illegal lvalue" error.
     
     let (block0 as (decls, stmts), disdecl, newdecl?) =
     case cexpr0 of
       | C_Var decl -> ((decls, stmts), decl, false)
       | _ ->
         let disname         = "_dis_" ^ show (length decls)       in
         let (cspc, distype) = c4Type (ctxt, cspc, typed_expr.typ) in
         let disdecl         = (disname, distype)                  in
         let disdecl0        = (disname, distype, None)            in
         let block0          = (decls++[disdecl0], stmts)          in
         (block0, disdecl, true)
     in
     
     %% To prevent C typing errors, insert a dummy variable of the same type 
     %% as the expression to be used in the nonexhaustive match case, 
     
     let (cspc, xtype)  = c4Type (ctxt, cspc, typ)                  in
     let xtype          = if xtype = C_Void then C_Int32 else xtype in
     let varPrefix      = getVarPrefix ("_Vd_", xtype)              in
     let xname          = freshVarName (varPrefix, ctxt, block)     in
     let xdecl          = (xname, xtype, None)                      in
     let funname4errmsg = printCurrentContext ctxt.currentContext   in
     let errorCaseExpr  = C_Comma (C_Var ("NONEXHAUSTIVEMATCH_ERROR"^funname4errmsg, C_Int32), 
                                   C_Var (xname, xtype)) 
     in
     let block0         = (decls ++ [xdecl], stmts)                 in
     
     let 
       def casecond index = 
         getSelCompareExp (ctxt, C_Var disdecl, index) 
     in
     
     let (cspc, block, ifexpr) =
         foldr (fn (unioncase, (cspc, block as (decls, stmts), ifexp)) -> 
                  case unioncase of
                       
                    | I_ConstrCase (opt_selector, vlist, expr) ->
                      (case opt_selector of

                         | None -> 
                           %% pattern is just a simple wildcard
                           c4RhsExpression (ctxt, cspc0, block0, expr)
                           
                         | Some selector ->
                           let condition = casecond selector in
                           % insert the variables:
                           let (cspc, block, cexpr) =
                               case findLeftmost (fn | None -> false | _ -> true) vlist of
                                 
                                 | None -> 
                                   %% varlist contains only wildcards (same as single wildcard case)
                                   c4RhsExpression (ctxt, cspc, block, expr)
                                   
                                 | _ ->
                                   let Some (_,field_type) = findLeftmost (fn field -> field.1 = selector.name) union_fields   in
                                   let (cspc, idtype)      = c4Type (ctxt, cspc, field_type)                                   in
                                   let valexp              = mkCUnionRef (mkCStructRef (cexpr0, "alt"), selector.name)         in
                                   case vlist of
                                     
                                     | [Some id] -> 
                                       
                                       %% vlist contains exactly one var
                                       
                                       let (id, expr) = substVarIfDeclared (ctxt, id, decls, expr) in % subst before
                                       let decl       = (id, idtype)                               in
                                       let assign     = getSetExpr (ctxt, C_Var decl, valexp)      in
                                       
                                       %% The assignment must be attached to the declaration.  
                                       %% Otherwise the new variable could be accessed without being initialized.
                                       %% [so why is optinit None then?]
                                       
                                       let optinit                       = None                                      in
                                       let decl1                         = (id, idtype, optinit)                     in
                                       let (cspc, (decls, stmts), cexpr) = c4RhsExpression (ctxt, cspc, block, expr) in
                                       (cspc, (decls ++ [decl1], stmts), C_Comma (assign, cexpr))
                                       
                                     | _ -> 
                                       
                                       %% vlist is a list of variable names representing the fields of the record 
                                       %% that is the argument of the constructor. 
                                       
                                       %% We introduce a fresh variable of that record type and substitute the variable
                                       %% in the vlist by corresponding StructRefs into the record.
                                       
                                       let varPrefix            = getVarPrefix ("_Va", idtype)                             in
                                       let id                   = freshVarName (varPrefix, ctxt, block)                    in
                                       let decl                 = (id, idtype)                                             in
                                       let assign               = getSetExpr (ctxt, C_Var decl, valexp)                    in
                                       let optinit              = None                                                     in
                                       let decl1                = (id, idtype, optinit)                                    in
                                       %% Put decl1 into the block passed to c4RhsExpression, to avoid reusing id.
                                       let (decls, stmts)       = block                                                    in
                                       let block                = (decls ++ [decl1], stmts)                                in
                                       let (cspc, block, cexpr) = c4RhsExpression (ctxt, cspc, block, expr)                in
                                       let cexpr                = substVarListByFieldRefs (ctxt, vlist, C_Var decl, cexpr) in  % subst after
                                       (cspc, block, C_Comma (assign, cexpr))

                           in
                           (cspc, block, C_IfExp (condition, cexpr, ifexp)))

                    | I_VarCase (id,ityp,exp) ->
                      let (cid, exp)          = substVarIfDeclared (ctxt, id, decls, exp)    in
                      let (cspc, block, cexp) = c4RhsExpression (ctxt, cspc, block, exp)     in
                      let (cspc, ctype)       = c4Type (ctxt, cspc, ityp)                    in
                      let cvar                = (cid, ctype)                                 in
                      let cassign             = getSetExpr (ctxt, C_Var cvar, C_Var disdecl) in
                      
                      %% The assignment must be attached to the declaration.
                      %% Otherwise the new variable may be accessed without being initialized.
                      %% [so why is coptinit None then?]
                      
                      let coptinit            = None                                         in
                      let cdecl               = (cid, ctype, coptinit)                       in
                      (cspc, (decls ++ [cdecl], stmts), C_Comma (cassign, cexp))
                      
                    | I_NatCase (n, exp) -> 
                      let (cspc, block, ce)    = c4RhsExpression (ctxt, cspc, block, exp)                 in
                      let constant             = {expr = I_Int n, typ = I_Primitive I_Int, cast? = false} in
                      let (cspc, block, const) = c4RhsExpression (ctxt, cspc, block, constant)            in  
                      let cond                 = C_Binary (C_Eq, C_Var disdecl, const)                    in
                      let ifexp                = C_IfExp  (cond, ce, ifexp)                               in
                      (cspc, block, ifexp)
                      
                    | I_CharCase (c, exp) ->
                      let (cspc, block, ce)    = c4RhsExpression (ctxt, cspc, block, exp)                   in
                      let constant             = {expr = I_Char c, typ = I_Primitive I_Char, cast? = false} in
                      let (cspc, block, const) = c4RhsExpression (ctxt, cspc, block, constant)              in
                      let cond                 = C_Binary (C_Eq, C_Var disdecl, const)                      in
                      let ifexp                = C_IfExp  (cond, ce, ifexp)                                 in
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
            let var   = C_Var disdecl                                                  in
            let xx    = C_Binary (C_Set, var, cexpr0)                                  in
            let newif = mapExp (fn expr -> if expr = cexpr0 then var else expr) ifexpr in
            C_Comma (xx, newif)
         else 
           ifexpr)

   | I_Embedded (id, exp) ->
     let (cspc, block, cexp) = c4RhsExpression (ctxt, cspc, block, exp) in
     (cspc, block, getSelCompareExp (ctxt, cexp, id))

   | I_IfExpr (e1, e2, e3) ->
     let (cspc, block, ce1) = c4RhsExpression (ctxt, cspc, block, e1) in
     let (cspc, block, ce2) = c4RhsExpression (ctxt, cspc, block, e2) in
     let (cspc, block, ce3) = c4RhsExpression (ctxt, cspc, block, e3) in
     (cspc, block, C_IfExp (ce1, ce2, ce3))
     
   | I_Var id ->
     let (cspc, ctype) = c4Type (ctxt, cspc, typ) in
     let vname         = qname2id id              in
     let varexp        = C_Var (vname, ctype)     in
     (cspc, block, varexp)
     
   | I_VarDeref id ->
     let var_expr = {expr = I_Var id, typ = typ, cast? = false} in
     let (cspc, block, cexp) = c4RhsExpression (ctxt, cspc, block, var_expr) in
     (cspc, block, C_Unary (C_Contents, cexp))
     
   | I_VarRef id ->
     let var_expr = {expr = I_Var id, typ = typ, cast? = false} in
     let (cspc, block, cexp) = c4RhsExpression (ctxt, cspc, block, var_expr) in
     (cspc, block, C_Unary (C_Address, cexp))
     
   | I_Comma (exprs) ->
     (case exprs of
        
        | expr1::exprs1 ->
          let (exprs, expr)        = getLastElem (exprs)                    in
          let (cspc, block, cexpr) = c4RhsExpression (ctxt, cspc, block, expr) in
          foldr (fn (expr1, (cspc, block, cexpr)) ->
                   let (cspc, block, cexpr1) = c4RhsExpression (ctxt, cspc, block, expr1) in
                   (cspc, block, C_Comma (cexpr1, cexpr)))
                (cspc, block, cexpr) 
                exprs
          
        | _ -> fail "Comma expression with no expressions?!")
     
   | I_Null ->
     (cspc, block, C_Ignore)
     
   | I_Problem msg ->
     (cspc, block, C_Problem msg)

   | _ -> 
     (print expr;
      fail  "unimplemented case for expression.")

% --------------------------------------------------------------------------------

op c4StructExpr (ctxt       : I2C_Context, 
                 cspc       : C_Spec, 
                 block      : C_Block, 
                 typ        : I_Type, 
                 exprs      : I_TypedExprs, 
                 fieldnames : List String, 
                 _          : Bool)
 : C_Spec * C_Block * C_Exp =
 %% Even inside initialization forms, we may need to allocate struct's.
 % if forInitializer? then
 %  c4StructExprForInitializer (ctxt, cspc, block, typ, exprs, fieldnames)
 % else
 c4StructExpr2 (ctxt, cspc, block, typ, exprs, fieldnames)
      

op c4StructExpr2 (ctxt       : I2C_Context, 
                  cspc       : C_Spec, 
                  block      : C_Block,
                  typ        : I_Type,
                  exprs      : I_TypedExprs, 
                  fieldnames : List String)
 : C_Spec * C_Block * C_Exp =
 let (cspc, block as (decls, stmts), fexprs) = c4RhsExpressions (ctxt, cspc, block, exprs) in
 let (cspc, ctype)                           = c4Type (ctxt, cspc, typ)                    in
 let varPrefix                               = getVarPrefix ("_product", ctype)            in
 let xname                                   = freshVarName (varPrefix, ctxt, block)       in
 let ctype                                   = if ctype = C_Void then C_Int32 else ctype   in
 let decl                                    = (xname, ctype)                              in
 let optinit                                 = None                                        in % if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None ???
 let decl1                                   = (xname, ctype, optinit)                     in
 let assignstmts = map (fn (field, fexpr) ->
                          let fieldref = mkCStructRef (C_Var decl, field) in
                          C_Exp (getSetExpr (ctxt, fieldref, fexpr)))
                       (zip (fieldnames, fexprs))
 in
 let block = (decls++[decl1], stmts++assignstmts) in
 let res   = C_Var decl                           in
 (cspc, block, res)

op c4StructExprForInitializer (ctxt  : I2C_Context,
                               cspc  : C_Spec,
                               block : C_Block,
                               _     : I_Type,
                               exprs : I_TypedExprs,
                               _     : List String)
 : C_Spec * C_Block * C_Exp =
 let (cspc, block, cexprs) = c4InitializerExpressions (ctxt, cspc, block, exprs) in
 (cspc, block, C_Field cexprs)

% --------------------------------------------------------------------------------

op strcmp         : C_Exp = C_Fn ("strcmp",         [C_String,  C_String],          C_Int16)  % might subtract one char from another for result
op strncmp        : C_Exp = C_Fn ("strncmp",        [C_String,  C_String, C_Int32], C_Int16)  % might subtract one char from another for result
op hasConstructor : C_Exp = C_Fn ("hasConstructor", [C_VoidPtr, C_Int16],           C_Int8)   % boolean value
op selstrncpy     : C_Exp = C_Fn ("SetConstructor", [C_String,  C_String],          C_String) % strncpy

op c4BuiltInExpr (ctxt  : I2C_Context,
                  cspc  : C_Spec,
                  block : C_Block,
                  exp   : I_BuiltinExpression) 
 : C_Spec * C_Block * C_Exp =
 let 
   def c4e e = c4RhsExpression (ctxt, cspc, block, e) 
 in
 let
   def c42e f e1 e2 = 
     let (cspc, block, ce1) = c4RhsExpression (ctxt, cspc, block, e1) in
     let (cspc, block, ce2) = c4RhsExpression (ctxt, cspc, block, e2) in
     (cspc, block, f (ce1, ce2))
 in
 let
   def c41e f e1 =
     let (cspc, block, ce1) = c4RhsExpression (ctxt, cspc, block, e1) in
     (cspc, block, f ce1)
 in
 let
   def strless (ce1, ce2) =
     let strcmpcall = C_Apply (strcmp, [ce1, ce2]) in
     C_Binary (C_Eq, strcmpcall, C_Const (C_Int (true, -1)))
     
   def strequal (ce1, ce2) =
     let strcmpcall = C_Apply (strcmp, [ce1, ce2]) in
     C_Binary (C_Eq, strcmpcall, C_Const (C_Int (true, 0)))
     
   def strgreater (ce1, ce2) =
     let strcmpcall = C_Apply (strcmp, [ce1, ce2]) in
     C_Binary (C_Eq, strcmpcall, C_Const (C_Int (true, 1)))
 in
 let
   def stringToFloat e =
     case c4e e of
       | (cspc, block, C_Const (C_Str s)) -> 
         let f = (true, 11, 22, None) in % TODO: FIX THIS TO PARSE s
         (cspc, block, C_Const (C_Float f))
       | _ -> fail "expecting string as argument to \"stringToFloat\""
 in
 case exp of
   | I_Equals              (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Eq,     c1, c2))     e1 e2
     
   | I_BoolNot             (e1)     -> c41e (fn (c1)     -> C_Unary  (C_LogNot, c1))         e1
   | I_BoolAnd             (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_LogAnd, c1, c2))     e1 e2
   | I_BoolOr              (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_LogOr,  c1, c2))     e1 e2
   | I_BoolImplies         (e1, e2) -> c42e (fn (c1, c2) -> C_IfExp  (c1,       c2, cfalse)) e1 e2
   | I_BoolEquiv           (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Eq,     c1, c2))     e1 e2
     
   | I_IntPlus             (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Add,    c1, c2))     e1 e2
   | I_IntMinus            (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Sub,    c1, c2))     e1 e2
   | I_IntUnaryMinus       (e1)     -> c41e (fn (c1)     -> C_Unary  (C_Negate, c1))         e1
   | I_IntMult             (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Mul,    c1, c2))     e1 e2
   | I_IntDiv              (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Div,    c1, c2))     e1 e2
   | I_IntRem              (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Mod,    c1, c2))     e1 e2
   | I_IntLess             (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Lt,     c1, c2))     e1 e2
   | I_IntGreater          (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Gt,     c1, c2))     e1 e2
   | I_IntLessOrEqual      (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Le,     c1, c2))     e1 e2
   | I_IntGreaterOrEqual   (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Ge,     c1, c2))     e1 e2
     
   | I_IntToFloat          (e1)     -> c41e (fn (c1)     -> C_Cast   (C_Float,  c1))         e1
   | I_StringToFloat       (e1)     -> stringToFloat e1
     
   | I_FloatPlus           (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Add,    c1, c2))     e1 e2
   | I_FloatMinus          (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Sub,    c1, c2))     e1 e2
   | I_FloatUnaryMinus     (e1)     -> c41e (fn (c1)     -> C_Unary  (C_Negate, c1))         e1
   | I_FloatMult           (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Mul,    c1, c2))     e1 e2
   | I_FloatDiv            (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Div,    c1, c2))     e1 e2
   | I_FloatLess           (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Lt,     c1, c2))     e1 e2
   | I_FloatGreater        (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Gt,     c1, c2))     e1 e2
   | I_FloatLessOrEqual    (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Le,     c1, c2))     e1 e2
   | I_FloatGreaterOrEqual (e1, e2) -> c42e (fn (c1, c2) -> C_Binary (C_Ge,     c1, c2))     e1 e2
   | I_FloatToInt          (e1)     -> c41e (fn (c1)     -> C_Cast   (C_Int32,  c1))         e1
     
   | I_StrLess             (e1, e2) -> c42e strless    e1 e2
   | I_StrEquals           (e1, e2) -> c42e strequal   e1 e2
   | I_StrGreater          (e1, e2) -> c42e strgreater e1 e2

op ctrue  : C_Exp = C_Var ("TRUE",  C_Int32)
op cfalse : C_Exp = C_Var ("FALSE", C_Int32)

% --------------------------------------------------------------------------------

(*
 * code for handling special case, e.g. the bitstring operators
 *)

type PrePost = | Prefix | Postfix

op map_unary_name (s : String, prepost : PrePost) : Option C_UnaryOp =
 case s of

   % for unary "*" "&" "-" "~" "!", there is no ambiguity, 
   % so allow prefix or nothing:

   | "*"          -> Some C_Contents
   | "prefix_*"   -> Some C_Contents
   | "&"          -> Some C_Address
   | "prefix_&"   -> Some C_Address
   | "-"          -> Some C_Negate
   | "prefix_-"   -> Some C_Negate
   | "~"          -> Some C_BitNot
   | "prefix_~"   -> Some C_BitNot
   | "!"          -> Some C_LogNot
   | "prefix_!"   -> Some C_LogNot
     
   % but force user to be explicit for "++" and "--", where there 
   % is a real ambiguity between prefix and postfix:
     
   | "prefix_++"  -> Some C_PreInc
   | "postfix_++" -> Some C_PostInc
     
   | "prefix_--"  -> Some C_PreDec
   | "postfix_--" -> Some C_PostDec
     
   | _ -> None
       
op map_binary_name (s : String) : Option C_BinaryOp =
 case s of
   | "="   -> Some C_Set          
   | "+"   -> Some C_Add          
   | "-"   -> Some C_Sub          
   | "*"   -> Some C_Mul          
   | "/"   -> Some C_Div          
   | "%"   -> Some C_Mod          
   | "&"   -> Some C_BitAnd       
   | "|"   -> Some C_BitOr        
   | "xor" -> Some C_BitXor       
   | "<<"  -> Some C_ShiftLeft    
   | ">>"  -> Some C_ShiftRight   
   | "+="  -> Some C_SetAdd       
   | "-="  -> Some C_SetSub       
   | "*="  -> Some C_SetMul       
   | "/="  -> Some C_SetDiv       
   | "%="  -> Some C_SetMod       
   | "&="  -> Some C_SetBitAnd    
   | "|="  -> Some C_SetBitOr     
   | "^="  -> Some C_SetBitXor    
   | "<<=" -> Some C_SetShiftLeft 
   | ">>=" -> Some C_SetShiftRight
   | "&&"  -> Some C_LogAnd       
   | "||"  -> Some C_LogOr        
   | "=="  -> Some C_Eq           
   | "!="  -> Some C_NotEq        
   | "<"   -> Some C_Lt           
   | ">"   -> Some C_Gt           
   | "<="  -> Some C_Le           
   | ">="  -> Some C_Ge           
   | _ -> None

op c4SpecialExpr (ctxt : I2C_Context, cspc : C_Spec, block : C_Block, typed_expr : I_TypedExpr) 
 : Option (C_Spec * C_Block * C_Exp) =
 let 
   %% def c4e e = 
   %%   Some (c4RhsExpression (ctxt, cspc, block, e))
 
   def c41e f e1 =
     let (cspc, block, ce1) = c4RhsExpression (ctxt, cspc, block, e1) in
     Some (cspc, block, f ce1)
     
   def c42e f e1 e2 = 
     let (cspc, block, ce1) = c4RhsExpression (ctxt, cspc, block, e1) in
     let (cspc, block, ce2) = c4RhsExpression (ctxt, cspc, block, e2) in
     Some (cspc, block, f (ce1, ce2))
     
 in
 if ~bitStringSpecial? then 
   None
 else 
   case typed_expr.expr of
     | I_Var (_, "Zero") -> Some (cspc, block, C_Const (C_Int (true, 0)))
     | I_Var (_, "One")  -> Some (cspc, block, C_Const (C_Int (true, 1)))

     | I_FunCall (("System", "setf"), [], [e1, e2]) -> 
       c42e (fn (c1, c2) -> 
               C_Binary (C_Set, c1, c2))
            e1
            e2
       
     | I_FunCall ((_, name),  [], [e1]) ->
       (case map_unary_name (name, Prefix) of % todo: allow PostFix
          | Some c_unary_op ->
            c41e (fn c1 -> 
                    C_Unary (c_unary_op, c1))
                 e1
          | _ -> None)

     | I_FunCall ((_, name),  [], [e1, e2]) ->
       %% todo: verify Infix ??
       (case map_binary_name name of 
          | Some c_binary_op ->
            c42e (fn (c1, c2) -> 
                    C_Binary (c_binary_op, c1, c2)) 
                 e1 
                 e2
          | _ -> None)
     | _ ->
       None

% --------------------------------------------------------------------------------

op constExpr? (cspc : C_Spec, expr : C_Exp) : Bool =
 case expr of
   | C_Const  _                  -> true
   | C_Var    ("TRUE",  C_Int32) -> true
   | C_Var    ("FALSE", C_Int32) -> true
   | C_Var    ("NULL",  C_Ptr _) -> true
   | C_Field  []                 -> true
   | C_Field  (e1 :: es)         -> (constExpr? (cspc, e1)) && (constExpr? (cspc, C_Field es))
   | C_Unary  (_, e1)            ->  constExpr? (cspc, e1)
   | C_Binary (_, e1, e2)        -> (constExpr? (cspc, e1)) && (constExpr? (cspc, e2))
     
     % this isn't true in C:
     % | C_Var (vname, vdecl) ->
     %   (case findLeftmost (fn (id, _, _)->id=vname) cspc.varDefns of
     % | Some (_, _, exp) -> constExpr? (cspc, exp)
     % | _ -> false)
     
   | _ -> false

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                     %
%                               STADS                                 %
%                                                                     %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


op c4StadCode (ctxt       : I2C_Context, 
               cspc       : C_Spec,
               block      : C_Block, 
               allstads   : List I_StadCode, 
               returnstmt : C_Stmt,
               stadcode   : I_StadCode) 
 : C_Spec * C_Block * C_Stmts =
 % decls are empty, so the following 2 lines have no effect:
 let declscspc = generateC4ImpUnit (stadcode.decls, ctxt.slice) in
 let cspc      = mergeCSpecs [cspc, declscspc] in
 let (cspc, block, stepstmts) =
 foldl (fn ((cspc, block, stmts), stp) ->
          let (cspc, block, stpstmts) = c4StepCode (ctxt, cspc, block, allstads, returnstmt, stp) in
          (cspc, block, stmts++stpstmts))
       (cspc, block, []) 
       stadcode.steps
 in
 let lblstmt = if stadcode.showLabel? then [C_Label stadcode.label] else [] in
 (cspc, block, lblstmt ++ stepstmts ++ [returnstmt])
 
op c4StepCode (ctxt            : I2C_Context, 
               cspc            : C_Spec,
               block           : C_Block,
               allstads        : List I_StadCode, 
               returnstmt      : C_Stmt, 
               (rule, gotolbl) : I_StepCode) 
 : C_Spec * C_Block * C_Stmts =
 let gotostmt                   = if final? (allstads, gotolbl) then returnstmt else C_Goto gotolbl in
 let (cspc, block, rules_stmts) = c4StepRule (ctxt, cspc, block, Some gotostmt, rule)               in
 %foldl (fn ((cspc, block, rulestmts), rule) -> 
 %	     let (cspc, block, rule1stmts) = c4StepRule (ctxt, cspc, block, rule) in
 %        (cspc, block, rulestmts++rule1stmts))
 %	   (cspc, block, [])
 %      rules
 %in
 (cspc, block, rules_stmts)

op c4StepRule (ctxt                    : I2C_Context,
               cspc                    : C_Spec,
               block as (decls, stmts) : C_Block,
               optgotostmt             : Option C_Stmt,
               rule                    : I_Rule)
 : C_Spec * C_Block * C_Stmts =
 let gotostmts = case optgotostmt of | Some stmt -> [stmt] | None -> [] in
 case rule of
   
   | I_Skip -> 
     (cspc, block, gotostmts)
     
   | I_Cond (expr, rule) ->
     let (cspc, block,  cexpr)     = c4RhsExpression (ctxt, cspc, block, expr)                 in
     let (cspc, block0, rulestmts) = c4StepRule   (ctxt, cspc, ([], []), optgotostmt, rule) in
     (cspc, block, [C_IfThen (cexpr, addStmts (C_Block block0, rulestmts))])

   | I_Update (optexpr1, expr2) ->
     let (cspc, block0 as (decls0, stmts0), cexpr2) = c4RhsExpression (ctxt, cspc, ([], []), expr2) in
     (case optexpr1 of
        
        | Some expr1 ->
          let (cspc, block0 as (decls0, stmts0), cexpr1) = c4LhsExpression (ctxt, cspc, block0, expr1) in
          let stmts = stmts0++[C_Exp (getSetExpr (ctxt, cexpr1, cexpr2))]++gotostmts                   in
          let stmts = if decls0 = [] then stmts else [C_Block (decls0, stmts)]                         in
          (cspc, block, stmts)
          
        | None -> 
          let stmts = stmts0 ++ [C_Exp cexpr2] ++ gotostmts                    in
          let stmts = if decls0 = [] then stmts else [C_Block (decls0, stmts)] in
          (cspc, block, stmts))
     
   | I_UpdateBlock (upddecls, updates) ->
     let (cspc, block, declstmts) =
         foldl (fn ((cspc, block, updstmts), ((_, id), typ, optexpr)) ->
                  let (cspc, ctype) = c4Type (ctxt, cspc, typ) in
                  let iddecl        = (id, ctype)              in
                  let optinit       = None                     in % if ctxt.useRefTypes then getMallocApply (cspc, ctype) else None ??
                  let iddecl1       = (id, ctype, optinit)     in
                  let (cspc, block as (decls1, stmts1), assignidstmts) = 
                  case optexpr of
                    
                    | None -> 
                      (cspc, block, [])
                      
                    | Some expr ->
                      let (cspc, block, cexpr) = c4RhsExpression (ctxt, cspc, block, expr) in
                      (cspc, block, [C_Exp (getSetExpr (ctxt, C_Var iddecl, cexpr))])
                      
                  in
                  let block = (decls1 ++ [iddecl1], stmts1) in
                  (cspc, block, updstmts ++ assignidstmts))
               (cspc, block, []) 
               upddecls
     in
     let (cspc, block, updatestmts) =
         foldl (fn ((cspc, block, updatestmts), update) ->
                  let (cspc, block, stmts) = c4StepRule (ctxt, cspc, block, None, I_Update update) in
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
op getSelAssignStmt (ctxt     : I2C_Context,
                     selector : I_Selector,
                     varname  : String,
                     vartype  : C_Type) 
 : C_Stmt =
 C_Exp (C_Binary (C_Set, 
                  mkCStructRef (C_Var (varname, vartype), "sel"), 
                  C_Const (C_Int (true, selector.index))))

op getSelCompareExp (ctxt     : I2C_Context,
                     expr     : C_Exp,
                     selector : I_Selector) 
 : C_Exp =
 case expr of
   
   | C_Unary (C_Contents, expr) -> 
     C_Apply (hasConstructor, [expr, C_Const (C_Int (true, selector.index))])
     
   | _ -> 
     C_Binary (C_Eq, mkCStructRef (expr, "sel"), (C_Const (C_Int (true, selector.index))))

op getSelCompareExp0 (ctxt     : I2C_Context,
                      expr     : C_Exp,
                      selector : I_Selector) 
 : C_Exp =
 C_Binary (C_Eq, mkCStructRef (expr, "sel"), C_Const (C_Int (true, selector.index)))

% --------------------------------------------------------------------------------

% checks whether id is already declared in var decls; if yes, a new name is generated
% and id is substituted in expression

op substVarIfDeclared (ctxt  : I2C_Context,
                       id    : String,
                       decls : C_VarDecls1,
                       expr  : I_TypedExpr)
 : String * I_TypedExpr =
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
 let id    = cString     id in % e.g., id could be "tv--0" due to maybeIntroduceVarsForTerms in Environment.sw
 let newid = determineId id in
 if newid = id then 
   (id, expr)
 else 
   (newid, substVarName (expr, ("", id), ("", newid)))

% --------------------------------------------------------------------------------

op substVarListByFieldRefs (ctxt       : I2C_Context,
                            vlist      : List (Option String),
                            structexpr : C_Exp,
                            expr       : C_Exp) 
 : C_Exp =
 let
   def subst (vlist, expr, n) =
     case vlist of
       | [] -> expr
       | None::vlist -> subst (vlist, expr, n+1)
       | (Some v)::vlist ->
         let expr = substVarInExp (expr, v, mkCStructRef (structexpr, "field" ^ show n)) in
         subst (vlist, expr, n+1)
 in
 subst (vlist, expr, 0)
 
op substVarListByFieldRefsInDecl (ctxt                    : I2C_Context, 
                                  vlist                   : List (Option String), 
                                  structexpr              : C_Exp, 
                                  (vname, vtype, optexpr) : C_VarDecl1) 
 : C_VarDecl1 =
 case optexpr of
   | Some e -> (vname, vtype, Some (substVarListByFieldRefs (ctxt, vlist, structexpr, e)))
   | None   -> (vname, vtype, None)
     
op substVarListByFieldRefsInDecls (ctxt       : I2C_Context,
                                   vlist      : List (Option String),
                                   structexpr : C_Exp,
                                   decls      : C_VarDecls1)
 : C_VarDecls1 =
 map (fn decl -> 
        substVarListByFieldRefsInDecl (ctxt, vlist, structexpr, decl)) 
     decls

% --------------------------------------------------------------------------------

op mergeBlockIntoExpr (cspc                    : C_Spec,
                       block as (decls, stmts) : C_Block,
                       cexpr                   : C_Exp)
 : C_Spec * C_Block * C_Exp =
 case stmts of
   | [] -> (cspc, block, cexpr)
   | stmt::stmts ->
     let (cspc, block as (decls, stmts), cexpr) = mergeBlockIntoExpr (cspc, (decls, stmts), cexpr) in
     let (cexpr, stmts) = 
         case stmt of
           | C_Exp e -> (C_Comma (e, cexpr), stmts)
           | _ -> (cexpr, stmt::stmts)
     in
     (cspc, (decls, stmts), cexpr)

% --------------------------------------------------------------------------------

op flattenCommaExprs (_ : I2C_Context, exp : C_Exp) : C_Exps =
 let
   def aux exp =
     case exp of
       
       | C_Binary (C_Set, e0, C_Comma (e1, e2)) ->
         let e1s                    = aux e1           in
         let e2_last :: rev_e2_tail = reverse (aux e2) in
         e1s ++ (reverse rev_e2_tail) ++ [C_Binary (C_Set, e0, e2_last)]
         
         % | C_Comma (C_Binary (C_Set, e0, e1), e2) ->
         %   let (stmts, e1) = commaExprToStmts0 (stmts, e1) in
         %   let stmts = stmts ++ [C_Exp (C_Binary (C_Set, e0, e1)) : C_Stmt] in
         %   commaExprToStmts0 (stmts, e2)

       | C_Comma (e1, e2) ->
         (aux e1) ++ (aux e2)

       | _ -> 
         [exp]
 in
 aux exp

% --------------------------------------------------------------------------------

op conditionalExprToStmts (ctxt   : I2C_Context,
                           exp    : C_Exp,
                           rtype  : C_Type)
 : C_Stmts =
 let
   def aux exp return? =
     let exprs                 = flattenCommaExprs (ctxt, exp) in
     let last_expr :: rev_head = reverse exprs                 in
     let head_exprs            = reverse rev_head              in
     let head_stmts = 
         foldl (fn (stmts, exp) ->
                          case exp of
                            | C_IfExp (condExp, thenExp, elseExp) ->
                              let thenStmts = aux thenExp false in
                              let elseStmts = aux elseExp false in
                              (case elseStmts of
                                 | [] ->
                                   let ifStmt = C_IfThen (condExp, 
                                                          C_Block ([], thenStmts)) 
                                   in
                                   let new = ifStmt::elseStmts in
                                   stmts ++ new
                                 | _ ->
                                   let ifStmt = C_If (condExp, 
                                                      C_Block ([], thenStmts), 
                                                      C_Block ([], elseStmts)) 
                                   in
                                   let new = [ifStmt] in
                                   stmts ++ new)
                            | _ ->
                              let new = [C_Exp exp] in
                              stmts ++ new)
                       []
                       head_exprs
     in
     let last_stmts =
         case last_expr of
             
           | C_IfExp (condExp, thenExp, elseExp) ->
             let thenStmts = aux thenExp return? in
             let elseStmts = aux elseExp return? in
             if return? then
               let ifStmt = C_IfThen (condExp, C_Block ([], thenStmts)) in
               (ifStmt::elseStmts)
             else
               let ifStmt = C_If (condExp, C_Block ([], thenStmts), C_Block ([], elseStmts)) in
               [ifStmt]
               
           | _ -> 
             let last_stmt = 
                 if return? then
                   convertExprToReturnStmt rtype last_expr
                 else
                   C_Exp last_expr
             in
             [last_stmt]
     in
     let stmts = head_stmts ++ last_stmts in
     case last stmts of
       | C_Exp (C_Var _) -> butLast stmts
       | _ -> stmts
 in
 aux exp true 

% --------------------------------------------------------------------------------

% returns the expression for ce1 = ce2
op getSetExpr (_ : I2C_Context, ce1 : C_Exp, ce2 : C_Exp) : C_Exp =
 let lhs = ce1 in
 C_Binary (C_Set, lhs, ce2)

% --------------------------------------------------------------------------------

op genName (cspc    : C_Spec,
            prefix  : String, 
            suffixn : Nat) 
 : String =
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
 let quali = if qualifier = UnQualified || qualifier = "" || qualifier = "#return#" then  % terminate string for emacs "
               "" 
             else 
               qualifier ^ "_" 
 in
 cString (quali ^ id)

op getConstructorOpNameFromQName (qname : String * String, consid : String)
 : String =
 % the two _'s are important: that is how the constructor op names are
 % distinguished from other opnames (hack)
 (qname2id qname) ^ "__" ^ cString consid
 
op [X] getLastElem (l : List X) : List X * X =
 case l of
   | [e] -> ([], e)
   | e::l -> 
     let (pref, last) = getLastElem l in
     (e::pref, last)

% --------------------------------------------------------------------------------

op mkCStructRef (cexpr: C_Exp, fname : String) : C_Exp = 
 let field_name = getProjectionFieldName fname in
 C_StructRef (cexpr, field_name)

op getProjectionFieldName (pname : String) : String =
 let pchars = explode pname in
 if forall? isNum pchars then
   let num = stringToNat pname in
   "field" ^ show (num - 1)
 else
   cString pname

op mkCUnionRef (cexpr: C_Exp, vname : String) : C_Exp = 
 let variant_name = cString vname in
 C_UnionRef (cexpr, variant_name)

op getPredefinedFnDecl (fname : String) : C_FnDecl =
 case fname of
   | "swc_malloc" -> ("swc_malloc", [C_Int32], C_VoidPtr)
   | "sizeof"     -> ("sizeof",     [C_Void],  C_UInt32)
   | "New"        -> ("New",        [C_Void],  C_VoidPtr)   % this is defined in SWC_common.h
   | _ -> fail ("no predefined function \""^fname^"\" found.")
     
% --------------------------------------------------------------------------------

% returns the "malloc" expression for the given ctype
% the op unfolds the type in the spec in order to determine
% the struct to which it points to
op getMallocApply (cspc : C_Spec, t : C_Type) : Option C_Exp =
 let t0 = unfoldType (cspc, t) in
 case t0 of
   
   | C_Ptr t1 -> 
     let fdecl    = getPredefinedFnDecl "New" in
     let typename = ctypeToString t1 in
     let exp      = C_Apply (C_Fn fdecl, [C_Var (typename, C_Void)]) in
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
op getVarPrefix (gen : String, typ : C_Type) : String =
 case typ of
   | C_Base (s, _)               -> "_" ^ (map toLowerCase s) ^ "_"
   | C_Ptr  (C_Base (s, Struct)) -> "_" ^ (map toLowerCase s) ^ "_"
   | _ -> gen
     
op freshVarName (prefix              : String,
                 ctxt                : I2C_Context, 
                 block as (decls, _) : C_Block) 
 : String =
 let vars_to_avoid = (map (fn cvar_decl -> cvar_decl.1) ctxt.currentFunParams) 
                     ++ 
                     (freeVars block) 
                     ++ 
                     (map (fn (v, _, _) -> v) decls)
 in
 let
   def aux (n, name) = 
     if name in? vars_to_avoid then
       aux (n + 1, prefix ^ (show n))
     else 
       name
 in
 aux (0, prefix)

end-spec
