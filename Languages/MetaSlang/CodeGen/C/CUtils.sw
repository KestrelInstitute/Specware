
CUtils qualifying spec
{

  import C
  import CPrint
  import /Languages/MetaSlang/Specs/Printer

  op emptyCSpec (name : String) : CSpec =
    {
     name                 = name,
     includes             = [],
     defines              = [],
     constDefns           = [],
     vars                 = [],
     fns                  = [],
     axioms               = [],
     structUnionTypeDefns = [],
     varDefns             = [],
     fnDefns              = []}

  op addDefine    (cspc : CSpec, X    : String) : CSpec =
    let defines = filter (fn(df) -> df ~= X) cspc.defines in
    let defines = defines ++ [X] in
    cspc << {defines = defines}

  op renameCSpec             (cspc : CSpec, X : String)                : CSpec = cspc << {name                 = X}                       
  op addInclude              (cspc : CSpec, X : String)                : CSpec = cspc << {includes             = cspc.includes             ++ [X]}
  op addConstDefn            (cspc : CSpec, X : CVarDefn)              : CSpec = cspc << {constDefns           = cspc.constDefns           ++ [X]}
  op addVar                  (cspc : CSpec, X : CVarDecl)              : CSpec = cspc << {vars                 = cspc.vars                 ++ [X]}
  op addVarDefn              (cspc : CSpec, X : CVarDefn)              : CSpec = cspc << {varDefns             = cspc.varDefns             ++ [X]}
  op addAxiom                (cspc : CSpec, X : CExp)                  : CSpec = cspc << {axioms               = cspc.axioms               ++ [X]}
  op addStructDefn           (cspc : CSpec, X : CStructDefn)           : CSpec = cspc << {structUnionTypeDefns = cspc.structUnionTypeDefns ++ [CStruct X]}
  op addUnionDefn            (cspc : CSpec, X : CUnionDefn)            : CSpec = cspc << {structUnionTypeDefns = cspc.structUnionTypeDefns ++ [CUnion  X]}
  op setStructUnionTypeDefns (cspc : CSpec, X : CStructUnionTypeDefns) : CSpec = cspc << {structUnionTypeDefns = X}

  %% CMacros is a list of names of macros defined in SWC_Common.h
  %% E.g. "String_Less" expands to "strcmp", so we should avoid
  %% adding another declaration for strcmp.
  op SWC_Common_Macros : List String =
    ["String_PlusPlus",
     "String_Caret",
     "Caret",
     "writeLine",
     "String_toScreen",
     "toString",
     "Nat_toString",
     "Less",
     "Greater",
     "String_Less",
     "fail"]

  op addFn (cspc : CSpec, X as (fname,_,_) : CFnDecl) : CSpec =
    if fname in? SWC_Common_Macros then
      cspc
    else
      let other_fns = filter (fn(fname0,_,_) -> fname0 ~= fname) cspc.fns in
      cspc << {fns = other_fns ++ [X]}

  op delFn (cspc : CSpec, fname : String) : CSpec =
    let other_fns = filter (fn(fname0,_,_) -> fname0 ~= fname) cspc.fns in
    cspc << {fns = other_fns}

  op addTypeDefn (cspc : CSpec, X as (tname,_) : CTypeDefn) : CSpec =
    let other_typedefs = filter (fn (CTypeDefn (tname0,_)) -> tname0 ~= tname | _ -> true) cspc.structUnionTypeDefns in
    cspc << {structUnionTypeDefns = other_typedefs ++ [CTypeDefn X]}

  op addFnDefnAux (cspc : CSpec, fndefn as (fname,params,rtype,body) : CFnDefn, overwrite? : Bool) : CSpec =
    let other_defs = if overwrite? then
                       filter (fn(fname0,_,_,_) -> fname ~= fname0) cspc.fnDefns
                     else 
                       cspc.fnDefns
    in 
    cspc << {fnDefns = other_defs ++ [fndefn]}

  op addFnDefn          (cspc : CSpec, fndefn : CFnDefn) : CSpec = addFnDefnAux(cspc, fndefn, true)
  op addFnDefnOverwrite (cspc : CSpec, fndefn : CFnDefn) : CSpec = addFnDefnAux(cspc, fndefn, true)

  % --------------------------------------------------------------------------------

  op getStructDefns (cspc : CSpec) : CStructDefns =
    foldl (fn (structs, su) ->
             case su of
               | CStruct X -> structs ++ [X]
               | _ -> structs)
          [] 
          cspc.structUnionTypeDefns

  op getUnionDefns (cspc : CSpec) : CUnionDefns =
    foldl (fn (unions, su) ->
             case su of
               | CUnion X -> unions ++ [X]
               | _ -> unions)
          []
          cspc.structUnionTypeDefns

  op getTypeDefns (cspc : CSpec) : CTypeDefns =
    foldl (fn (typedefns, su) ->
             case su of
               | CTypeDefn X -> typedefns ++ [X]
               | _ -> typedefns)
          []
          cspc.structUnionTypeDefns

  % --------------------------------------------------------------------------------

  (**
   * adds a new type definition to cspc; definition in xcspc are
   * also searched (for incremental code generation)
   *)
  op addNewTypeDefn (cspc : CSpec, xcspc : CSpec, tdef as (tname,typ) : CTypeDefn) 
    : CSpec * CType =
    case findTypeDefnInCSpecs ([cspc,xcspc], typ) of
      | Some s -> (cspc,                   CBase s)
      | None   -> (addTypeDefn(cspc,tdef), CBase tname)

  % --------------------------------------------------------------------------------

  % only add the struct definition, if it is new, i.e. if now other
  % struct definition exists in the cspec that has the same fields
  % returns the struct definition that contains the same fields as
  % the input struct definition.
  op addNewStructDefn (cspc : CSpec, xcspc : CSpec, (sname,sfields) : CStructDefn, useRefTypes? : Bool) 
    : CSpec * CType =
    let structs  = getStructDefns cspc  in
    let xstructs = getStructDefns xcspc in
    let (cspc,struct) = 
        case findLeftmost (fn (sname0,sfields0) -> sfields = sfields0) (structs ++ xstructs) of

          | Some (sname,_) -> 
            (cspc,CStruct sname)

          | None -> 
            let cspc   = addStructDefn (cspc, (sname,sfields)) in
            let struct = CStruct sname in
            (cspc,struct)
    in
    let typ = if useRefTypes? then CPtr struct else struct in
    let typ = case findTypeDefnInCSpecs ([cspc,xcspc], typ) of
                | Some s -> CBase s
                | None -> typ
    in
    (cspc,typ)


  op addNewUnionDefn (cspc : CSpec, xcspc : CSpec, (sname,sfields) : CUnionDefn)
    : CSpec * CType =
    let unions  = getUnionDefns cspc  in
    let xunions = getUnionDefns xcspc in
    case findLeftmost (fn (sname0,sfields0) -> sfields = sfields0) (unions ++ xunions) of

      | Some (sname,_) -> 
        (cspc, CUnion sname)

      | _ ->
        let cspc = addUnionDefn (cspc, (sname,sfields)) in
        (cspc, CUnion sname)


  % --------------------------------------------------------------------------------

  op addStmts (stmt1 : CStmt, stmts2 : CStmts) : CStmt =
    case stmt1 of

      | CBlock (decls, stmts) -> 
        CBlock (decls, stmts ++ stmts2)

      | _ -> 
        CBlock ([],    [stmt1]++stmts2)

  % --------------------------------------------------------------------------------

  op prependDecl (decl : CVarDecl1, stmt : CStmt) : CStmt =
    case stmt of

      | CBlock (decls,       stmts) -> 
        CBlock (decl::decls, stmts)

      | _ -> 
        CBlock ([decl],      [stmt])

  % --------------------------------------------------------------------------------

  op mkBlock (stmt : CStmt) : CBlock =
    case stmt of
      | CBlock (decls, stmts) -> (decls, stmts)
      | _ -> ([], [stmt])

  % --------------------------------------------------------------------------------

  op [a] memberEq (eq : a * a -> Bool) (elem : a, l : List a) : Bool =
    case l of 
      | [] -> false
      | x::l -> eq (x, elem) || memberEq eq (elem,l)

  op [a] concatnew (eq : a * a -> Bool) (l1 : List a, l2 : List a) : List a =
    foldl (fn (res,elem) -> 
             if memberEq eq (elem,res) then
               res
             else 
               res ++ [elem])
           l1 
           l2

  op [a] concatnewEq : List a * List a -> List a = 
    concatnew (fn (x,y) -> x=y)

  op mergeCSpecs (cspcs : List CSpec) : CSpec =
    case cspcs of
      | []     -> emptyCSpec ""
      | [cspc] -> cspc
      | cspc1 :: cspc2 :: cspcs ->
        let cspc =
         {
	  name                 = cspc1.name,
	  includes             = concatnewEq (cspc1. includes,   cspc2.includes),
	  defines              = concatnewEq (cspc1. defines,    cspc2.defines),
	  constDefns           = concatnewEq (cspc1. constDefns, cspc2.constDefns),
	  axioms               = concatnewEq (cspc1. axioms,     cspc2.axioms),
	  varDefns             = concatnewEq (cspc1. varDefns,   cspc2.varDefns),
	  vars                 = concatnew (fn ((var1,_),      (var2,_))       -> var1=var2)     (cspc1.vars,    cspc2.vars),
	  fns                  = concatnew (fn ((fname1,_,_),  (fname2,_,_))   -> fname1=fname2) (cspc1.fns,     cspc2.fns),
	  fnDefns              = concatnew (fn ((fname1,_,_,_),(fname2,_,_,_)) -> fname1=fname2) (cspc1.fnDefns, cspc2.fnDefns),
	  structUnionTypeDefns = foldr (fn | (x as CTypeDefn(tname,_),res) -> 
                                             (filter (fn (CTypeDefn (tname0,_)) -> tname0 ~= tname | _ -> true) res) ++ [x]
                                           | (x,res) -> 
                                             res ++ [x])
                                       cspc2.structUnionTypeDefns
                                       cspc1.structUnionTypeDefns}
        in
        mergeCSpecs (cspc :: cspcs)

  op printCType (t : CType) : String =
    let pr  = ppType (t, prettysNone[]) in
    let txt = format (80, pr) in
    toString txt

  op printCTypes (sep : String) (types : List CType) : String =
    foldl (fn (s,t) -> s ^ sep ^ printCType t) "" types

  type Destination = | File | Terminal | String

  op printCSpecToX (cspc : CSpec, fname : String, asHeader : Bool, X : Destination) : String =
    let pr = if asHeader then
               ppHeaderSpec cspc
	     else 
               ppSpec cspc
    in
    let txt = format (80, pr) in
    case X of
      | File     -> (writeLine("C-File: "^fname); toFile(fname,txt); "")
      | Terminal -> (toTerminal txt; "")
      | String   -> toString txt

  op printCSpecToFileEnv (cspc : CSpec, fname : String) : SpecCalc.Env () =
    let _ = printCSpecToFile (cspc, fname) in
    return ()

  op printCSpecToFile (cspc : CSpec, fname : String) : () =
    %let fname = getImplFilename(cspc.name) in
    let _ = printCSpecToX (cspc, fname, false, File) in
    ()

  op printCSpecToTerminal (cspc : CSpec) : () = 
    let _ = printCSpecToX (cspc, "", false, Terminal) in
    ()

  op printCSpecToString (cspc : CSpec) : String = 
    printCSpecToX (cspc, "", false, String)

  def printCSpecAsHeaderToFile(cspc) = 
    let fname = getHeaderFilename(cspc.name) in
    (printCSpecToX(cspc,fname,true,File);())

  op printCSpecAsHeaderToTerminal (cspc : CSpec) : () = (printCSpecToX(cspc,"",true,Terminal);())

  op printCSpecAsHeaderToString   (cspc : CSpec) : String = printCSpecToX(cspc,"",true,String)
  
  op getHeaderFilename (fname : String) : String = fname ^ ".h"
  op getImplFilename   (fname : String) : String = fname ^ ".c"

  % --------------------------------------------------------------------------------

  op cString (id : String) : String = 
    let id = map cChar id in
    if isCKeyword id then 
      cString ("slang_" ^ id)
    else 
      substGlyphInIdent id

  op substGlyphInIdent (id : String) : String =
    let 
      def substGlyphChar (c : Char) : List Char =
        let ord = Char.ord(c) in
        if ord < 32 then 
          [#_]
        else if ord > 126 then 
          [#_]
        else if ((ord >= 48) && (ord <=  57))
  	     || ((ord >= 65) && (ord <=  90))
	     || ((ord >= 97) && (ord <= 122))
             || (ord = 95)
             || (ord = 36)
         then 
          [c]
        else
	 case ord of
	   |  32 -> explode "Space"
           |  33 -> explode "Exclam"
           |  34 -> explode "Quotedbl"
           |  35 -> explode "Numbersign"
          %|  36 -> explode "Dollar"
           |  37 -> explode "Percent"
           |  38 -> explode "Ampersand"
           |  39 -> explode "Quotesingle"
           |  40 -> explode "Parenleft"
           |  41 -> explode "Parenright"
           |  42 -> explode "Asterisk"
           |  43 -> explode "Plus"
           |  44 -> explode "Comma"
           |  45 -> explode "$"
           |  46 -> explode "Period"
           |  47 -> explode "Slash"
           |  58 -> explode "Colon"
           |  59 -> explode "Semicolon"
           |  60 -> explode "Less"
           |  61 -> explode "Equal"
           |  62 -> explode "Greater"
           |  63 -> explode "Q"
           |  64 -> explode "At"
           |  91 -> explode "Bracketleft"
           |  92 -> explode "Backslash"
           |  93 -> explode "Bracketright"
           |  94 -> explode "Caret"
           |  96 -> explode "Grave"
           | 123 -> explode "Braceleft"
           | 124 -> explode "Bar"
           | 125 -> explode "Braceright"
           | 126 -> explode "Tilde"
           | _ -> [#_]
    in
    let 
      def substGlyph carray =
        case carray of
          | [#']       -> [] % special case: last character is a single quote
	  | c::carray0 -> substGlyphChar c ++ substGlyph carray0
	  | []         -> []
    in
    implode (substGlyph (explode id))

  op cChar (c : Char) : Char =
    case c of
      | #? -> #Q
      | _  -> c

  op isCKeyword (s : String) : Bool =
    s in? cKeywords

  op cKeywords : List String =
    ["auto",     "break",  "case",     "char",    "const",    "continue",
     "default",  "do",     "double",   "else",    "enum",     "extern",
     "float",    "for",    "goto",     "if",      "int",      "long",
     "register", "return", "short",    "signed",  "sizeof",   "static",
     "struct",   "switch", "typedef",  "union",   "unsigned", "void",
     "volatile", "while"]

  op mapExp (f : CExp -> CExp) (e : CExp) : CExp =
    let mp = mapExp f in
    let e  = f e      in
    case e of
      | CApply (e,    es) ->
        CApply (mp e, map mp es)

      | CUnary (o, e) ->
        CUnary (o, mp e)

      | CBinary (o, e1,    e2) ->
        CBinary (o, mp e1, mp e2)

      | CCast (t, e) ->
        CCast (t, mp e)

      | CStructRef (e,    s) ->
        CStructRef (mp e, s)

      | CUnionRef (e,    s) ->
        CUnionRef (mp e, s)

      | CArrayRef (e1,    e2) ->
        CArrayRef (mp e1, mp e2)

      | CIfExp (e1,    e2,    e3) ->
        CIfExp (mp e1, mp e2, mp e3)

      | CComma (e1,    e2) ->
        CComma (mp e1, mp e2)

      | CSizeOfExp (e1) ->
        CSizeOfExp (mp e1)

      | CField (es) ->
        CField (map mp es)

      | _ -> e

  op mapExp2 (f : CExp -> CExp, ft : CType -> CType) (e : CExp) : CExp =
    let mp = mapExp2 (f,ft) in
    let e  = f e            in
    case e of
      | CVar decl -> 
        CVar (mapVarDecl (f,ft) decl)

      | CFn decl -> 
        CFn( mapFnDecl (f,ft) decl)

      | CApply(e,es) -> 
        CApply (mp e,map mp es)

      | CUnary (o, e) -> 
        CUnary (o, mp e)

      | CBinary (o, e1,    e2) -> 
        CBinary (o, mp e1, mp e2)

      | CCast (t, e) -> 
        CCast (t, mp e)

      | CStructRef (e,    s) -> 
        CStructRef (mp e, s)

      | CUnionRef (e,    s) -> 
        CUnionRef (mp e, s)

      | CArrayRef (e1,    e2) -> 
        CArrayRef (mp e1, mp e2)

      | CIfExp (e1,    e2,    e3) -> 
        CIfExp (mp e1, mp e2, mp e3)

      | CComma (e1,    e2) -> 
        CComma (mp e1, mp e2)

      | CSizeOfExp e1 -> 
        CSizeOfExp (mp e1)

      | CSizeOfType t -> 
        CSizeOfType (ft t)

      | CField es -> 
        CField (map mp es)

      | _ -> e


  op substVarInExp (e : CExp, id : String, substexp : CExp) : CExp =
    mapExp (fn e -> 
              case e of
                | CVar (id0,_) -> if id0 = id then substexp else e
                | _ -> e)
           e

  op mapType (f : CType -> CType) (t : CType) : CType =
    let mp = mapType f in
    let t  = f t       in
    case t of

      | CPtr t -> 
        CPtr (mp t)

      | CArray t -> 
        CArray (mp t)

      | CArrayWithSize (n, t) -> 
        CArrayWithSize (n, mp t)

      | CFn (ts,        t) -> 
        CFn (map mp ts, mp t)

      | _ -> t

  op mapCSpec (fe : CExp -> CExp, ft : CType -> CType) (cspc : CSpec) : CSpec =
    cspc << {
             constDefns           = map (mapVarDefn             (fe,ft)) cspc.constDefns,
             vars                 = map (mapVarDecl             (fe,ft)) cspc.vars,
             fns                  = map (mapFnDecl              (fe,ft)) cspc.fns,
             axioms               = map (mapExp2                (fe,ft)) cspc.axioms,
             structUnionTypeDefns = map (mapStructUnionTypeDefn (fe,ft)) cspc.structUnionTypeDefns,
             varDefns             = map (mapVarDefn             (fe,ft)) cspc.varDefns,
             fnDefns              = map (mapFnDefn              (fe,ft)) cspc.fnDefns
             }

  op mapStmt (fe : CExp -> CExp, ft : CType -> CType) (stmt : CStmt) : CStmt =
    let mp  = mapStmt (fe,ft) in
    let mpe = mapExp2 (fe,ft) in
    let mpt = mapType ft      in
    case stmt of

      | CExp e -> 
        CExp (fe e)

      | CBlock (decls,                          stmts) -> 
        CBlock (map (mapVarDecl1(fe,ft)) decls, map mp stmts)

      | CIf (e,     stmt1,    stmt2) -> 
        CIf (mpe e, mp stmt1, mp stmt2)

      | CReturn e -> 
        CReturn (mpe e)

      | CWhile (e,     stmt) -> 
        CWhile (mpe e, mp stmt)

      | CIfThen (e,     stmt) ->
        CIfThen (mpe e, mp stmt)

      | CSwitch (e,     stmts) -> 
        CSwitch (mpe e, map mp stmts)

      | _ -> stmt

  op mapVarDecl (fe : CExp -> CExp, ft : CType -> CType) ((id, t) : CVarDecl)    
    : CVarDecl = 
    (id, mapType ft t)

  op mapVarDecl1 (fe : CExp -> CExp, ft : CType -> CType) ((id, t, optexp) : CVarDecl1)   
    : CVarDecl1 = 
    (id, 
     mapType ft t, 
     case optexp of 
       | None -> None 
       | Some e -> Some (mapExp2 (fe,ft) e))

  op mapFnDecl (fe : CExp -> CExp, ft : CType -> CType) ((id, ts, t) : CFnDecl)     
    : CFnDecl = 
    (id, map (mapType ft) ts, mapType ft t)

  op mapTypeDefn   (fe : CExp -> CExp, ft : CType -> CType) ((id, t): CTypeDefn)   
    : CTypeDefn = 
    (id, mapType ft t)

  op mapStructDefn (fe : CExp -> CExp, ft : CType -> CType) ((id, decls) : CStructDefn) 
    : CStructDefn = 
    (id, map (mapVarDecl (fe,ft)) decls)

  op mapUnionDefn  (fe : CExp -> CExp, ft : CType -> CType) ((id, decls) : CUnionDefn)
    : CUnionDefn = 
    (id, map (mapVarDecl (fe,ft)) decls)

  op mapVarDefn (fe : CExp -> CExp, ft : CType -> CType) ((id, t, e) : CVarDefn)
    : CVarDefn = 
    (id, mapType ft t, mapExp2 (fe,ft) e)

  op mapFnDefn (fe : CExp -> CExp, ft : CType -> CType) ((id, decls, t, stmt) : CFnDefn)
    : CFnDefn = 
    (id, 
     map (mapVarDecl (fe,ft)) decls,
     mapType ft t,
     mapStmt (fe,ft) stmt)

  op mapStructUnionTypeDefn (fe : CExp -> CExp, ft : CType -> CType) (sut : CStructUnionTypeDefn) 
    : CStructUnionTypeDefn =
    case sut of
      | CStruct   s -> CStruct   (mapStructDefn (fe,ft) s)
      | CUnion    u -> CUnion    (mapUnionDefn  (fe,ft) u)
      | CTypeDefn t -> CTypeDefn (mapTypeDefn   (fe,ft) t)

  % --------------------------------------------------------------------------------

  op getHeaderCSpec (cspc : CSpec) : CSpec =
    %% vars will be printed as "extern"
    %% varDefns will be printed as "extern"
    %% fnDefns will be printed as "extern"
    cspc << {axioms = []}

  op getImplCSpec (cspc : CSpec) : CSpec =
    {
     name                 = cspc.name,
     includes             = [],
     defines              = [],
     constDefns           = [],
     vars                 = cspc.vars,
     fns                  = [],
     axioms               = cspc.axioms,
     structUnionTypeDefns = [],
     varDefns             = cspc.varDefns,
     fnDefns              = cspc.fnDefns
    }

  % --------------------------------------------------------------------------------

  % this removes void* typedefs in a cspec, if the same typename is defined at another place
  % in the spec
  op removePtrVoidTypeDefs (cspc : CSpec) : CSpec =
    let suts = cspc.structUnionTypeDefns in
    let suts = foldl (fn (suts, sut) ->
                        case sut of

                          | CTypeDefn (tname, CPtr CVoid) ->
                            (case findLeftmost (fn |CTypeDefn (tname1,_) -> (tname1=tname) | _ -> false) suts of
                               | Some _ -> suts
                               | _ -> suts ++ [sut])

                          | _ -> 
                            suts ++ [sut])
                     []
                     suts
    in
    setStructUnionTypeDefns (cspc, suts)

  % --------------------------------------------------------------------------------

  % finds the typedef for a given type
  op findTypeDefn (cspc : CSpec, typ : CType) : Option String =
    let typedefns = cspc.structUnionTypeDefns in
    let 
      def findTypeDefn0 typedefns =
	case typedefns of

	  | (CTypeDefn (s,type0)) :: typedefns ->
	    if type0 = typ then 
              Some s
	    else 
              findTypeDefn0(typedefns)

	  | _ :: typedefns -> findTypeDefn0 typedefns

	  | _ -> None
    in
    findTypeDefn0 typedefns

  op findTypeDefnInCSpecs (cspcl : List CSpec, typ : CType) : Option String =
    case cspcl of
      | [] -> None
      | cspc::cspcl -> 
        case findTypeDefn(cspc,typ) of
          | Some x -> Some x
          | _ -> findTypeDefnInCSpecs (cspcl, typ)

  % --------------------------------------------------------------------------------

  op findStructUnionTypeDefn (cspc : CSpec, typ : CType) : Option CStructUnionTypeDefn =
    case typ of
      | CBase   n -> findLeftmost (fn |(CTypeDefn (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | CStruct n -> findLeftmost (fn |(CStruct   (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | CUnion  n -> findLeftmost (fn |(CUnion    (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | _ -> None

  op structUnionTypeDefnGT (cspc : CSpec) (sut1 : CStructUnionTypeDefn, sut2 : CStructUnionTypeDefn) : Bool =
    let deps2 = structUnionTypeDefnDepends (cspc, sut2) in
    let t1    = structUnionTypeDefnToType sut1 in
    t1 nin? deps2

  op sortStructUnionTypeDefns (cspc : CSpec) : CSpec =
    let suts = cspc.structUnionTypeDefns               in
    let suts = qsort (structUnionTypeDefnGT cspc) suts in
    setStructUnionTypeDefns (cspc, suts)

  op structUnionTypeDefnToType (sut : CStructUnionTypeDefn) : CType =
    case sut of
      | CTypeDefn (n,_) -> CBase   n
      | CStruct   (s,_) -> CStruct s
      | CUnion    (u,_) -> CUnion  u

  op structUnionTypeDefnDepends (cspc : CSpec, sutdef : CStructUnionTypeDefn) : CTypes =
    case sutdef of
     %| CTypeDefn (n,CPtr(_))     -> typeDepends (cspc, CBase   n, [])
      | CTypeDefn (n,CFn(tys,ty)) -> typeDepends (cspc, CBase   n, tys++[ty])
      | CTypeDefn (n,t)           -> typeDepends (cspc, CBase   n, [t])
      | CStruct   (s,fields)      -> typeDepends (cspc, CStruct s, map (fn (_,t) -> t) fields)
      | CUnion    (u,fields)      -> typeDepends (cspc, CUnion  u, map (fn (_,t) -> t) fields)

  op getSubTypes (t : CType) : CTypes =
    case t of

      | CFn (tys, ty) -> 
        foldl (fn (res, t) -> 
                 res ++ getSubTypes t) 
              (getSubTypes ty)
              tys

      | _ -> []

  op typeDepends (cspc : CSpec, _ : CType, types : CTypes) : CTypes =
    let
      def typeDepends0 (t, deps) =
	if t in? deps then 
          deps
	else
	  case findStructUnionTypeDefn (cspc, t) of

            | Some (CTypeDefn (n, t1)) -> 
              typeDepends0 (t1, CBase n :: deps)

            | Some (CStruct (s, fields)) ->
              let deps  = CStruct s :: deps in
              let types = map (fn (_, t) -> t) fields in
              foldl (fn (deps, t) -> typeDepends0 (t, deps)) deps types

            | Some (CUnion (u, fields)) ->
              let deps  = CUnion u :: deps in
              let types = map (fn (_, t) -> t) fields in
              foldl (fn (deps, t) -> typeDepends0 (t, deps)) deps types

            | _ -> deps
    in
    foldl (fn (deps, t) -> typeDepends0 (t, deps)) [] types
    
  % --------------------------------------------------------------------------------

  % identifies equal structs and unions by inserting defines. This
  % is necessary, because in C structs/unions with the same fields
  % aren't the same.
  op identifyEqualStructsUnions (cspc : CSpec) : CSpec =
    let
      def processStructUnion (cspc : CSpec, sut : CStructUnionTypeDefn) is
        let suts = cspc.structUnionTypeDefns in
        if sut nin? suts then 
          cspc 
        else
	  case sut of

	    | CTypeDefn _ -> cspc

	    | CStruct (id,fields) ->
	      (case findLeftmost (fn sut ->
                                    case sut of
                                      | CStruct (id0,fields0) ->
                                        (id0 ~= id) && (equalVarDecls cspc (fields0,fields))
                                      | _ -> false) 
                                 suts 
                 of
		 | Some (CStruct (id0,_)) ->
		   let suts = filter (fn | CStruct(id1,_) -> (id1 ~= id0)
                                         | _ -> true) 
                                     suts
		   in
		   %let _ = writeLine("identifying structs \""^id^"\" and \""^id0^"\"") in
		   let cspc = setStructUnionTypeDefns(cspc,suts) in
		   let cspc = addDefine(cspc,id0^" "^id) in
		   let cspc = mapCSpec (fn e -> e,
                                        fn t ->
                                          case t of
                                            | CStruct id1 -> if id1=id0 then CStruct id else t
                                            | _ -> t)
                                       cspc
		   in
		   cspc

		 | None -> 
		   %let _ = writeLine("struct \""^id^"\": no identical structs found.") in
		   cspc)

	    | CUnion (id, fields) ->
	      (case findLeftmost (fn sut ->
                                    case sut of
                                      | CUnion (id0,fields0) ->
                                        (id0 ~= id) && (equalVarDecls cspc (fields0,fields))
                                      | _ -> false) 
                                 suts
                 of

                 | Some (CUnion (id0,_)) ->
		   let suts = filter (fn  | CUnion(id1,_) -> id1 ~= id0
					  | _ -> true) 
                                     suts
		   in
		   %let _ = writeLine("identifying unions \""^id^"\" and \""^id0^"\"") in
		   let cspc = setStructUnionTypeDefns (cspc, suts) in
		   let cspc = addDefine (cspc, id0 ^ " " ^ id)     in
		   let cspc = mapCSpec (fn e -> e,
                                        fn t ->
                                          case t of
                                            | CUnion id1 -> if id1=id0 then CUnion id else t
                                            | _ -> t)
                                       cspc
		   in
		   cspc

		 | None -> 
		   %let _ = writeLine("union \""^id^"\": no identical unions found.") in
		   cspc)
      in
      let
        def identifyRec cspc =
	  let suts  = cspc.structUnionTypeDefns in
	  let cspc0 = foldl (fn (cspc, sut) -> processStructUnion (cspc, sut)) cspc suts in
	  if cspc0 = cspc then cspc else identifyRec cspc0
      in
      let cspc = identifyRec cspc in
      setStructUnionTypeDefns (cspc, mkUnique (cspc. structUnionTypeDefns))

  % --------------------------------------------------------------------------------

  op unfoldType (cspc : CSpec, typ : CType) : CType =
    mapType (fn t ->
               case t of
                 | CBase tid -> 
                   (case findLeftmost (fn sut ->
                                         case sut of
                                           | CTypeDefn (tid0, _) -> tid = tid0
                                           | _ -> false) 
                                      cspc.structUnionTypeDefns 
                      of
                      | Some (CTypeDefn (_, tx)) -> tx
                      | None -> t)
                 | _ -> t)
            typ

  % equality modulo typedefns
  op ctypeEqual (cspc : CSpec) (t1 : CType, t2 : CType) : Bool =
    let t1 = unfoldType (cspc, t1) in
    let t2 = unfoldType (cspc, t2) in
    t1 = t2

  op equalVarDecl (cspc : CSpec) ((id1, t1) : CVarDecl, (id2, t2) : CVarDecl) : Bool =
    if id1=id2 then ctypeEqual cspc (t1,t2) else false

  op equalVarDecls (cspc : CSpec) (decls1 : CVarDecls, decls2 : CVarDecls) :Bool =
    case (decls1,decls2) of

      | ([],[]) -> true

      | (decl1::decls1, decl2::decls2) ->
        if equalVarDecl cspc (decl1,  decl2) then 
          equalVarDecls cspc (decls1, decls2)
	else 
          false

      | _ -> 
        false

  op [X] mkUnique (l : List X) : List X  =
    foldr (fn (e,l) -> if e in? l then l else e::l) [] l


  op [X] qsort (gt : X*X->Bool) (l : List X) : List X =
    let
      def split(x,l) =
	case l of
	  | [] -> ([],[])
	  | y::l -> 
            let (l1,l2) = split(x,l) in
	    if gt (y,x) then
              (l1, y::l2)
	    else 
              (y::l1, l2)
    in
    case l of
      | []   -> []
      | [x]  -> [x]
      | x::l -> 
        let (l1,l2) = split(x,l) in
	let l1 = qsort gt l1 in
	let l2 = qsort gt l2 in
	l1 ++ (x::l2)


  % --------------------------------------------------------------------------------

  op ctypeToString (t : CType) : String =
    let p   = ppPlainType t  in
    let txt = format (80, p) in
    toString txt

  % --------------------------------------------------------------------------------

  op freeVarsExp (fvs : List String, exp : CExp) : List String =
    case exp of
      | CVar       (v,_)      -> if v in? fvs then fvs else v::fvs
      | CApply     (e1,exps)  -> foldl (fn (fvs0, exp) ->
                                          freeVarsExp (fvs0, exp)) 
                                       (freeVarsExp (fvs, e1)) 
                                       exps
      | CUnary     (_,exp)    -> freeVarsExp (fvs, exp)
      | CBinary    (_,e1,e2)  -> freeVarsExp (freeVarsExp (fvs, e1), e2)
      | CCast      (_,e)      -> freeVarsExp (fvs, e)
      | CStructRef (e,_)      -> freeVarsExp (fvs, e)
      | CUnionRef  (e,_)      -> freeVarsExp (fvs, e)
      | CArrayRef  (e1,e2)    -> freeVarsExp (freeVarsExp (fvs,e1), e2)
      | CIfExp     (e1,e2,e3) -> freeVarsExp (freeVarsExp (freeVarsExp (fvs, e1), e2), e3)
      | CComma     (e1,e2)    -> freeVarsExp (freeVarsExp (fvs,e1), e2)
      | CSizeOfExp (e)        -> freeVarsExp (fvs,e)
      | CField     exps       -> foldl (fn (fvs0, exp) -> 
                                          freeVarsExp(fvs0,exp)) 
                                       fvs 
                                       exps
      | _ -> fvs

  op freeVarsStmt (fvs : List String, stmt : CStmt, rec? : Bool) : List String = 
    case stmt of

      | CExp    e         -> freeVarsExp (fvs, e)

      | CBlock  b         -> if rec? then 
                               freeVarsBlock (fvs, b, rec?) 
                             else 
                               fvs

      | CIf     (e,s1,s2) -> let fvs0 = freeVarsExp (fvs, e) in
                             if rec? then 
                               freeVarsStmt (freeVarsStmt (fvs0, s1, rec?), s2, rec?)
                             else 
                               fvs0

      | CReturn e         -> freeVarsExp (fvs, e)

      | CWhile  (e,s)     -> let fvs0 = freeVarsExp (fvs, e) in
                             if rec? then 
                               freeVarsStmt (fvs0, s, rec?)
                             else 
                               fvs0

      | CIfThen (e,s)     -> let fvs0 = freeVarsExp (fvs, e) in
                             if rec? then 
                               freeVarsStmt (fvs0, s, rec?)
                             else 
                               fvs0

      | CSwitch (e,stmts) -> let fvs0 = freeVarsExp (fvs, e) in
                             if rec? then 
                               freeVarsStmts (fvs0, stmts, rec?)
                             else
                               fvs0

      | _ -> fvs

  op freeVarsStmts (fvs : List String, stmts : CStmts, rec? : Bool) : List String =
    foldl (fn (fvs0, stmt) -> 
             freeVarsStmt (fvs0, stmt, rec?)) 
          fvs 
          stmts

  op freeVarsBlock (fvs : List String, block as (decls,stmts) : CBlock, rec? : Bool)
    : List String =
    case decls of

      | [] -> freeVarsStmts (fvs, stmts, rec?)

      | (v, _, optexp) :: decls ->
        let fvs0 = case optexp of
                     | Some e -> freeVarsExp (fvs, e)
                     | None -> fvs
	in
	let fvs1 = freeVarsBlock (fvs, (decls, stmts), rec?) in
	let fvs1 = filter (fn v0 -> v0 ~= v && v0 nin? fvs0) fvs1 in
	fvs0 ++ fvs1

  op freeVars         (b : CBlock) : List String = freeVarsBlock ([], b, true)
  op freeVarsToplevel (b : CBlock) : List String = freeVarsBlock ([], b, false)

  op showFreeVars (b : CBlock) : () =
    let fvs = freeVars b in
    let s   = foldl (fn (s,v) -> if s = "" then v else v^","^s) "" fvs in
    writeLine ("freeVars: ["^s^"]")

  % auxiliary op for moving decls to the innermost block:
  % counts the number of direct sub-blocks of stmts that contain the
  % given variable freely. If it's more than 1 than the decl must stay
  % in the outer level otherwise it can be moved further inside the
  % inner block
  op countInnerBlocksWithFreeVar (v : String, stmts : CStmts) : Nat =
    let
      def fvnum fvs =
	if v in? fvs then 1 else 0
    in
    let
      def fvnumStmts (n0, stmts) =
	foldl (fn (n, stmt) -> 
                 fvnum (freeVarsStmt ([], stmt, true)) + n)
              n0
              stmts
    in
    case stmts of
      | [] -> 0
      | stmt :: stmts -> 
        let n = case stmt of
		  | CBlock  b         -> fvnum (freeVarsBlock ([], b, true))
	          | CIf     (_,s1,s2) -> fvnumStmts (0, [s1,s2])
	          | CWhile  (_,s)     -> fvnumStmts (0, [s])
	          | CIfThen (_,s)     -> fvnumStmts (0, [s])
	          | CSwitch (_,s)     -> fvnumStmts (0, s)
	          | _ -> 0
	in
	let m = countInnerBlocksWithFreeVar (v, stmts) in
	n + m

  % called after the countSubBlocksWithFreeVar has returned 1 for the variable
  % it moves the vardecl to the first inner block where it occurs as free variable
  op moveDeclToInnerBlock (decl as (v,_,_) : CVarDecl1, stmts : CStmts) 
    : CStmts =
    let
      def moveDeclStmts stmts =
	case stmts of

	  | [] -> ([],false)

	  | stmt::stmts ->
	    let fvs = freeVarsStmt ([], stmt, true) in
	    if v in? fvs then 
	      let stmt = prependDecl (decl, stmt) in
	      let stmt = case stmt of
			   | CBlock b -> CBlock (findBlockForDecls b)
	                   | _ -> stmt
	      in
	      (stmt :: stmts, true)
	    else
	      let (stmts, added?) = moveDeclStmts stmts in
	      (stmt :: stmts, added?)
    in
    case stmts of
      | [] -> [] % should not happen
      | stmt :: stmts ->
        let (stmt,added?) =
            case stmt of
              | CBlock  (b as (decls,stmts)) -> if v in? freeVarsBlock([],b,true) then
                                                  let b = (decl::decls, stmts) in 
                                                  let b = findBlockForDecls b    in
                                                  (CBlock b, true) 
                                                else 
                                                  (stmt, false)
              | CIf     (e,s1,s2) -> let ([s1,s2],added?) = moveDeclStmts([s1,s2]) in (CIf     (e,s1,s2), added?)
              | CWhile  (e,s)     -> let ([s],added?)     = moveDeclStmts([s])     in (CWhile  (e,s),     added?)
              | CIfThen (e,s)     -> let ([s],added?)     = moveDeclStmts([s])     in (CIfThen (e,s),     added?)
              | CSwitch (e,stmts) -> let (stmts,added?)   = moveDeclStmts(stmts)   in (CSwitch (e,stmts), added?)
              | _ -> (stmt,false)
	in
	if added? then
	  stmt::stmts
	else
	  let stmts = moveDeclToInnerBlock (decl, stmts) in
	  stmt::stmts


  op findBlockForDecls (block as (decls,stmts) : CBlock) : CBlock =
    case decls of
      | [] -> ([], stmts)
      | decl::decls -> findBlockForDecl (decl, (decls, stmts))


  op findBlockForDecl (decl as (v,typ,optexp) : CVarDecl1, b as (decls,stmts) : CBlock)
    : CBlock =
    let
      def dontMoveDecl () =
	let (decls, stmts) = findBlockForDecls b in
	(decl::decls, stmts)
    in
    let fvtl = freeVarsToplevel b in
    if v in? fvtl then
      dontMoveDecl ()
    else
      let cnt = countInnerBlocksWithFreeVar (v, stmts) in
      if cnt = 1 then
	let stmts = moveDeclToInnerBlock (decl, stmts) in
	let newblock = (decls, stmts) in
	findBlockForDecls newblock
      else
	dontMoveDecl ()

  % --------------------------------------------------------------------------------

  op NULL : CExp = CVar("NULL",CInt)

  % --------------------------------------------------------------------------------

  % splits the cspc into header and implementation cspcs
  op splitCSpec (cspc : CSpec) : CSpec * CSpec =
    let
      def filterFnDefn isHdr (fndefn as (fname,_,_,_)) =
	isHdr = exists? (fn c -> c = #_) fname
    in
    let hdr = cspc << {axioms  = [],
                       fnDefns = filter (filterFnDefn true) cspc.fnDefns}
    in
    let cspc = {
                name                 = cspc.name,
                includes             = [],
                defines              = [],
                constDefns           = [],
                vars                 = [],
                fns                  = [],
                structUnionTypeDefns = [],
                varDefns             = [],
                axioms               = cspc.axioms,
                fnDefns              = filter (filterFnDefn false) cspc.fnDefns
                }
    in
    (hdr,cspc)


  % --------------------------------------------------------------------------------

  op deleteUnusedTypes (cspc : CSpec) : CSpec =
    let usedtypes = usedCTypes cspc in
    let suts = filter (fn (CTypeDefn (n,_)) -> CBase   n in? usedtypes
		        | (CStruct   (n,_)) -> CStruct n in? usedtypes
		        | (CUnion    (n,_)) -> CUnion  n in? usedtypes)
                      cspc.structUnionTypeDefns
    in
    setStructUnionTypeDefns (cspc, suts)

  % --------------------------------------------------------------------------------

  op usedCTypes (cspc : CSpec) : List CType =
    let types = (flatten (map usedCTypesFnDefn  cspc.fnDefns))             in
    let types = (flatten (map usedCTypesVarDefn cspc.varDefns))   ++ types in
    let types = (flatten (map usedCTypesVarDefn cspc.constDefns)) ++ types in
    let types = (flatten (map usedCTypesVarDecl cspc.vars))       ++ types in
    let types = (flatten (map usedCTypesFnDecl  cspc.fns))        ++ types in
    let types = mkUnique types                                             in
    let types = flatten (map (usedCTypesType cspc []) types)               in
    let types = mkUnique types                                             in
    types

  op usedCTypesFnDefn ((_,vdecls,rtype,stmt) : CFnDefn) : List CType =
    let types = flatten (map usedCTypesVarDecl vdecls) in
    let types = rtype::types in
    let types = (usedCTypeStmt stmt) ++ types in
    types

  op usedCTypesFnDecl   ((_,ptypes,rtype) : CFnDecl)   : List CType = rtype::ptypes
  op usedCTypesVarDefn  ((_,t,_)          : CVarDefn)  : List CType = [t]
  op usedCTypesVarDecl  ((_,t)            : CVarDecl)  : List CType = [t]
  op usedCTypesVarDecl1 ((_,t,_)          : CVarDecl1) : List CType = [t]

  op usedCTypeStmt (stmt : CStmt) : List CType =
    case stmt of

      | CBlock(vdecls1,stmts) ->
        let types = flatten (map usedCTypesVarDecl1 vdecls1) in
	let types = (flatten (map usedCTypeStmt stmts)) ++ types in
	types

      | CIf     (_,s1,s2) -> usedCTypeStmt s1 ++ usedCTypeStmt s2

      | CWhile  (_,s)     -> usedCTypeStmt s

      | CIfThen (_,s)     -> usedCTypeStmt s

      | CSwitch (_,stmts) -> flatten (map usedCTypeStmt stmts)

      | _ -> []

  op usedCTypesType (cspc : CSpec) (visited : List CType) (t : CType) : List CType =
    let
      def usedTypes4SUT t =
	case findStructUnionTypeDefn (cspc, t) of
	  | Some (CTypeDefn (_,t))      -> [t]
	  | Some (CUnion    (_,vdecls)) -> flatten (map usedCTypesVarDecl vdecls)
	  | Some (CStruct   (_,vdecls)) -> flatten (map usedCTypesVarDecl vdecls)
	  | _ -> []
    in
    let newtypes =
      case t of
	| CPtr           t            -> [t]
	| CArray         t            -> [t]
	| CBase          _            -> usedTypes4SUT t
	| CStruct        _            -> usedTypes4SUT t
	| CUnion         _            -> usedTypes4SUT t
	| CArrayWithSize (_,t)        -> [t]
	| CFn            (types, typ) -> typ::types
	| _ -> []
    in
    let newtypes = filter (fn t -> t nin? visited) newtypes in
    let visited = visited ++ newtypes in
    t :: flatten (map (usedCTypesType cspc visited) newtypes)

  % --------------------------------------------------------------------------------

  op prependBlockStmt (block : CBlock, stmt : CStmt) : CStmt =
    case block of
      | ([],[]) -> stmt
      | (decls,stmts) ->
        case stmt of

	  | CBlock (decls1,        stmts1) -> 
            CBlock (decls++decls1, stmts++stmts1)

	  | _ -> CBlock (decls, stmts++[stmt])

}
