(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

CUtils qualifying spec
{
 import C
 import CPrint
 import /Languages/MetaSlang/Specs/Printer

 op emptyCSpec (name : String) : C_Spec =
  {
   name                 = name,
   headers              = [],
   trailers             = [],
   hincludes            = [],
   cincludes            = [],
   hverbatims           = [],
   cverbatims           = [],
   defines              = [],
   constDefns           = [],
   vars                 = [],
   fns                  = [],
   structUnionTypeDefns = [],
   axioms               = [],
   varDefns             = [],
   fnDefns              = []
   }


 op renameCSpec             (cspc : C_Spec, X : String)                 : C_Spec = cspc << {name                 = cString X}                       
 op addHeader               (cspc : C_Spec, X : String)                 : C_Spec = cspc << {headers              = cspc.headers              ++ [X]}
 op addTrailer              (cspc : C_Spec, X : String)                 : C_Spec = cspc << {trailers             = cspc.trailers             ++ [X]}
 op addHInclude             (cspc : C_Spec, X : String)                 : C_Spec = cspc << {hincludes            = cspc.hincludes            ++ [X]}
 op prefixCInclude          (cspc : C_Spec, X : String)                 : C_Spec = cspc << {cincludes            = [X]            ++ cspc.cincludes}
 op addCInclude             (cspc : C_Spec, X : String)                 : C_Spec = cspc << {cincludes            = cspc.cincludes            ++ [X]}
 op addHVerbatim            (cspc : C_Spec, X : String)                 : C_Spec = cspc << {hverbatims           = cspc.hverbatims           ++ [X]}
 op addCVerbatim            (cspc : C_Spec, X : String)                 : C_Spec = cspc << {cverbatims           = cspc.cverbatims           ++ [X]}
 op addDefine               (cspc : C_Spec, X : C_Define)               : C_Spec = cspc << {defines              = cspc.defines              ++ [X]}
 op addConstDefn            (cspc : C_Spec, X : C_VarDefn)              : C_Spec = cspc << {constDefns           = cspc.constDefns           ++ [X]}
 op addVar                  (cspc : C_Spec, X : C_VarDecl)              : C_Spec = cspc << {vars                 = cspc.vars                 ++ [X]}
 op setStructUnionTypeDefns (cspc : C_Spec, X : C_StructUnionTypeDefns) : C_Spec = cspc << {structUnionTypeDefns = X}
 op addEnumDefn             (cspc : C_Spec, X : C_EnumDefn)             : C_Spec = cspc << {structUnionTypeDefns = cspc.structUnionTypeDefns ++ [Enum   X]}
 op addStructDefn           (cspc : C_Spec, X : C_StructDefn)           : C_Spec = cspc << {structUnionTypeDefns = cspc.structUnionTypeDefns ++ [Struct X]}
 op addUnionDefn            (cspc : C_Spec, X : C_UnionDefn)            : C_Spec = cspc << {structUnionTypeDefns = cspc.structUnionTypeDefns ++ [Union  X]}
 op addAxiom                (cspc : C_Spec, X : C_Exp)                  : C_Spec = cspc << {axioms               = cspc.axioms               ++ [X]}
 op addVarDefn              (cspc : C_Spec, X : C_VarDefn)              : C_Spec = cspc << {varDefns             = cspc.varDefns             ++ [X]}

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
  
 op addFn (cspc : C_Spec, X as (fname,_,_) : C_FnDecl) : C_Spec =
  if fname in? SWC_Common_Macros then
    cspc
  else
    let other_fns = filter (fn(fname0,_,_) -> fname0 ~= fname) cspc.fns in
    cspc << {fns = other_fns ++ [X]}

 op delFn (cspc : C_Spec, fname : String) : C_Spec =
  let other_fns = filter (fn(fname0,_,_) -> fname0 ~= fname) cspc.fns in
  cspc << {fns = other_fns}
 
 op addTypeDefn (cspc : C_Spec, X as (tname,tdef) : C_TypeDefn) : C_Spec =
  let other_typedefs = filter (fn (Type (tname0,_)) -> tname0 ~= tname | _ -> true) 
                              cspc.structUnionTypeDefns 
  in
  cspc << {structUnionTypeDefns = other_typedefs ++ [Type X]}

 op addFnDefnAux (cspc : C_Spec, fndefn as (fname,params,rtype,body) : C_FnDefn, overwrite? : Bool)
  : C_Spec =
  let other_defs = if overwrite? then
                     filter (fn(fname0,_,_,_) -> fname ~= fname0) cspc.fnDefns
                   else 
                     cspc.fnDefns
  in 
  cspc << {fnDefns = other_defs ++ [fndefn]}

 op addFnDefn          (cspc : C_Spec, fndefn : C_FnDefn) : C_Spec = addFnDefnAux(cspc, fndefn, true)
 op addFnDefnOverwrite (cspc : C_Spec, fndefn : C_FnDefn) : C_Spec = addFnDefnAux(cspc, fndefn, true)

 % --------------------------------------------------------------------------------

 op getStructDefns (cspc : C_Spec) : C_StructDefns =
  foldl (fn (structs, su) ->
           case su of
             | Struct X -> structs ++ [X]
             | _ -> structs)
        [] 
        cspc.structUnionTypeDefns

 op getUnionDefns (cspc : C_Spec) : C_UnionDefns =
  foldl (fn (unions, su) ->
           case su of
             | Union X -> unions ++ [X]
             | _ -> unions)
        []
        cspc.structUnionTypeDefns

 op getTypeDefns (cspc : C_Spec) : C_TypeDefns =
  foldl (fn (typedefns, su) ->
           case su of
             | Type X -> typedefns ++ [X]
             | _ -> typedefns)
        []
        cspc.structUnionTypeDefns

 % --------------------------------------------------------------------------------

 (*
  * adds a new type definition to cspc; definition in xcspc are
  * also searched (for incremental code generation)
  *)

 op addNewTypeDefn (cspc                : C_Spec, 
                    xcspc               : C_Spec, 
                    tdef as (tname,typ) : C_TypeDefn) 
  : C_Spec * C_Type =
  case findTypeDefnInCSpecs ([cspc,xcspc], typ) of
    | Some s -> (cspc,                   C_Base (s,     Type))
    | None   -> (addTypeDefn(cspc,tdef), C_Base (tname, Type))

 % --------------------------------------------------------------------------------

 % only add the struct definition, if it is new, i.e. if now other
 % struct definition exists in the cspec that has the same fields
 % returns the struct definition that contains the same fields as
 % the input struct definition.

 op addNewStructDefn (cspc : C_Spec, xcspc : C_Spec, (sname, sfields) : C_StructDefn) 
  : C_Spec * C_Type =
  let structs  = getStructDefns cspc  in
  let xstructs = getStructDefns xcspc in
  let (cspc, struct) = 
      case findLeftmost (fn (sname0,sfields0) -> sfields = sfields0) (structs ++ xstructs) of
    
        | Some (sname,_) -> 
          (cspc, C_Base (sname, Struct))
          
        | None -> 
          let cspc = addStructDefn (cspc, (sname,sfields)) in
          (cspc, C_Base (sname, Struct))
  in
  let typ = case findTypeDefnInCSpecs ([cspc,xcspc], struct) of
              | Some s -> C_Base (s, Struct)
              | None -> struct
  in
  (cspc,typ)

 op addNewUnionDefn (cspc             : C_Spec, 
                     xcspc            : C_Spec, 
                     (sname, sfields) : C_UnionDefn)
  : C_Spec * C_Type =
  let unions  = getUnionDefns cspc  in
  let xunions = getUnionDefns xcspc in
  case findLeftmost (fn (sname0,sfields0) -> sfields = sfields0) (unions ++ xunions) of

    | Some (sname,_) -> 
      (cspc, C_Base (sname, Union))
      
    | _ ->
      let cspc = addUnionDefn (cspc, (sname,sfields)) in
      (cspc, C_Base (sname, Union))

 % --------------------------------------------------------------------------------

 op addStmts (stmt1 : C_Stmt, stmts2 : C_Stmts) : C_Stmt =
  case stmt1 of
    
    | C_Block (decls, stmts) -> 
      C_Block (decls, stmts ++ stmts2)
      
    | _ -> 
      C_Block ([],    [stmt1]++stmts2)
     
 % --------------------------------------------------------------------------------

 op prependDecl (decl : C_VarDecl1, stmt : C_Stmt) : C_Stmt =
  case stmt of
    
    | C_Block (decls,       stmts) -> 
      C_Block (decl::decls, stmts)
      
    | _ -> 
      C_Block ([decl],      [stmt])
      
 % --------------------------------------------------------------------------------

 op mkBlock (stmt : C_Stmt) : C_Block =
  case stmt of
    | C_Block (decls, stmts) -> (decls, stmts)
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

 op mergeCSpecs (cspcs : List C_Spec) : C_Spec =
  case cspcs of
    | []     -> emptyCSpec ""
    | [cspc] -> cspc
    | cspc1 :: cspc2 :: cspcs ->
      let cspc =
          {
           name                 = cspc1.name,
           headers              = cspc1.headers  ++ cspc2.headers,
           trailers             = cspc1.trailers ++ cspc2.trailers,
           hincludes            = concatnewEq (cspc1. hincludes,  cspc2.hincludes),
           cincludes            = concatnewEq (cspc1. cincludes,  cspc2.cincludes),
           cverbatims           = cspc1.hverbatims ++ cspc2.hverbatims,
           hverbatims           = cspc1.cverbatims ++ cspc2.cverbatims,
           defines              = concatnewEq (cspc1. defines,    cspc2.defines),
           constDefns           = concatnewEq (cspc1. constDefns, cspc2.constDefns),
           vars                 = concatnew (fn ((var1,_),      (var2,_))       -> var1=var2)     (cspc1.vars,    cspc2.vars),
           fns                  = concatnew (fn ((fname1,_,_),  (fname2,_,_))   -> fname1=fname2) (cspc1.fns,     cspc2.fns),
           structUnionTypeDefns = foldr (fn | (x as Type (tname,_),res) -> 
                                           (filter (fn (Type (tname0,_)) -> tname0 ~= tname | _ -> true) res) ++ [x]
                                         | (x,res) -> 
                                           res ++ [x])
                                        cspc2.structUnionTypeDefns
                                        cspc1.structUnionTypeDefns,
           axioms               = concatnewEq (cspc1. axioms,     cspc2.axioms),
           varDefns             = concatnewEq (cspc1. varDefns,   cspc2.varDefns),
           fnDefns              = concatnew (fn ((fname1,_,_,_),(fname2,_,_,_)) -> fname1=fname2) (cspc1.fnDefns, cspc2.fnDefns)
           }
      in
      mergeCSpecs (cspc :: cspcs)

 op printCType (t : C_Type) : String =
  let pr  = ppType (t, prettysNone[]) in
  let txt = format (80, pr) in
  toString txt

 op printCTypes (sep : String) (types : List C_Type) : String =
  foldl (fn (s,t) -> s ^ sep ^ printCType t) "" types

 type Destination = | File | Terminal | String

 op printCSpecToX (cspc : C_Spec, fname : String, asHeader : Bool, X : Destination) : String =
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

 op printCSpecToFile (cspc : C_Spec, fname : String) : () =
  %let fname = getImplFilename(cspc.name) in
  let _ = printCSpecToX (cspc, fname, false, File) in
  ()

 op printCSpecToFileEnv (cspc : C_Spec, fname : String) : SpecCalc.Env () =
  let _ = printCSpecToFile (cspc, fname) in
  return ()

 op printCSpecToTerminal (cspc : C_Spec) : () = 
  let _ = printCSpecToX (cspc, "", false, Terminal) in
  ()

 op printCSpecToString (cspc : C_Spec) : String = 
  printCSpecToX (cspc, "", false, String)

 op printCSpecAsHeaderToFile (cspc : C_Spec, fname : String) : () = 
  % let xfname = getHeaderFilename (cspc.name) in
  let _ = printCSpecToX (cspc, fname, true, File) in
  ()

 op printCSpecAsHeaderToTerminal (cspc : C_Spec) : () = 
  let _ = printCSpecToX (cspc, "", true, Terminal) in
  ()

 op printCSpecAsHeaderToString   (cspc : C_Spec) : String = 
  printCSpecToX (cspc, "", true, String)
  
 op getHeaderFilename (fname : String) : String = fname ^ ".h"
 op getImplFilename   (fname : String) : String = fname ^ ".c"

 % --------------------------------------------------------------------------------

 op cString (id : String) : String = 
  let id = map cChar id in
  if isCKeyword id then 
    id %% cString ("slang_" ^ id)
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
          |  32 -> explode " "
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

 op mapExp (f : C_Exp -> C_Exp) (e : C_Exp) : C_Exp =
  let mp = mapExp f in
  let e  = f e      in
  case e of
    | C_Apply (e,    es) ->
      C_Apply (mp e, map mp es)
      
    | C_Unary (o, e) ->
      C_Unary (o, mp e)
      
    | C_Binary (o, e1,    e2) ->
      C_Binary (o, mp e1, mp e2)
      
    | C_Cast (t, e) ->
      C_Cast (t, mp e)
      
    | C_StructRef (e,    s) ->
      C_StructRef (mp e, s)
      
    | C_UnionRef (e,    s) ->
      C_UnionRef (mp e, s)
      
    | C_ArrayRef (e1,    e2) ->
      C_ArrayRef (mp e1, mp e2)
      
    | C_IfExp (e1,    e2,    e3) ->
      C_IfExp (mp e1, mp e2, mp e3)
      
    | C_Comma (e1,    e2) ->
      C_Comma (mp e1, mp e2)
      
    | C_SizeOfExp (e1) ->
      C_SizeOfExp (mp e1)
      
    | C_Field (es) ->
      C_Field (map mp es)
      
    | _ -> e
      
 op mapExp2 (f : C_Exp -> C_Exp, ft : C_Type -> C_Type) (e : C_Exp) : C_Exp =
  let mp = mapExp2 (f,ft) in
  let e  = f e            in
  case e of
    | C_Var decl -> 
      C_Var (mapVarDecl (f,ft) decl)
      
    | C_Fn decl -> 
      C_Fn( mapFnDecl (f,ft) decl)
      
    | C_Apply(e,es) -> 
      C_Apply (mp e,map mp es)
      
    | C_Unary (o, e) -> 
      C_Unary (o, mp e)
      
    | C_Binary (o, e1,    e2) -> 
      C_Binary (o, mp e1, mp e2)
      
    | C_Cast (t, e) -> 
      C_Cast (t, mp e)
      
    | C_StructRef (e,    s) -> 
      C_StructRef (mp e, s)
      
    | C_UnionRef (e,    s) -> 
      C_UnionRef (mp e, s)
      
    | C_ArrayRef (e1,    e2) -> 
      C_ArrayRef (mp e1, mp e2)
      
    | C_IfExp (e1,    e2,    e3) -> 
      C_IfExp (mp e1, mp e2, mp e3)
      
    | C_Comma (e1,    e2) -> 
      C_Comma (mp e1, mp e2)
      
    | C_SizeOfExp e1 -> 
      C_SizeOfExp (mp e1)
      
    | C_SizeOfType t -> 
      C_SizeOfType (ft t)
      
    | C_Field es -> 
      C_Field (map mp es)
      
    | _ -> e

 op substVarInExp (e : C_Exp, id : String, substexp : C_Exp) : C_Exp =
  mapExp (fn e -> 
            case e of
              | C_Var (id0,_) -> if id0 = id then substexp else e
              | _ -> e)
         e

 op mapType (f : C_Type -> C_Type) (t : C_Type) : C_Type =
  let mp = mapType f in
  let t  = f t       in
  case t of

    | C_Ptr t -> 
      C_Ptr (mp t)
      
    | C_Array t -> 
      C_Array (mp t)
      
    | C_ArrayWithSize (n, t) -> 
      C_ArrayWithSize (n, mp t)
      
    | C_Fn (ts,        t) -> 
      C_Fn (map mp ts, mp t)
      
    | _ -> t

 op mapCSpec (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type) (cspc : C_Spec) : C_Spec =
  cspc << {
           constDefns           = map (mapVarDefn             (fe,ft)) cspc.constDefns,
           vars                 = map (mapVarDecl             (fe,ft)) cspc.vars,
           fns                  = map (mapFnDecl              (fe,ft)) cspc.fns,
           structUnionTypeDefns = map (mapStructUnionTypeDefn (fe,ft)) cspc.structUnionTypeDefns,
           axioms               = map (mapExp2                (fe,ft)) cspc.axioms,
           varDefns             = map (mapVarDefn             (fe,ft)) cspc.varDefns,
           fnDefns              = map (mapFnDefn              (fe,ft)) cspc.fnDefns
           }

 op mapStmt (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type) (stmt : C_Stmt) : C_Stmt =
  let mp  = mapStmt (fe,ft) in
  let mpe = mapExp2 (fe,ft) in
  let mpt = mapType ft      in
  case stmt of

    | C_Exp e -> 
      C_Exp (fe e)
      
    | C_Block (decls,                          stmts) -> 
      C_Block (map (mapVarDecl1(fe,ft)) decls, map mp stmts)
      
    | C_If (e,     stmt1,    stmt2) -> 
      C_If (mpe e, mp stmt1, mp stmt2)
      
    | C_Return e -> 
      C_Return (mpe e)
      
    | C_While (e,     stmt) -> 
      C_While (mpe e, mp stmt)
      
    | C_IfThen (e,     stmt) ->
      C_IfThen (mpe e, mp stmt)
      
    | C_Switch (e,     stmts) -> 
      C_Switch (mpe e, map mp stmts)
      
    | _ -> stmt

 op mapVarDecl    (fe : C_Exp  -> C_Exp, ft : C_Type -> C_Type)   ((id, t) : C_VarDecl) 
  : C_VarDecl = 
  (id, mapType ft t)

 op mapVarDecl1   (fe : C_Exp -> C_Exp,  ft : C_Type -> C_Type)   ((id, t, optexp) : C_VarDecl1)   
  : C_VarDecl1 = 
  (id, 
   mapType ft t, 
   case optexp of 
     | None -> None 
     | Some e -> Some (mapExp2 (fe, ft) e))

 op mapFnDecl     (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, ts, t) : C_FnDecl)     
  : C_FnDecl = 
  (id, map (mapType ft) ts, mapType ft t)

 op mapTypeDefn   (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, t) : C_TypeDefn)   
  : C_TypeDefn = 
  (id, mapType ft t)

 op mapStructDefn (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, decls) : C_StructDefn) 
  : C_StructDefn = 
  (id, map (mapVarDecl (fe,ft)) decls)

 op mapUnionDefn  (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, decls) : C_UnionDefn)
  : C_UnionDefn = 
  (id, map (mapVarDecl (fe,ft)) decls)

 op mapVarDefn    (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, t, e) : C_VarDefn)
  : C_VarDefn = 
  (id, mapType ft t, mapExp2 (fe,ft) e)

 op mapFnDefn     (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type)   ((id, decls, t, stmt) : C_FnDefn)
  : C_FnDefn = 
  (id, 
   map (mapVarDecl (fe, ft)) decls,
   mapType ft t,
   mapStmt (fe, ft) stmt)

 op mapStructUnionTypeDefn (fe : C_Exp -> C_Exp, ft : C_Type -> C_Type) (sut : C_StructUnionTypeDefn) 
  : C_StructUnionTypeDefn =
  case sut of
    | Struct x -> Struct (mapStructDefn (fe, ft) x)
    | Union  x -> Union  (mapUnionDefn  (fe, ft) x)
    | Type   x -> Type   (mapTypeDefn   (fe, ft) x)
    | Enum   x -> Enum x

 % --------------------------------------------------------------------------------

 % this removes void* typedefs in a cspec, if the same typename is defined at another place
 % in the spec
 op removePtrVoidTypeDefs (cspc : C_Spec) : C_Spec =
  let suts = cspc.structUnionTypeDefns in
  let suts = foldl (fn (suts, sut) ->
                      case sut of

                        | Type (tname, C_VoidPtr) ->
                          (case findLeftmost (fn | Type (tname1,_) -> (tname1=tname) | _ -> false) suts of
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
 op findTypeDefn (cspc : C_Spec, typ : C_Type) : Option String =
  let typedefns = cspc.structUnionTypeDefns in
  let 
    def findTypeDefn0 typedefns =
      case typedefns of

        | (Type (s,type0)) :: typedefns ->
          if type0 = typ then 
            Some s
          else 
            findTypeDefn0(typedefns)

        | _ :: typedefns -> findTypeDefn0 typedefns

        | _ -> None
  in
  findTypeDefn0 typedefns

 op findTypeDefnInCSpecs (cspcl : List C_Spec, typ : C_Type) : Option String =
  case cspcl of
    | [] -> None
    | cspc::cspcl -> 
      case findTypeDefn(cspc,typ) of
        | Some x -> Some x
        | _ -> findTypeDefnInCSpecs (cspcl, typ)

 % --------------------------------------------------------------------------------

 op findStructUnionTypeDefn (cspc : C_Spec, typ : C_Type) : Option C_StructUnionTypeDefn =
  case typ of
    | C_Base  (n, Type)   -> findLeftmost (fn x -> case x of | (Type   (n0, _)) -> n0 = n | _ -> false) cspc.structUnionTypeDefns
    | C_Base  (n, Struct) -> findLeftmost (fn x -> case x of | (Struct (n0, _)) -> n0 = n | _ -> false) cspc.structUnionTypeDefns
    | C_Base  (n, Union)  -> findLeftmost (fn x -> case x of | (Union  (n0, _)) -> n0 = n | _ -> false) cspc.structUnionTypeDefns
    | C_Base  (n, Enum)   -> findLeftmost (fn x -> case x of | (Enum   (n0, _)) -> n0 = n | _ -> false) cspc.structUnionTypeDefns
    | _ -> None

 op structUnionTypeDefnGT (cspc : C_Spec) (sut1 : C_StructUnionTypeDefn, sut2 : C_StructUnionTypeDefn) : Bool =
  let deps2 = structUnionTypeDefnDepends (cspc, sut2) in
  let t1    = structUnionTypeDefnToType sut1 in
  t1 nin? deps2
 
 op typeStructUnionTypeDefns (cspc : C_Spec) : C_Spec =
  let suts = cspc.structUnionTypeDefns               in
  let suts = quickSort (structUnionTypeDefnGT cspc) suts in
  setStructUnionTypeDefns (cspc, suts)
  
 op structUnionTypeDefnToType (sut : C_StructUnionTypeDefn) : C_Type =
  case sut of
    | Type   (s,_) -> C_Base (s, Type)
    | Struct (s,_) -> C_Base (s, Struct)
    | Union  (s,_) -> C_Base (s, Union)
    | Enum   (s,_) -> C_Base (s, Enum)

 op structUnionTypeDefnDepends (cspc : C_Spec, sutdef : C_StructUnionTypeDefn) : C_Types =
  case sutdef of
   %| C_TypeDefn (n, C_Ptr(_))     -> typeDepends (cspc, C_Base   n, [])
    | Type   (n, C_Fn(tys,ty)) -> 
      typeDepends (cspc, C_Base (n, Type),   tys++[ty])
    | Type   (n, t)            -> 
      typeDepends (cspc, C_Base (n, Type),   [t])

    | Struct (s, fields)       -> typeDepends (cspc, C_Base (s, Struct), map (fn (_,t) -> t) fields)
    | Union  (u, fields)       -> typeDepends (cspc, C_Base (u, Union),  map (fn (_,t) -> t) fields)
    | Enum   (u, fields)       -> typeDepends (cspc, C_Base (u, Enum),   [])
      
 op getSubTypes (t : C_Type) : C_Types =
  case t of
    | C_Fn (tys, ty) -> 
      foldl (fn (res, t) -> 
               res ++ getSubTypes t) 
            (getSubTypes ty)
            tys
    | _ -> []
      
 op typeDepends (cspc : C_Spec, _ : C_Type, types : C_Types) : C_Types =
  let
    def typeDepends0 (t, deps) =
      if t in? deps then 
        deps
      else
        case findStructUnionTypeDefn (cspc, t) of

          | Some (Type (n, t1)) -> 
            typeDepends0 (t1, C_Base (n, Type) :: deps)
            
          | Some (Struct (s, fields)) ->
            let deps  = (C_Base (s, Struct)) :: deps in
            let types = map (fn (_, t) -> t) fields in
            foldl (fn (deps, t) -> typeDepends0 (t, deps)) deps types
            
          | Some (Union (u, fields)) ->
            let deps  = (C_Base (u, Union)) :: deps in
            let types = map (fn (_, t) -> t) fields in
            foldl (fn (deps, t) -> typeDepends0 (t, deps)) deps types
            
          | _ -> deps
  in
  foldl (fn (deps, t) -> typeDepends0 (t, deps)) [] types
    
 % --------------------------------------------------------------------------------

 % identifies equal structs and unions by inserting defines. This
 % is necessary, because in C structs/unions with the same fields
 % aren't the same.
 op identifyEqualStructsUnions (cspc : C_Spec) : C_Spec =
  let
    def processStructUnion (cspc : C_Spec, sut : C_StructUnionTypeDefn) is
      let suts = cspc.structUnionTypeDefns in
      if sut nin? suts then 
        cspc 
      else
        case sut of
          
          | Type _ -> cspc
            
          | Struct (id,fields) ->
            (case findLeftmost (fn sut ->
                                  case sut of
                                    | Struct (id0,fields0) ->
                                      (id0 ~= id) && (equalVarDecls cspc (fields0,fields))
                                    | _ -> false) 
                               suts 
               of
               | Some (Struct (id0,_)) ->
                 let suts = filter (fn | Struct(id1,_) -> (id1 ~= id0)
                                       | _ -> true) 
                                   suts
                 in
                 %let _ = writeLine("identifying structs \""^id^"\" and \""^id0^"\"") in
                 let cspc = setStructUnionTypeDefns(cspc,suts) in
                 let cspc = addDefine (cspc, (id0, id)) in
                 let cspc = mapCSpec (fn e -> e,
                                      fn t ->
                                        case t of
                                          | C_Base (id1, Struct) -> if id1=id0 then C_Base (id, Struct) else t
                                          | _ -> t)
                                     cspc
                 in
                 cspc

               | None -> 
                 %let _ = writeLine("struct \""^id^"\": no identical structs found.") in
                 cspc)

          | Union (id, fields) ->
            (case findLeftmost (fn sut ->
                                  case sut of
                                    | Union (id0,fields0) ->
                                      (id0 ~= id) && (equalVarDecls cspc (fields0,fields))
                                    | _ -> false) 
                               suts
               of
               | Some (Union (id0,_)) ->
                 let suts = filter (fn  | Union(id1,_) -> id1 ~= id0
                                        | _ -> true) 
                                   suts
                 in
                 %let _ = writeLine("identifying unions \""^id^"\" and \""^id0^"\"") in
                 let cspc = setStructUnionTypeDefns (cspc, suts) in
                 let cspc = addDefine (cspc, (id0, id)) in
                 let cspc = mapCSpec (fn e -> e,
                                      fn t ->
                                        case t of
                                          | C_Base (id1, Union) -> if id1=id0 then C_Base (id, Union) else t
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

 op unfoldType (cspc : C_Spec, typ : C_Type) : C_Type =
  mapType (fn t ->
             case t of
               | C_Base (tid, Type) -> 
                 (case findLeftmost (fn sut ->
                                       case sut of
                                         | Type (tid0, _) -> tid = tid0
                                         | _ -> false) 
                                    cspc.structUnionTypeDefns 
                    of
                    | Some (Type (_, tx)) -> tx
                    | None -> t)
               | _ -> t)
          typ

 % equality modulo typedefns
 op ctypeEqual (cspc : C_Spec) (t1 : C_Type, t2 : C_Type) : Bool =
  let t1 = unfoldType (cspc, t1) in
  let t2 = unfoldType (cspc, t2) in
  t1 = t2

 op equalVarDecl (cspc : C_Spec) ((id1, t1) : C_VarDecl, (id2, t2) : C_VarDecl) : Bool =
  if id1=id2 then ctypeEqual cspc (t1,t2) else false

 op equalVarDecls (cspc : C_Spec) (decls1 : C_VarDecls, decls2 : C_VarDecls) :Bool =
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
  foldl (fn (l,e) -> if e in? l then l else e::l) [] l

 op [X] quickSort (gt : X*X->Bool) (l : List X) : List X =
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
      let l1 = quickSort gt l1 in
      let l2 = quickSort gt l2 in
      l1 ++ (x::l2)

 % --------------------------------------------------------------------------------

 op ctypeToString (t : C_Type) : String =
  let p   = ppPlainType t  in
  let txt = format (80, p) in
  toString txt

 % --------------------------------------------------------------------------------

 op freeVarsExp (fvs : List String, exp : C_Exp) : List String =
  case exp of
    | C_Var       (v,_)      -> if v in? fvs then fvs else v::fvs
    | C_Apply     (e1,exps)  -> foldl (fn (fvs0, exp) ->
                                         freeVarsExp (fvs0, exp)) 
                                      (freeVarsExp (fvs, e1)) 
                                      exps
    | C_Unary     (_,exp)    -> freeVarsExp (fvs, exp)
    | C_Binary    (_,e1,e2)  -> freeVarsExp (freeVarsExp (fvs, e1), e2)
    | C_Cast      (_,e)      -> freeVarsExp (fvs, e)
    | C_StructRef (e,_)      -> freeVarsExp (fvs, e)
    | C_UnionRef  (e,_)      -> freeVarsExp (fvs, e)
    | C_ArrayRef  (e1,e2)    -> freeVarsExp (freeVarsExp (fvs,e1), e2)
    | C_IfExp     (e1,e2,e3) -> freeVarsExp (freeVarsExp (freeVarsExp (fvs, e1), e2), e3)
    | C_Comma     (e1,e2)    -> freeVarsExp (freeVarsExp (fvs,e1), e2)
    | C_SizeOfExp (e)        -> freeVarsExp (fvs,e)
    | C_Field     exps       -> foldl (fn (fvs0, exp) -> 
                                         freeVarsExp(fvs0,exp)) 
                                      fvs 
                                      exps
    | _ -> fvs

 op freeVarsStmt (fvs : List String, stmt : C_Stmt, rec? : Bool) : List String = 
  case stmt of

    | C_Exp    e         -> freeVarsExp (fvs, e)

    | C_Block  b         -> if rec? then 
                              freeVarsBlock (fvs, b, rec?) 
                            else 
                              fvs

    | C_If     (e,s1,s2) -> let fvs0 = freeVarsExp (fvs, e) in
                            if rec? then 
                              freeVarsStmt (freeVarsStmt (fvs0, s1, rec?), s2, rec?)
                            else 
                              fvs0

    | C_Return e         -> freeVarsExp (fvs, e)

    | C_While  (e,s)     -> let fvs0 = freeVarsExp (fvs, e) in
                            if rec? then 
                              freeVarsStmt (fvs0, s, rec?)
                            else 
                              fvs0

    | C_IfThen (e,s)     -> let fvs0 = freeVarsExp (fvs, e) in
                            if rec? then 
                              freeVarsStmt (fvs0, s, rec?)
                            else 
                              fvs0
                              
    | C_Switch (e,stmts) -> let fvs0 = freeVarsExp (fvs, e) in
                            if rec? then 
                              freeVarsStmts (fvs0, stmts, rec?)
                            else
                              fvs0
                              
    | _ -> fvs

 op freeVarsStmts (fvs : List String, stmts : C_Stmts, rec? : Bool) : List String =
  foldl (fn (fvs0, stmt) -> 
           freeVarsStmt (fvs0, stmt, rec?)) 
        fvs 
        stmts

 op freeVarsBlock (fvs : List String, block as (decls,stmts) : C_Block, rec? : Bool)
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

 op freeVars         (b : C_Block) : List String = freeVarsBlock ([], b, true)
 op freeVarsToplevel (b : C_Block) : List String = freeVarsBlock ([], b, false)

 op showFreeVars (b : C_Block) : () =
  let fvs = freeVars b in
  let s   = foldl (fn (s,v) -> if s = "" then v else v^","^s) "" fvs in
  writeLine ("freeVars: ["^s^"]")

 % auxiliary op for moving decls to the innermost block:
 % counts the number of direct sub-blocks of stmts that contain the
 % given variable freely. If it's more than 1 than the decl must stay
 % in the outer level otherwise it can be moved further inside the
 % inner block
 op countInnerBlocksWithFreeVar (v : String, stmts : C_Stmts) : Nat =
  let
    def fvnum fvs =
      if v in? fvs then 1 else 0

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
                | C_Block  b         -> fvnum (freeVarsBlock ([], b, true))
                | C_If     (_,s1,s2) -> fvnumStmts (0, [s1,s2])
                | C_While  (_,s)     -> fvnumStmts (0, [s])
                | C_IfThen (_,s)     -> fvnumStmts (0, [s])
                | C_Switch (_,s)     -> fvnumStmts (0, s)
                | _ -> 0
      in
      let m = countInnerBlocksWithFreeVar (v, stmts) in
      n + m

 % called after the countSubBlocksWithFreeVar has returned 1 for the variable
 % it moves the vardecl to the first inner block where it occurs as free variable
 op moveDeclToInnerBlock (decl as (v,_,_) : C_VarDecl1, stmts : C_Stmts) 
  : C_Stmts =
  let
    def moveDeclStmts stmts =
      case stmts of
        
        | [] -> ([],false)
          
        | stmt::stmts ->
          let fvs = freeVarsStmt ([], stmt, true) in
          if v in? fvs then 
            let stmt = prependDecl (decl, stmt) in
            let stmt = case stmt of
                         | C_Block b -> C_Block (findBlockForDecls b)
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
            | C_Block  (b as (decls,stmts)) -> if v in? freeVarsBlock([],b,true) then
                                                 let b = (decl::decls, stmts) in 
                                                 let b = findBlockForDecls b    in
                                                 (C_Block b, true) 
                                               else 
                                                 (stmt, false)
            | C_If     (e,s1,s2) -> let ([s1,s2],added?) = moveDeclStmts([s1,s2]) in (C_If     (e,s1,s2), added?)
            | C_While  (e,s)     -> let ([s],added?)     = moveDeclStmts([s])     in (C_While  (e,s),     added?)
            | C_IfThen (e,s)     -> let ([s],added?)     = moveDeclStmts([s])     in (C_IfThen (e,s),     added?)
            | C_Switch (e,stmts) -> let (stmts,added?)   = moveDeclStmts(stmts)   in (C_Switch (e,stmts), added?)
            | _ -> (stmt,false)
      in
      if added? then
        stmt::stmts
      else
        let stmts = moveDeclToInnerBlock (decl, stmts) in
        stmt::stmts

 op findBlockForDecls (block as (decls,stmts) : C_Block) : C_Block =
  case decls of
    | [] -> ([], stmts)
    | decl::decls -> findBlockForDecl (decl, (decls, stmts))


 op findBlockForDecl (decl as (v,typ,optexp) : C_VarDecl1, b as (decls,stmts) : C_Block)
  : C_Block =
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

 op NULL : C_Exp = C_Var ("NULL", C_VoidPtr)

 % --------------------------------------------------------------------------------

 op extractHSpec (cspc : C_Spec) : C_Spec =
  %% vars will be printed as "extern"
  %% varDefns will be printed as "extern"
  %% fnDefns will be printed as "extern"
  cspc << {cincludes  = [],
           cverbatims = [],
           axioms     = [],
           varDefns   = [],
           fnDefns    = []}

 op extractCSpec (cspc : C_Spec) : C_Spec =
  cspc << {hincludes            = [], 
           hverbatims           = [],
           defines              = [],
           constDefns           = [],
           vars                 = [],
           fns                  = [],
           structUnionTypeDefns = []}

 % splits the cspc into header and implementation cspcs
 op splitCSpec (cspc : C_Spec) : C_Spec * C_Spec =
  let h_spec = extractHSpec cspc in
  let c_spec = extractCSpec cspc in
  (h_spec, c_spec)

 % --------------------------------------------------------------------------------

 op deleteUnusedTypes (cspc : C_Spec) : C_Spec =
  let usedtypes = usedCTypes cspc in
  let suts = filter (fn dfn ->
                       case dfn of
                         | Type   (n,_) -> C_Base (n, Type)   in? usedtypes
                         | Struct (n,_) -> C_Base (n, Struct) in? usedtypes
                         | Union  (n,_) -> C_Base (n, Union)  in? usedtypes
                         | Enum   (n,_) -> C_Base (n, Enum)   in? usedtypes)
                    cspc.structUnionTypeDefns
  in
  setStructUnionTypeDefns (cspc, suts)

 % --------------------------------------------------------------------------------

 op usedCTypes (cspc : C_Spec) : List C_Type =
  let types = (flatten (map usedCTypesFnDefn  cspc.fnDefns))             in
  let types = (flatten (map usedCTypesVarDefn cspc.varDefns))   ++ types in
  let types = (flatten (map usedCTypesVarDefn cspc.constDefns)) ++ types in
  let types = (flatten (map usedCTypesVarDecl cspc.vars))       ++ types in
  let types = (flatten (map usedCTypesFnDecl  cspc.fns))        ++ types in
  let types = mkUnique types                                             in
  let types = flatten (map (usedCTypesType cspc []) types)               in
  let types = mkUnique types                                             in
  types

 op usedCTypesFnDefn ((_,vdecls,rtype,stmt) : C_FnDefn) : List C_Type =
  let types = flatten (map usedCTypesVarDecl vdecls) in
  let types = rtype::types in
  let types = (usedCTypeStmt stmt) ++ types in
  types

 op usedCTypesFnDecl   ((_,ptypes,rtype) : C_FnDecl)   : List C_Type = rtype::ptypes
 op usedCTypesVarDefn  ((_,t,_)          : C_VarDefn)  : List C_Type = [t]
 op usedCTypesVarDecl  ((_,t)            : C_VarDecl)  : List C_Type = [t]
 op usedCTypesVarDecl1 ((_,t,_)          : C_VarDecl1) : List C_Type = [t]

 op usedCTypeStmt (stmt : C_Stmt) : List C_Type =
   case stmt of

     | C_Block(vdecls1,stmts) ->
       let types = flatten (map usedCTypesVarDecl1 vdecls1) in
       let types = (flatten (map usedCTypeStmt stmts)) ++ types in
       types
       
     | C_If     (_,s1,s2) -> usedCTypeStmt s1 ++ usedCTypeStmt s2
       
     | C_While  (_,s)     -> usedCTypeStmt s
       
     | C_IfThen (_,s)     -> usedCTypeStmt s
       
     | C_Switch (_,stmts) -> flatten (map usedCTypeStmt stmts)
       
     | _ -> []

 op usedCTypesType (cspc : C_Spec) (visited : List C_Type) (t : C_Type) : List C_Type =
  let
    def usedTypes4SUT t =
      case findStructUnionTypeDefn (cspc, t) of
        | Some (Type   (_,t))      -> [t]
        | Some (Union  (_,vdecls)) -> flatten (map usedCTypesVarDecl vdecls)
        | Some (Struct (_,vdecls)) -> flatten (map usedCTypesVarDecl vdecls)
        | Some (Enum   (_,vdecls)) -> []
        | _ -> []
  in
  let newtypes =
      case t of
        | C_Ptr           t            -> [t]
        | C_Array         t            -> [t]
        | C_Base          _            -> usedTypes4SUT t
        | C_ArrayWithSize (_,t)        -> [t]
	| C_Fn            (types, typ) -> typ::types
	| _ -> []
  in
  let newtypes = filter (fn t -> t nin? visited) newtypes in
  let visited  = visited ++ newtypes                      in
  t :: flatten (map (usedCTypesType cspc visited) newtypes)

 % --------------------------------------------------------------------------------

 op prependBlockStmt (block : C_Block, stmt : C_Stmt) : C_Stmt =
  case block of
    | ([],[]) -> stmt
    | (decls,stmts) ->
      case stmt of

        | C_Block (decls1,        stmts1) -> 
          C_Block (decls++decls1, stmts++stmts1)

        | _ -> C_Block (decls, stmts++[stmt])

}
