
CUtils qualifying spec {

  import C
  import CPrint
  import /Languages/MetaSlang/Specs/Printer

  op emptyCSpec: String -> CSpec
  def emptyCSpec(name) =
    {
     name = name,
     includes = [],
     defines = [],
     constDefns = [],
     vars = [],
     fns = [],
     axioms = [],
     structUnionTypeDefns = [],
     varDefns = [],
     fnDefns = []
    }
  op renameCSpec: CSpec * String -> CSpec
  def renameCSpec(cspc,name) =
    {
     name = name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addInclude: CSpec * String -> CSpec
  def addInclude(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes @ [X],
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addDefine: CSpec * String -> CSpec
  def addDefine(cspc,X) =
    let defines = filter (fn(df) -> ~(df = X)) cspc.defines in
    let defines = defines @ [X] in
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addConstDefn: CSpec * VarDefn -> CSpec
  def addConstDefn(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns @ [X],
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addVar: CSpec * VarDecl -> CSpec
  def addVar(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars @ [X],
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addFn: CSpec * FnDecl -> CSpec
  def addFn(cspc,X as (fname,_,_)) =
    %let _ = writeLine("adding fndecl for "^fname^"...") in
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns @ [X],
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }

  op delFn: CSpec * String -> CSpec
  def delFn(cspc,fname) =
    %let _ = writeLine("deleting fndecl for "^fname^"...") in
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = filter (fn(fname0,_,_) -> ~(fname0=fname)) cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }


  op addAxiom: CSpec * Exp -> CSpec
  def addAxiom(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms @ [X],
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addTypeDefn: CSpec * TypeDefn -> CSpec
  def addTypeDefn(cspc,X as (tname,_)) =
    %let _ = String.writeLine("adding type definition \""^tname^"\"...") in
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = (filter (fn(TypeDefn(tname0,_)) -> ~(tname0=tname)| _ -> true) cspc.structUnionTypeDefns) @ [TypeDefn X],
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addStructDefn: CSpec * StructDefn -> CSpec
  def addStructDefn(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns @ [Struct X],
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addUnionDefn: CSpec * UnionDefn -> CSpec
  def addUnionDefn(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns @ [Union X],
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  op addVarDefn: CSpec * VarDefn -> CSpec
  def addVarDefn(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns @ [X],
     fnDefns = cspc.fnDefns
    }
  op addFnDefnAux: CSpec * FnDefn * Boolean -> CSpec
  def addFnDefnAux(cspc,fndefn as (fname,params,rtype,body),overwrite) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = if overwrite 
	     then filter (fn(fname0,_,_) -> ~(fname=fname0)) cspc.fns
	   else cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns,
     fnDefns = (if overwrite 
		  then (filter (fn(fname0,_,_,_) -> ~(fname=fname0)) cspc.fnDefns)
		else cspc.fnDefns) @ [fndefn]
    }

  op addFnDefn: CSpec * FnDefn -> CSpec
  def addFnDefn(cspc,fndefn) =
    addFnDefnAux(cspc,fndefn,false)

  op addFnDefnOverwrite: CSpec * FnDefn -> CSpec
  def addFnDefnOverwrite(cspc,fndefn) =
    addFnDefnAux(cspc,fndefn,true)

  op setStructUnionTypeDefns: CSpec * StructUnionTypeDefns -> CSpec
  def setStructUnionTypeDefns(cspc,X) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars,
     fns = cspc.fns,
     axioms = cspc.axioms,
     structUnionTypeDefns = X,
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }
  % --------------------------------------------------------------------------------

  op getStructDefns: CSpec -> StructDefns
  def getStructDefns(cspc) =
    List.foldl (fn(su,structs) ->
		case su of
		  | Struct X -> concat(structs,[X])
		  | _ -> structs
		 ) [] cspc.structUnionTypeDefns

  op getUnionDefns: CSpec -> UnionDefns
  def getUnionDefns(cspc) =
    List.foldl (fn(su,unions) ->
		case su of
		  | Union X -> concat(unions,[X])
		  | _ -> unions
		 ) [] cspc.structUnionTypeDefns

  op getTypeDefns: CSpec -> TypeDefns
  def getTypeDefns(cspc) =
    List.foldl (fn(su,typedefns) ->
		case su of
		  | TypeDefn X -> concat(typedefns,[X])
		  | _ -> typedefns
		 ) [] cspc.structUnionTypeDefns

  % --------------------------------------------------------------------------------

  (**
   * adds a new type definition to cspc; definition in xcspc are
   * also searched (for incremental code generation)
   *)
  op addNewTypeDefn: CSpec * CSpec * TypeDefn -> CSpec * Type
  def addNewTypeDefn(cspc,xcspc,tdef as (tname,typ)) =
    case findTypeDefnInCSpecs([cspc,xcspc],typ) of
      | Some s -> (cspc,Base s)
      | None -> (addTypeDefn(cspc,tdef),Base tname)

  % --------------------------------------------------------------------------------

  % only add the struct definition, if it is new, i.e. if now other
  % struct definition exists in the cspec that has the same fields
  % returns the struct definition that contains the same fields as
  % the input struct definition.
  op addNewStructDefn: CSpec * CSpec * StructDefn * Boolean -> CSpec * Type
  def addNewStructDefn(cspc,xcspc,(sname,sfields),useRefTypes?) =
    let structs = getStructDefns(cspc) in
    let xstructs = getStructDefns(xcspc) in
    let (cspc,struct) = 
      case List.find (fn(sname0,sfields0) -> sfields = sfields0) (structs@xstructs) of
        | Some (sname,_) -> (cspc,Struct sname)
        | None -> let cspc = addStructDefn(cspc,(sname,sfields)) in
                  let struct = Struct sname in
                  (cspc,struct)
    in
    let typ = if useRefTypes? then Ptr(struct) else struct in
    let typ =
        case findTypeDefnInCSpecs([cspc,xcspc],typ) of
	| Some s -> Base s
	| None -> typ
    in
    (cspc,typ)


  op addNewUnionDefn: CSpec * CSpec * UnionDefn -> CSpec * Type
  def addNewUnionDefn(cspc,xcspc,(sname,sfields)) =
    let unions = getUnionDefns(cspc) in
    let xunions = getUnionDefns(xcspc) in
    case List.find (fn(sname0,sfields0) -> sfields = sfields0) (unions@xunions) of
      | Some (sname,_) -> (cspc,Union sname)
      | None -> let cspc = addUnionDefn(cspc,(sname,sfields)) in
                (cspc,Union sname)


  % --------------------------------------------------------------------------------

  op addStmts: Stmt * Stmts -> Stmt
  def addStmts(stmt1,stmts2) =
    case stmt1 of
      | Block(decls,stmts) -> Block(decls,List.concat(stmts,stmts2))
      | _ -> Block([],[stmt1]@stmts2)

  % --------------------------------------------------------------------------------

  op prependDecl: VarDecl1 * Stmt -> Stmt
  def prependDecl(decl,stmt) =
    case stmt of
      | Block(decls,stmts) -> Block(cons(decl,decls),stmts)
      | _ -> Block([decl],[stmt])

  % --------------------------------------------------------------------------------

  op mkBlock: Stmt -> Block
  def mkBlock(stmt) = 
    case stmt of
      | Block(decls,stmts) -> (decls,stmts)
      | _ -> ([],[stmt])

  % --------------------------------------------------------------------------------

  op concatnew: fa(X) List(X) * List(X) -> List(X)
  def concatnew(l1,l2) =
    List.foldl (fn(elem,res) -> if List.member(elem,res) then
				  res
				else 
				  concat(res,[elem]))
    l1 l2

  op mergeCSpecs: List CSpec -> CSpec
  def mergeCSpecs(cspcs) =
    case cspcs of
      | [] -> emptyCSpec ""
      | [cspc] -> cspc
      | cspc1::cspc2::cspcs ->
      let cspc =
         {
	  name = cspc1.name,
	  includes = concatnew(cspc1.includes,cspc2.includes),
	  defines = concatnew(cspc1.defines,cspc2.defines),
	  constDefns = concatnew(cspc1.constDefns,cspc2.constDefns),
	  vars = concatnew(cspc1.vars,cspc2.vars),
	  fns = concatnew(cspc1.fns,cspc2.fns),
	  axioms = concatnew(cspc1.axioms,cspc2.axioms),
	  structUnionTypeDefns = %concatnew(cspc1.structUnionTypeDefns,cspc2.structUnionTypeDefns),
	  foldr (fn(x as TypeDefn(tname,_),res) -> (filter (fn(TypeDefn(tname0,_)) -> ~(tname0=tname)| _ -> true) res) @ [x]
		 | (x,res) -> res @ [x]) cspc2.structUnionTypeDefns cspc1.structUnionTypeDefns,
	  varDefns = concatnew(cspc1.varDefns,cspc2.varDefns),
	  fnDefns = concatnew(cspc1.fnDefns,cspc2.fnDefns)
	 }
      in
      mergeCSpecs(cons(cspc,cspcs))

  op printCType: C.Type -> String
  def printCType(t) =
    let pr = ppType(t,prettysNone[]) in
    let txt = PrettyPrint.format(80,pr) in
    PrettyPrint.toString(txt)

  op printCTypes: String -> List C.Type -> String
  def printCTypes sep types =
    (foldl (fn(t,s) -> s^sep^(printCType t)) "" types)

  op printCSpecToX: CSpec * String * Boolean * (|File|Terminal|String)-> String
  def printCSpecToX (cspc,fname,asHeader,X) =
    let pr = if asHeader
	     then CPrint.ppHeaderSpec(cspc)
	     else CPrint.ppSpec(cspc)
    in
    let txt = PrettyPrint.format(80,pr) in
    case X of
      | File -> (String.writeLine("C-File: "^fname);
		 PrettyPrint.toFile(fname,txt);"")
      | Terminal -> (PrettyPrint.toTerminal(txt);"")
      | String -> PrettyPrint.toString(txt)


  op printCSpecToFile: CSpec * String -> ()
  op printCSpecToTerminal: CSpec -> ()
  op printCSpecToString: CSpec -> String

  op printCSpecToFileEnv: CSpec * String -> SpecCalc.Env ()
  def printCSpecToFileEnv(cspc,fname) = 
    let _ = printCSpecToFile(cspc,fname) in
    return ()

  def printCSpecToFile(cspc,fname) = 
    %let fname = getImplFilename(cspc.name) in
    (printCSpecToX(cspc,fname,false,File);())
  def printCSpecToTerminal(cspc) = (printCSpecToX(cspc,"",false,Terminal);())
  def printCSpecToString(cspc) = printCSpecToX(cspc,"",false,String)

  def printCSpecAsHeaderToFile(cspc) = 
    let fname = getHeaderFilename(cspc.name) in
    (printCSpecToX(cspc,fname,true,File);())
  def printCSpecAsHeaderToTerminal(cspc) = (printCSpecToX(cspc,"",true,Terminal);())
  def printCSpecAsHeaderToString(cspc) = printCSpecToX(cspc,"",true,String)
  
  op getHeaderFilename: String -> String
  def getHeaderFilename(fname) = fname ^ ".h"

  op getImplFilename: String -> String
  def getImplFilename(fname) = fname ^ ".c"

  % --------------------------------------------------------------------------------

  def cString (id : String) : String = 
    let id = String.map cChar id in
    if isCKeyword id
    then cString("slang_" ^ id)
    else substGlyphInIdent(id)

  def substGlyphInIdent(id:String) : String =
    let def substGlyphChar(c:Char) : List Char =
       let ord = Char.ord(c) in
       if ord < 32 then [#_]
       else
       if ord > 126 then [#_]
       else
       if   ((ord >= 48) & (ord <=  57))
	 or ((ord >= 65) & (ord <=  90))
	 or ((ord >= 97) & (ord <= 122))
         or (ord = 95) or (ord = 36)
	 then [c]
       else
	 case ord
	   of  32 -> String.explode("Space")
	    |  33 -> String.explode("Exclam")
	    |  34 -> String.explode("Quotedbl")
	    |  35 -> String.explode("Numbersign")
%	    |  36 -> String.explode("Dollar")
	    |  37 -> String.explode("Percent")
	    |  38 -> String.explode("Ampersand")
	    |  39 -> String.explode("Quotesingle")
	    |  40 -> String.explode("Parenleft")
	    |  41 -> String.explode("Parenright")
	    |  42 -> String.explode("Asterisk")
	    |  43 -> String.explode("Plus")
	    |  44 -> String.explode("Comma")
	    |  45 -> String.explode("$")
	    |  46 -> String.explode("Period")
	    |  47 -> String.explode("Slash")
	    |  58 -> String.explode("Colon")
	    |  59 -> String.explode("Semicolon")
	    |  60 -> String.explode("Less")
	    |  61 -> String.explode("Equal")
	    |  62 -> String.explode("Greater")
	    |  63 -> String.explode("Q")
	    |  64 -> String.explode("At")
	    |  91 -> String.explode("Bracketleft")
	    |  92 -> String.explode("Backslash")
	    |  93 -> String.explode("Bracketright")
	    |  94 -> String.explode("Caret")
	    |  96 -> String.explode("Grave")
	    | 123 -> String.explode("Braceleft")
	    | 124 -> String.explode("Bar")
	    | 125 -> String.explode("Braceright")
	    | 126 -> String.explode("Tilde")
	    | _ -> [#_]
    in
    let def substGlyph(carray) =
       case carray of
          | [#'] -> [] % special case: last character is a single quote
	  | c::carray0  -> concat(substGlyphChar(c),substGlyph(carray0))
	  | []         -> []
    in
      String.implode(substGlyph(String.explode(id)))

  def cChar (c : Char) : Char =
    case c
%-      of #- -> #_
       of #? -> #Q
       | _  -> c

  def isCKeyword s =
    member (s, cKeywords)

  def cKeywords =
    ["auto",     "break",  "case",     "char",    "const",    "continue",
     "default",  "do",     "double",   "else",    "enum",     "extern",
     "float",    "for",    "goto",     "if",      "int",      "long",
     "register", "return", "short",    "signed",  "sizeof",   "static",
     "struct",   "switch", "typedef",  "union",   "unsigned", "void",
     "volatile", "while"]



  op mapExp: (Exp -> Exp) -> Exp -> Exp
  def mapExp f e =
    let mp = mapExp f in
    let e = f e in
    case e of
      | Apply(e,es) -> Apply(mp e,List.map mp es)
      | Unary(o,e) -> Unary(o,mp e)
      | Binary(o,e1,e2) -> Binary(o,mp e1,mp e2)
      | Cast(t,e) -> Cast(t,mp e)
      | StructRef(e,s) -> StructRef(mp e,s)
      | UnionRef(e,s) -> UnionRef(mp e,s)
      | ArrayRef(e1,e2) -> ArrayRef(mp e1, mp e2)
      | IfExp(e1,e2,e3) -> IfExp(mp e1,mp e2, mp e3)
      | Comma(e1,e2) -> Comma(mp e1,mp e2)
      | SizeOfExp(e1) -> SizeOfExp(mp e1)
      | Field(es) -> Field(List.map mp es)
      | _ -> e

  op mapExp2: (Exp -> Exp) * (Type -> Type) -> Exp -> Exp
  def mapExp2 (f,ft) e =
    let mp = mapExp2 (f,ft) in
    let e = f e in
    case e of
      | Var decl -> Var(mapVarDecl (f,ft) decl)
      | Fn decl -> Fn(mapFnDecl (f,ft) decl)
      | Apply(e,es) -> Apply(mp e,List.map mp es)
      | Unary(o,e) -> Unary(o,mp e)
      | Binary(o,e1,e2) -> Binary(o,mp e1,mp e2)
      | Cast(t,e) -> Cast(t,mp e)
      | StructRef(e,s) -> StructRef(mp e,s)
      | UnionRef(e,s) -> UnionRef(mp e,s)
      | ArrayRef(e1,e2) -> ArrayRef(mp e1, mp e2)
      | IfExp(e1,e2,e3) -> IfExp(mp e1,mp e2, mp e3)
      | Comma(e1,e2) -> Comma(mp e1,mp e2)
      | SizeOfExp(e1) -> SizeOfExp(mp e1)
      | SizeOfType(t) -> SizeOfType(ft t)
      | Field(es) -> Field(List.map mp es)
      | _ -> e


  op substVarInExp: Exp * String * Exp -> Exp
  def substVarInExp(e,id,substexp) =
    mapExp (fn(e) -> 
	    case e of
	      | Var(id0,_) -> if id0 = id then substexp else e
	      | _ -> e
	      ) e

  op mapType: (Type -> Type) -> Type -> Type
  def mapType f t =
    let mp = mapType f in
    let t = f t in
    case t of
      | Ptr t -> Ptr(mp t)
      | Array t -> Array(mp t)
      | ArrayWithSize(n,t) -> ArrayWithSize(n,mp t)
      | Fn(ts,t) -> Fn(List.map mp ts,mp t)
      | _ -> t

  op mapCSpec: (Exp -> Exp) * (Type -> Type) -> CSpec -> CSpec
  def mapCSpec (fe,ft) cspc =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = List.map (mapVarDefn(fe,ft)) cspc.constDefns,
     vars = List.map (mapVarDecl(fe,ft)) cspc.vars,
     fns = List.map (mapFnDecl(fe,ft)) cspc.fns,
     axioms = List.map (mapExp2(fe,ft)) cspc.axioms,
     structUnionTypeDefns = List.map (mapStructUnionTypeDefn(fe,ft)) cspc.structUnionTypeDefns,
     varDefns = List.map (mapVarDefn(fe,ft)) cspc.varDefns,
     fnDefns = List.map (mapFnDefn(fe,ft)) cspc.fnDefns
    }

  op mapStmt: (Exp -> Exp) * (Type -> Type) -> Stmt -> Stmt
  def mapStmt (fe,ft) stmt =
    let mp = mapStmt (fe,ft) in
    let mpe = mapExp2(fe,ft) in
    let mpt = mapType ft in
    case stmt of
      | Exp e -> Exp(fe e)
      | Block (decls,stmts) -> Block(List.map (mapVarDecl1(fe,ft)) decls,
				     List.map mp stmts)
      | If(e,stmt1,stmt2) -> If(mpe e,mp stmt1,mp stmt2)
      | Return e -> Return(mpe e)
      | While(e,stmt) -> While(mpe e,mp stmt)
      | IfThen(e,stmt) -> IfThen(mpe e,mp stmt)
      | Switch(e,stmts) -> Switch(mpe e,List.map mp stmts)
      | _ -> stmt

  op mapVarDecl: (Exp -> Exp) * (Type -> Type) -> VarDecl -> VarDecl
  def mapVarDecl (fe,ft) (id,t) = (id,mapType ft t)

  op mapVarDecl1: (Exp -> Exp) * (Type -> Type) -> VarDecl1 -> VarDecl1
  def mapVarDecl1 (fe,ft) (id,t,optexp) = 
    (id,mapType ft t,case optexp of None -> None | Some e -> Some(mapExp2(fe,ft) e))

  op mapFnDecl: (Exp -> Exp) * (Type -> Type) -> FnDecl -> FnDecl
  def mapFnDecl (fe,ft) (id,ts,t) = (id,List.map (mapType ft) ts,mapType ft t)

  op mapTypeDefn: (Exp -> Exp) * (Type -> Type) -> TypeDefn -> TypeDefn
  def mapTypeDefn (fe,ft) (id,t) = (id,mapType ft t)

  op mapStructDefn: (Exp -> Exp) * (Type -> Type) -> StructDefn -> StructDefn
  def mapStructDefn (fe,ft) (id,decls) = (id,List.map (mapVarDecl(fe,ft)) decls)

  op mapUnionDefn: (Exp -> Exp) * (Type -> Type) -> UnionDefn -> UnionDefn
  def mapUnionDefn (fe,ft) (id,decls) = (id,List.map (mapVarDecl(fe,ft)) decls)

  op mapVarDefn: (Exp -> Exp) * (Type -> Type) -> VarDefn -> VarDefn
  def mapVarDefn (fe,ft) (id,t,e) = (id,mapType ft t,mapExp2 (fe,ft) e)

  op mapFnDefn: (Exp -> Exp) * (Type -> Type) -> FnDefn -> FnDefn
  def mapFnDefn (fe,ft) (id,decls,t,stmt) = 
    (id,List.map (mapVarDecl (fe,ft)) decls,
     mapType ft t,mapStmt (fe,ft) stmt)

  op mapStructUnionTypeDefn: (Exp -> Exp) * (Type -> Type) -> StructUnionTypeDefn -> StructUnionTypeDefn
  def mapStructUnionTypeDefn (fe,ft) (sut) =
    case sut of
      | Struct s -> Struct (mapStructDefn (fe,ft) s)
      | Union u -> Union (mapUnionDefn (fe,ft) u)
      | TypeDefn t -> TypeDefn (mapTypeDefn (fe,ft) t)

  % --------------------------------------------------------------------------------

  op getHeaderCSpec: CSpec -> CSpec
  def getHeaderCSpec(cspc) =
    {
     name = cspc.name,
     includes = cspc.includes,
     defines = cspc.defines,
     constDefns = cspc.constDefns,
     vars = cspc.vars, % will be printed as "extern"
     fns = cspc.fns,
     axioms = [],
     structUnionTypeDefns = cspc.structUnionTypeDefns,
     varDefns = cspc.varDefns, % will be printed as "extern"
     fnDefns = cspc.fnDefns % will be printed as "extern"
    }

  op getImplCSpec: CSpec -> CSpec
  def getImplCSpec(cspc) =
    {
     name = cspc.name,
     includes = [],
     defines = [],
     constDefns = [],
     vars = cspc.vars,
     fns = [],
     axioms = cspc.axioms,
     structUnionTypeDefns = [],
     varDefns = cspc.varDefns,
     fnDefns = cspc.fnDefns
    }

  % --------------------------------------------------------------------------------

  % this removes void* typedefs in a cspec, if the same typename is defined at another place
  % in the spec
  op removePtrVoidTypeDefs: CSpec -> CSpec
  def removePtrVoidTypeDefs(cspc) =
    let suts = cspc.structUnionTypeDefns in
    let suts = List.foldl
               (fn(sut,suts) ->
		case sut of
		  | TypeDefn (tname,Ptr(Void)) ->
		    (case List.find (fn|TypeDefn (tname1,_) -> (tname1=tname) | _ -> false) suts of
		       | Some _ -> suts
		       | _ -> concat(suts,[sut])
		      )
		  | _ -> concat(suts,[sut])
		 ) [] suts
    in
    setStructUnionTypeDefns(cspc,suts)

  % --------------------------------------------------------------------------------

  % finds the typedef for a given type
  op findTypeDefn: CSpec * Type -> Option String
  def findTypeDefn(cspc,typ) =
    let typedefns = cspc.structUnionTypeDefns in
    let 
      def findTypeDefn0(typedefns) =
	case typedefns of
	  | (TypeDefn (s,type0))::typedefns ->
	    if type0 = typ then Some s
	    else findTypeDefn0(typedefns)
	  | _::typedefns -> findTypeDefn0(typedefns)
	  | [] -> None
    in
    findTypeDefn0(typedefns)

  op findTypeDefnInCSpecs: List(CSpec) * Type -> Option String
  def findTypeDefnInCSpecs(cspcl,typ) =
    case cspcl of
      | [] -> None
      | cspc::cspcl -> (case findTypeDefn(cspc,typ) of
			  | Some x -> Some x
			  | None -> findTypeDefnInCSpecs(cspcl,typ))

  % --------------------------------------------------------------------------------

  op findStructUnionTypeDefn: CSpec * Type -> Option StructUnionTypeDefn
  def findStructUnionTypeDefn(cspc,typ) =
    case typ of
      | Base n -> List.find (fn|(TypeDefn (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | Struct n -> List.find (fn|(Struct (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | Union n -> List.find (fn|(Union (n0,t)) -> n0=n | _ -> false) cspc.structUnionTypeDefns
      | _ -> 
        %let _ = writeLine("definition for type "^(printCType typ)^" not found.") in
        None

  op structUnionTypeDefnGT: CSpec -> (StructUnionTypeDefn * StructUnionTypeDefn) -> Boolean
  def structUnionTypeDefnGT cspc (sut1,sut2) =
    %let deps1 = structUnionTypeDefnDepends(cspc,sut1) in
    %let t2 = structUnionTypeDefnToType(sut2) in
    %List.member(t2,deps1)
    let deps2 = structUnionTypeDefnDepends(cspc,sut2) in
    let t1 = structUnionTypeDefnToType(sut1) in
    ~(List.member(t1,deps2))

  op sortStructUnionTypeDefns: CSpec -> CSpec
  def sortStructUnionTypeDefns(cspc) =
    let suts = cspc.structUnionTypeDefns in
    let suts = qsort (structUnionTypeDefnGT cspc) suts in
    setStructUnionTypeDefns(cspc,suts)

  op structUnionTypeDefnToType: StructUnionTypeDefn -> Type
  def structUnionTypeDefnToType(sut) =
    case sut of
      | TypeDefn (n,_) -> Base n
      | Struct (s,_) -> Struct s
      | Union (u,_) -> Union u

  op structUnionTypeDefnDepends: CSpec * StructUnionTypeDefn -> Types
  def structUnionTypeDefnDepends(cspc,sutdef) =
    case sutdef of
      %| TypeDefn (n,Ptr(_)) -> typeDepends(cspc,Base n,[])
      | TypeDefn (n,Fn(tys,ty)) -> typeDepends(cspc,Base n,tys@[ty])
      | TypeDefn (n,t) -> typeDepends(cspc,Base n,[t])
      | Struct (s,fields) -> typeDepends(cspc,Struct s,List.map (fn(_,t) -> t) fields)
      | Union (u,fields) -> typeDepends(cspc,Union u,List.map (fn(_,t) -> t) fields)

  op getSubTypes: Type -> Types
  def getSubTypes(t) =
    case t of
      | Fn(tys,ty) -> List.foldl (fn(t,res) -> concat(res,getSubTypes(t))) (getSubTypes(ty)) tys
      | _ -> []

  op typeDepends: CSpec * Type * Types -> Types
  def typeDepends(cspc,_,types) =
    let
      def typeDepends0(t,deps) =
	if List.member(t,deps) then deps
	else
	  case findStructUnionTypeDefn(cspc,t) of
	  | Some (TypeDefn(n,t1)) -> typeDepends0(t1,cons(Base n,deps))
	  | Some (Struct (s,fields)) ->
	    let deps = cons(Struct s,deps) in
	    let types = List.map (fn(_,t)->t) fields in
	    List.foldl (fn(t,deps) -> typeDepends0(t,deps)) deps types
	  | Some (Union (u,fields)) ->
	    let deps = cons(Union u,deps) in
	    let types = List.map (fn(_,t)->t) fields in
	    List.foldl (fn(t,deps) -> typeDepends0(t,deps)) deps types
	  | _ -> deps
    in
    List.foldl (fn(t,deps) -> typeDepends0(t,deps)) [] types
    
    % --------------------------------------------------------------------------------

    % identifies equal structs and unions by inserting defines. This
    % is necessary, because in C structs/unions with the same fields
    % aren't the same.
    op identifyEqualStructsUnions: CSpec -> CSpec
    def identifyEqualStructsUnions(cspc) =
      % let suts = cspc.structUnionTypeDefns in
      let
        def processStructUnion(cspc:CSpec,sut:StructUnionTypeDefn) is
	  let suts = cspc.structUnionTypeDefns in
	  if Boolean.~(List.member(sut,suts)) then cspc else
	  case sut of
	    | TypeDefn _ -> cspc
	    | Struct (id,fields) ->
	      %let _ = String.writeLine("checking struct \""^id^"\"...") in
	      (case List.find (fn(sut) ->
			       case sut of
				 | Struct (id0,fields0) ->
				   (Boolean.~(id0 = id)) & (equalVarDecls cspc (fields0,fields))
				 | _ -> false) suts of
		 | Some (Struct (id0,_)) ->
		   let suts = List.filter (fn|Struct(id1,_) -> Boolean.~(id1=id0)
					     | _ -> true) suts
		   in
		   %let _ = String.writeLine("identifying structs \""^id^"\" and \""^id0^"\"") in
		   let cspc = setStructUnionTypeDefns(cspc,suts) in
		   let cspc = addDefine(cspc,id0^" "^id) in
		   let cspc = mapCSpec ((fn(e)->e),(fn(t) ->
						    case t of
						      | Struct id1 -> if id1=id0 then Struct id else t
						      | _ -> t)) cspc
		   in
		   cspc
		 | None -> 
		   %let _ = String.writeLine("struct \""^id^"\": no identical structs found.") in
		   cspc
		  )
	    | Union (id,fields) ->
	      %let _ = String.writeLine("checking union \""^id^"\"...") in
	      (case List.find (fn(sut) ->
			       case sut of
				 | Union (id0,fields0) ->
				   (Boolean.~(id0 = id)) & (equalVarDecls cspc (fields0,fields))
				 | _ -> false) suts of
		 | Some (Union (id0,_)) ->
		   let suts = List.filter (fn|Union(id1,_) -> Boolean.~(id1=id0)
					     | _ -> true) suts
		   in
		   %let _ = String.writeLine("identifying unions \""^id^"\" and \""^id0^"\"") in
		   let cspc = setStructUnionTypeDefns(cspc,suts) in
		   let cspc = addDefine(cspc,id0^" "^id) in
		   let cspc = mapCSpec ((fn(e)->e),(fn(t) ->
						    case t of
						      | Union id1 -> if id1=id0 then Union id else t
						      | _ -> t)) cspc
		   in
		   cspc
		 | None -> 
		   %let _ = String.writeLine("union \""^id^"\": no identical unions found.") in
		   cspc
		  )
      in
      let
        def identifyRec(cspc) =
	  let suts = cspc.structUnionTypeDefns in
	  %let _ = String.writeLine("---") in
	  let cspc0 = List.foldl (fn(sut,cspc) -> processStructUnion(cspc,sut)) cspc suts in
	  if cspc0 = cspc then cspc else identifyRec cspc0
      in
      let cspc = identifyRec(cspc) in
      setStructUnionTypeDefns(cspc,mkUnique(cspc.structUnionTypeDefns))

  % --------------------------------------------------------------------------------

  op unfoldType: CSpec * Type -> Type
  def unfoldType(cspc,typ) =
    mapType (fn(t) ->
	     case t of
	       | Base tid -> %let _ = writeLine("base type "^tid^" found in unfoldType...") in
	                     (case List.find 
				    (fn(sut) ->
				     case sut of
				       | TypeDefn (tid0,_) -> 
				         %let _ = writeLine("   checking typedef for "^tid0) in
				         tid=tid0
				       | _ -> false) cspc.structUnionTypeDefns of
				| Some (TypeDefn (_,tx)) -> tx
				| None -> t)
	       | _ -> t) typ

  % equality modulo typedefns
  op ctypeEqual: CSpec -> Type * Type -> Boolean
  def ctypeEqual cspc (t1,t2) =
    let t1 = unfoldType(cspc,t1) in
    let t2 = unfoldType(cspc,t2) in
    t1 = t2

  op equalVarDecl: CSpec -> VarDecl * VarDecl -> Boolean
  def equalVarDecl cspc ((id1,t1),(id2,t2)) =
    if id1=id2 then ctypeEqual cspc (t1,t2) else false

  op equalVarDecls: CSpec -> VarDecls * VarDecls -> Boolean
  def equalVarDecls cspc (decls1,decls2) =
    case (decls1,decls2) of
      | ([],[]) -> true
      | (decl1::decls1,decl2::decls2) ->
        if equalVarDecl cspc (decl1,decl2)
	  then equalVarDecls cspc (decls1,decls2)
	else false
      | _ -> false

%name
%includes
%defines
%constDefns
%vars
%fns
%axioms
%structUnionTypeDefns
%varDefns
%fnDefns

  op mkUnique: fa(X) List(X) -> List(X)
  def mkUnique(l) =
    List.foldr
    (fn(e,l) -> if List.member(e,l) then l else cons(e,l)) [] l


  op qsort: fa(X) (X*X->Boolean) -> List(X) -> List(X)
  def qsort gt l =
    let
      def split(x,l) =
	case l of
	  | [] -> ([],[])
	  | y::l -> 
            let (l1,l2) = split(x,l) in
	    if gt(y,x) 
	      then (l1,cons(y,l2))
	    else (cons(y,l1),l2)
    in
    case l of
      | [] -> []
      | [x] -> [x]
      | x::l -> 
        let (l1,l2) = split(x,l) in
	let l1 = qsort gt l1 in
	let l2 = qsort gt l2 in
	concat(l1,cons(x,l2))


  % --------------------------------------------------------------------------------

  op ctypeToString: Type -> String
  def ctypeToString(t) =
    let p = ppPlainType(t) in
    let txt = PrettyPrint.format(80,p) in
    PrettyPrint.toString(txt)

  % --------------------------------------------------------------------------------

  op freeVarsExp: List String * Exp -> List String
  def freeVarsExp(fvs,exp) =
    case exp of
      | Var(v,_) -> if member(v,fvs) then fvs else cons(v,fvs)
      | Apply(e1,exps) -> List.foldl (fn(exp,fvs0) -> freeVarsExp(fvs0,exp)) (freeVarsExp(fvs,e1)) exps
      | Unary(_,exp) -> freeVarsExp(fvs,exp)
      | Binary(_,e1,e2) -> freeVarsExp(freeVarsExp(fvs,e1),e2)
      | Cast(_,e) -> freeVarsExp(fvs,e)
      | StructRef(e,_) -> freeVarsExp(fvs,e)
      | UnionRef(e,_) -> freeVarsExp(fvs,e)
      | ArrayRef(e1,e2) -> freeVarsExp(freeVarsExp(fvs,e1),e2)
      | IfExp(e1,e2,e3) -> freeVarsExp(freeVarsExp(freeVarsExp(fvs,e1),e2),e3)
      | Comma(e1,e2) -> freeVarsExp(freeVarsExp(fvs,e1),e2)
      | SizeOfExp(e) -> freeVarsExp(fvs,e)
      | Field exps -> List.foldl (fn(exp,fvs0) -> freeVarsExp(fvs0,exp)) fvs exps
      | _ -> fvs

  op freeVarsStmt: List String * Stmt * Boolean -> List String
  def freeVarsStmt(fvs,stmt,rec?) =
    case stmt of
      | Exp e -> freeVarsExp(fvs,e)
      | Block b -> if rec? then freeVarsBlock(fvs,b,rec?) else fvs
      | If(e,s1,s2) -> let fvs0 = freeVarsExp(fvs,e) in
                       if rec? then freeVarsStmt(freeVarsStmt(fvs0,s1,rec?),s2,rec?)
		       else fvs0
      | Return e -> freeVarsExp(fvs,e)
      | While(e,s) -> let fvs0 = freeVarsExp(fvs,e) in
		      if rec? then freeVarsStmt(fvs0,s,rec?)
		      else fvs0
      | IfThen(e,s) -> let fvs0 = freeVarsExp(fvs,e) in
		       if rec? then freeVarsStmt(fvs0,s,rec?)
		       else fvs0
      | Switch(e,stmts) -> let fvs0 = freeVarsExp(fvs,e) in
			   if rec? then freeVarsStmts(fvs0,stmts,rec?)
			   else fvs0
      | _ -> fvs

  op freeVarsStmts: List String * Stmts * Boolean -> List String
  def freeVarsStmts(fvs,stmts,rec?) =
     List.foldl (fn(stmt,fvs0) -> freeVarsStmt(fvs0,stmt,rec?)) fvs stmts

  op freeVarsBlock: List String * Block * Boolean -> List String
  def freeVarsBlock(fvs,block as (decls,stmts),rec?) =
    case decls of
      | [] -> freeVarsStmts(fvs,stmts,rec?)
      | (v,_,optexp)::decls ->
        let fvs0 = case optexp of
	            | Some e -> freeVarsExp(fvs,e)
	            | None -> fvs
	in
	let fvs1 = freeVarsBlock(fvs,(decls,stmts),rec?) in
	let fvs1 = List.filter (fn(v0) -> ~(v0 = v) & ~(member(v0,fvs0))) fvs1 in
	concat(fvs0,fvs1)

  op freeVars: Block -> List String
  def freeVars(b) = freeVarsBlock([],b,true)

  op freeVarsToplevel: Block -> List String
  def freeVarsToplevel(b) = freeVarsBlock([],b,false)

  op showFreeVars: Block -> ()
  def showFreeVars(b) =
    let fvs = freeVars(b) in
    let s = List.foldl (fn(v,s) -> if s = "" then v else v^","^s) "" fvs in
    writeLine("freeVars: ["^s^"]")

  % auxiliary op for moving decls to the innermost block:
  % counts the number of direct sub-blocks of stmts that contain the
  % given variable freely. If it's more than 1 than the decl must stay
  % in the outer level otherwise it can be moved further inside the
  % inner block
  op countInnerBlocksWithFreeVar: String * Stmts -> Nat
  def countInnerBlocksWithFreeVar(v,stmts) =
    let
      def fvnum(fvs) =
	if member(v,fvs) then 1 else 0
    in
    let
      def fvnumStmts(n0,stmts) =
	List.foldl (fn(stmt,n) -> fvnum(freeVarsStmt([],stmt,true))+n) n0 stmts
    in
    case stmts of
      | [] -> 0
      | stmt::stmts -> 
        let n = case stmt of
		  | Block b -> fvnum(freeVarsBlock([],b,true))
	          | If(_,s1,s2) -> fvnumStmts(0,[s1,s2])
	          | While(_,s) -> fvnumStmts(0,[s])
	          | IfThen(_,s) -> fvnumStmts(0,[s])
	          | Switch(_,s) -> fvnumStmts(0,s)
	          | _ -> 0
	in
	let m = countInnerBlocksWithFreeVar(v,stmts) in
	n + m

  % called after the countSubBlocksWithFreeVar has returned 1 for the variable
  % it moves the vardecl to the first inner block where it occurs as free variable
  op moveDeclToInnerBlock: VarDecl1 * Stmts -> Stmts
  def moveDeclToInnerBlock(decl as (v,_,_),stmts) =
    let
      def moveDeclStmts(stmts) =
	case stmts of
	  | [] -> ([],false)
	  | stmt::stmts ->
	    let fvs = freeVarsStmt([],stmt,true) in
	    if member(v,fvs) then 
	      let stmt = prependDecl(decl,stmt) in
	      let stmt = case stmt of
			   | Block b -> let b = findBlockForDecls(b) in Block b
	                   | _ -> stmt
	      in
	      (cons(stmt,stmts),true)
	    else
	      let (stmts,added?) = moveDeclStmts(stmts) in
	      (cons(stmt,stmts),added?)
    in
    case stmts of
      | [] -> [] % should not happen
      | stmt::stmts ->
        let (stmt,added?) =
	   case stmt of
	     | Block (b as (decls,stmts)) -> if member(v,freeVarsBlock([],b,true)) then
	                                     let b = (cons(decl,decls),stmts) in 
					     let b = findBlockForDecls(b) in
	                                     (Block b,true) else (stmt,false)
	     | If(e,s1,s2) -> let ([s1,s2],added?) = moveDeclStmts([s1,s2]) in (If(e,s1,s2),added?)
	     | While(e,s) -> let ([s],added?) = moveDeclStmts([s]) in (While(e,s),added?)
	     | IfThen(e,s) -> let ([s],added?) = moveDeclStmts([s]) in (IfThen(e,s),added?)
	     | Switch(e,stmts) -> let (stmts,added?) = moveDeclStmts(stmts) in (Switch(e,stmts),added?)
	     | _ -> (stmt,false)
	in
	if added? then
	  cons(stmt,stmts)
	else
	  let stmts = moveDeclToInnerBlock(decl,stmts) in
	  cons(stmt,stmts)


  op findBlockForDecls: Block -> Block
  def findBlockForDecls(block as (decls,stmts)) =
    case decls of
      | [] -> ([],stmts)
      | decl::decls -> findBlockForDecl(decl,(decls,stmts))


  op findBlockForDecl: VarDecl1 * Block -> Block
  def findBlockForDecl(decl as (v,type,optexp),b as (decls,stmts)) =
    let
      def dontMoveDecl() =
	let (decls,stmts) = findBlockForDecls(b) in
	(cons(decl,decls),stmts)
    in
    let fvtl = freeVarsToplevel(b) in
    if member(v,fvtl) then
      dontMoveDecl()
    else
      let cnt = countInnerBlocksWithFreeVar(v,stmts) in
      if cnt = 1 then
	let stmts = moveDeclToInnerBlock(decl,stmts) in
	let newblock = (decls,stmts) in
	findBlockForDecls(newblock)
      else
	dontMoveDecl()

  % --------------------------------------------------------------------------------

  op NULL: Exp
  def NULL = Var("NULL",Int)

  % --------------------------------------------------------------------------------

  % splits the cspc into header and implementation cspcs
  op splitCSpec: CSpec -> CSpec * CSpec
  def splitCSpec(cspc) = 
    let
      def filterFnDefn isHdr (fndefn as (fname,_,_,_)) =
	isHdr = exists (fn(c) -> c = #$) fname
      %def filterFnDecl isHdr (fndecl as (fname,_,_)) =
	%isHdr = exists (fn(c) -> c = #$) fname
    in
    let hdr = {
	       name = cspc.name,
	       includes = cspc.includes,
	       defines = cspc.defines,
	       constDefns = cspc.constDefns,
	       vars = cspc.vars,
	       fns = cspc.fns,
	       axioms = [],
	       structUnionTypeDefns = cspc.structUnionTypeDefns,
	       varDefns = cspc.varDefns,
	       fnDefns = filter (filterFnDefn true) cspc.fnDefns
	      }
    in
    let cspc = {
	       name = cspc.name,
	       includes = [],
	       defines = [],
	       constDefns = [],
	       vars = [],
	       fns = [],
	       axioms = cspc.axioms,
	       structUnionTypeDefns = [],
	       varDefns = [],
	       fnDefns = filter (filterFnDefn false) cspc.fnDefns
	       }
    in
    (hdr,cspc)


  % --------------------------------------------------------------------------------

  op deleteUnusedTypes: CSpec -> CSpec
  def deleteUnusedTypes(cspc) =
    let usedtypes = usedCTypes(cspc) in
    let suts = filter (fn(TypeDefn(n,_)) -> List.member(Base n,usedtypes)
		       | (Struct(n,_)) -> List.member(Struct n,usedtypes)
		       | (Union(n,_)) -> List.member(Union n,usedtypes))
               cspc.structUnionTypeDefns
    in
    setStructUnionTypeDefns(cspc,suts)

  % --------------------------------------------------------------------------------

  op usedCTypes: CSpec -> List C.Type
  def usedCTypes(cspc) =
    let types = flatten (map usedCTypesFnDefn cspc.fnDefns) in
    let types = (flatten (map usedCTypesVarDefn cspc.varDefns))@types in
    let types = (flatten (map usedCTypesVarDefn cspc.constDefns))@types in
    let types = (flatten (map usedCTypesVarDecl cspc.vars))@types in
    let types = (flatten (map usedCTypesFnDecl cspc.fns))@types in
    let types = mkUnique types in
    %let _ = printCSpecToTerminal(cspc) in
    let types = flatten (map (usedCTypesType cspc []) types) in
    let types = mkUnique types in
    types

  op usedCTypesFnDefn: FnDefn -> List C.Type
  def usedCTypesFnDefn(_,vdecls,rtype,stmt) =
    let types = flatten (map usedCTypesVarDecl vdecls) in
    let types = cons(rtype,types) in
    let types = (usedCTypeStmt stmt)@types in
    types

  op usedCTypesFnDecl: FnDecl -> List C.Type
  def usedCTypesFnDecl(_,ptypes,rtype) =
    cons(rtype,ptypes)

  op usedCTypesVarDefn: VarDefn -> List C.Type
  def usedCTypesVarDefn(_,t,_) = [t]

  op usedCTypesVarDecl: VarDecl -> List C.Type
  def usedCTypesVarDecl(_,t) = [t]

  op usedCTypesVarDecl1: VarDecl1 -> List C.Type
  def usedCTypesVarDecl1(_,t,_) = [t]

  op usedCTypeStmt: Stmt -> List C.Type
  def usedCTypeStmt(stmt) =
    case stmt of
      | Block(vdecls1,stmts) ->
        let types = flatten (map usedCTypesVarDecl1 vdecls1) in
	let types = (flatten (map usedCTypeStmt stmts))@types in
	types
      | If(_,s1,s2) -> concat(usedCTypeStmt(s1),usedCTypeStmt(s2))
      | While(_,s) -> usedCTypeStmt(s)
      | IfThen(_,s) -> usedCTypeStmt(s)
      | Switch(_,stmts) -> flatten (map usedCTypeStmt stmts)
      | _ -> []

  op usedCTypesType: CSpec -> List C.Type -> C.Type -> List C.Type
  def usedCTypesType cspc visited t =
    let
      def usedTypes4SUT(t) =
	case findStructUnionTypeDefn(cspc,t) of
	  | Some (TypeDefn(_,t)) -> [t]
	  | Some (Union(_,vdecls)) -> flatten(map usedCTypesVarDecl vdecls)
	  | Some (Struct(_,vdecls)) -> flatten(map usedCTypesVarDecl vdecls)
	  | _ -> []
    in
    let newtypes =
      case t of
	| Ptr(t) -> [t]
	| Array(t) -> [t]
	| Base _ -> usedTypes4SUT(t)
	| Struct _ -> usedTypes4SUT(t)
	| Union _ -> usedTypes4SUT(t)
	| ArrayWithSize(_,t) -> [t]
	| Fn(types,typ) -> cons(typ,types)
	| _ -> []
    in
    let newtypes = filter (fn(t) -> ~(member(t,visited))) newtypes in
    let visited = visited @ newtypes in
    cons(t,flatten (map (usedCTypesType cspc visited) newtypes))

  % --------------------------------------------------------------------------------

  op prependBlockStmt: Block * Stmt -> Stmt
  def prependBlockStmt(block,stmt) =
    case block of
      | ([],[]) -> stmt
      | (decls,stmts) ->
        case stmt of
	  | Block(decls1,stmts1) -> Block(decls@decls1,stmts@stmts1)
	  | _ -> Block(decls,stmts@[stmt])

}
