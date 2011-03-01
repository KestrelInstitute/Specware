
CPrint qualifying spec
{
  %import System  	% ../utilities/system-base.sl
  % import Topsort  	% ../data-structures/topsort.sl
  import C
  import /Languages/MetaSlang/Specs/Printer

  op Specware.currentDeviceAsString : () -> String % defined in toplevel.lisp

  op ppBaseType (s : String, p : Pretty) : Pretty =
    prettysNone [string s, p]

  op ppPlainType    : CType  -> Pretty
  op ppPlainTypes   : CTypes -> Pretty
  op ppExp          : CExp   -> Pretty
  op ppExpInOneLine : CExp   -> Pretty % needed for #defines

  op ppType (t : CType, p : Pretty) : Pretty =
    case t of
      | CVoid          -> ppBaseType ("void"          , p)
      | CChar          -> ppBaseType ("char"          , p)
      | CConstField    -> ppBaseType ("ConstField"    , p)
      | CShort         -> ppBaseType ("short"         , p)
      | CInt           -> ppBaseType ("int"           , p)
      | CLong          -> ppBaseType ("long"          , p)
      | CUnsignedChar  -> ppBaseType ("unsigned char" , p)
      | CUnsignedShort -> ppBaseType ("unsigned short", p)
      | CUnsignedInt   -> ppBaseType ("unsigned int"  , p)
      | CUnsignedLong  -> ppBaseType ("unsigned long" , p)
      | CFloat         -> ppBaseType ("float"         , p)
      | CDouble        -> ppBaseType ("double"        , p)
      | CLongDouble    -> ppBaseType ("long double"   , p)
      | CBase   t      -> ppBaseType ((cId t)         , p)
      | CStruct s      -> prettysNone [string "struct ", string (cId s), p]
      | CUnion  u      -> prettysNone [string "union ",  string (cId u), p]
      | CPtr    t      -> ppType (t, prettysNone [string "*", p, string ""])
      | CArray  t      -> ppType (t, prettysNone [string "(", p, string "[])"])
      | CArrayWithSize (conststr, t) -> ppType (t, prettysNone [(*string "(",*) p, strings ["[",conststr,"]"]])
      | CFn    (ts, t) -> ppType (t, prettysNone [string " (*", p, string ") ", ppPlainTypes ts])
      | mystery -> fail ("Unexpected type to print "^anyToString mystery)

  op ppConst (v : CVal) : Pretty =
    case v of
      | CChar   c           -> strings ["'", show c, "'"]
      | CInt    (b, n)      -> strings [if b then "" else "-", show n]
%     | CFloat  (b, n1, n2) -> strings [if b then "" else "-", show n1, ".", show n2]
      | CFloat  f           -> string f
      | CString s           -> strings ["\"", ppQuoteString(s), "\""]
      | _ -> fail "Unexpected const to print"

  op ppQuoteString (s : String) : String =
    let 
      def ppQuoteCharList (clist: List Char) =
        case clist of
          | [] -> []
          | #\" :: clist -> [#\\,#\"] ++ ppQuoteCharList clist
          %% following fixes bug 162:
          %% C code generation should print newlines within strings as "\n"
          | #\n :: clist -> [#\\,#n]  ++ ppQuoteCharList clist 
          | c :: clist   -> c         :: ppQuoteCharList clist
    in
    implode (ppQuoteCharList (explode s))

  op unaryPrefix? (u : CUnaryOp) : Bool =
    case u of
      | CPostInc -> false
      | CPostDec -> false
      | _        -> true

  op ppUnary (u : CUnaryOp) : Pretty =
    string (case u of
              | CContents -> "*"
              | CAddress  -> "&"
              | CNegate   -> "-"
              | CBitNot   -> "~"
              | CLogNot   -> "!"
              | CPreInc   -> "++"
              | CPreDec   -> "--"
              | CPostInc  -> "++"
              | CPostDec  -> "--"
              | _ -> fail "Unexpected unary")

  op binaryToString(b:CBinaryOp) : String = 
    case b of
      | CSet           -> " = "
      | CAdd           -> " + "
      | CSub           -> " - "
      | CMul           -> " * "
      | CDiv           -> " / "
      | CMod           -> " % "
      | CBitAnd        -> " & "
      | CBitOr         -> " | "
      | CBitXor        -> " ^ "
      | CShiftLeft     -> " << "
      | CShiftRight    -> " >> "
      | CSetAdd        -> " += "
      | CSetSub        -> " -= "
      | CSetMul        -> " *= "
      | CSetDiv        -> " /= "
      | CSetMod        -> " %= "
      | CSetBitAnd     -> " &= "
      | CSetBitOr      -> " |= "
      | CSetBitXor     -> " ^= "
      | CSetShiftLeft  -> " <<= "
      | CSetShiftRight -> " >>= "
      | CLogAnd        -> " && "
      | CLogOr         -> " || "
      | CEq            -> " == "
      | CNotEq         -> " != "
      | CLt            -> " < "
      | CGt            -> " > "
      | CLe            -> " <= "
      | CGe            -> " >= "
      | _ -> fail "Unexpected binary"

  op ppBinary (b : CBinaryOp) : Pretty =
    string (binaryToString b)

  op ppExps          : CExps -> Pretty
  op ppExpsInOneLine : CExps -> Pretty
  % op ppPlainType       : Type -> Pretty

  (*
  op ppAssigns :  List[CVarDecl * CExp] -> Pretty

  op ppAssigns(assigns) = 
      prettysFill (map (fn ((id,_),e)->
                          prettysNone [string id, string " = ", ppExp e, string ","]) 
                       assigns)
  *)

  op parens (p : Pretty) : Pretty =
    prettysNone [string "(", p, string ")"]

  %% Let (assigns,e) -> parens (prettysFill [ppAssigns assigns,ppExp e])

  op ppExp          (e : CExp) : Pretty = ppExp_internal (e, false)
  op ppExpInOneLine (e : CExp) : Pretty = ppExp_internal (e, true)

  op ppExp_internal (e : CExp, inOneLine: Bool) : Pretty =
    let prettysFill   = if inOneLine then prettysNone else prettysFill in
    let prettysLinear = if inOneLine then prettysNone else prettysLinear in
    case e of
      | CConst v            -> ppConst v
      | CFn (s, ts, t)      -> string (cId s)
      | CVar (s, t)         -> string (cId s)
      | CApply (e, es)      -> prettysFill [ppExp_internal(e,inOneLine), prettysNone [string " ", ppExpsInOneline es]]
      | CUnary (u, e)       -> prettysNone (if unaryPrefix? u then
                                              [ppUnary u, ppExpRec(e,inOneLine)]
                                            else
                                              [ppExpRec(e,inOneLine), ppUnary u])
      | CBinary (b, e1, e2) -> prettysFill [ppExpRec(e1,inOneLine), ppBinary b, ppExpRec(e2,inOneLine)]
      | CCast (t, e)        -> parens (prettysNone [parens (ppPlainType t), string " ", ppExp_internal(e,inOneLine)])
      | CStructRef (CUnary (Contents, e), s) -> 
			       prettysNone [ppExpRec(e,inOneLine), strings [" -> ", (cId s)]]
      | CStructRef (e, s)   -> prettysNone [ppExp_internal(e,inOneLine), strings [".", (cId s)]]
      | CUnionRef (e, s)    -> prettysNone [ppExp_internal(e,inOneLine), strings [".", (cId s)]]
      | CArrayRef (e1, e2)  -> prettysNone [ppExpRec(e1,inOneLine), string "[", ppExp_internal (e2, inOneLine), string "]"]
      | CIfExp (e1, e2, e3) -> prettysLinear [prettysNone [ppExpRec(e1,inOneLine), string " ? "],
                                              prettysNone [ppExpRec(e2,inOneLine), string " : "],
                                              ppExpRec(e3,inOneLine)]
      | CComma (e1, e2)     -> parens (prettysFill [ppExp_internal(e1,inOneLine), string ", ", ppExp_internal(e2,inOneLine)])
      | CSizeOfType t       -> prettysNone [string "sizeof (", ppPlainType t, string ")"]
      | CSizeOfExp e        -> prettysNone [string "sizeof (", ppExp_internal(e,inOneLine), string ")"]
      | CField es -> prettysNone [if inOneLine then ppExpsCurlyInOneline es 
					       else ppExpsCurly es]
      | _ -> fail "Unexpected expression" 

  %% Print non-atomic expressions in parens.

  op ppExpRec (e : CExp, inOneLine : Bool) : Pretty =
    case e of
      | CConst _ -> ppExp_internal(e,inOneLine)
      | CVar   _ -> ppExp_internal(e,inOneLine)
      | CFn    _ -> ppExp_internal(e,inOneLine)
      | _ -> parens (ppExp_internal(e,inOneLine))

  op ppBlock   : CBlock -> Pretty
  op ppInBlock : CStmt  -> Pretty

  op ppStmt (s : CStmt) : Pretty =
    case s of
      | CExp e          -> prettysNone [ppExp e, string ";"]
      | CBlock b        -> ppBlock b
      | CIfThen (e, s1) -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "}")])
      | CIf (e, s1, s2) -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "} else {"),
                                         (2, ppInBlock s2),
                                         (0, string "}")])
      | CReturn e       -> prettysNone [string "return ", ppExp e, string ";"]
      | CReturnVoid     -> prettysNone [string "return;"]
      | CBreak          -> string "break;"
      | CNop            -> string ";"
      | CWhile (e, s)   -> blockAll (0, [(0, prettysNone [string "while (", ppExp e, string ") {"]),
                                         (2, ppInBlock s),
                                         (0, string "}")])
      | CLabel s        -> strings [(*"label ", *)s, ":"] %% Changed by Nikolaj
      | CGoto s         -> strings ["goto ", (cId s), ";"]
      | CSwitch (e, ss) -> blockAll (0, [(0, prettysNone [string "switch (", ppExp e, string ") {"]),
                                         (2, ppStmts ss),
                                         (0, string "}")])
      | CCase v         -> prettysNone [string "case ", ppConst v, string ":"]
      | _ -> fail "Unexpected statement" 

  op ppStmts (ss : CStmts) : Pretty =
    prettysAll (map ppStmt ss)

  op ppInclude (s : String) : Pretty =
    let s = if msWindowsSystem? && head (explode s) in? [#\\, #/] then
	      (currentDeviceAsString ()) ^ s
            else
              s
    in
    prettysAll [strings ["#include \"", s, "\""],
                emptyPretty ()]     

  op ppDefine (s : String) : Pretty =
    strings ["#define ", s]

  op ppArg (s : String, t : CType) : Pretty =
    ppType (t, strings [" ", cId s])

  op ppArgs (vds : CVarDecls) : Pretty =
    prettysLinearDelim ("(", ", ", ")") (map ppArg vds)

  op ppPlainType (t : CType) : Pretty =
    ppType (t, emptyPretty ())

  op ppPlainTypes (ts : CTypes) : Pretty =
    prettysLinearDelim ("(", ", ", ")") (map ppPlainType ts)
  
  op ppVarDecl (s : String, t : CType) : Pretty =
    prettysNone [ppArg (s, t), string ";"]

  op ppVarDecl1 (s : String, t : CType, e : Option CExp) : Pretty =
    case e of
      | None   -> prettysNone [ppArg (s, t), string ";"]
      | Some e -> prettysNone [ppArg (s, t), string " = ", ppExp(e), string ";"]

  op ppVarDecls (vds : CVarDecls) : Pretty =
    prettysAll (map ppVarDecl vds)

  op ppVarDecls1 (vds : CVarDecls1) : Pretty =
    prettysAll (map ppVarDecl1 vds)

  op ppTypeDefn (s : String, t : CType) : Pretty =
    let pp =  prettysNone [string "typedef ", ppVarDecl (s, t)] in
    case t of
      | CBase "Any" ->
	blockAll (0, [(0,strings [ "#ifndef "^s^"_is_externally_defined"]),
                      (0,pp),
                      (0,string "#endif")])
      | _ -> pp 

  op ppStructUnionTypeDefn (structOrUnion) : Pretty =
    case structOrUnion of
      | CStruct x -> ppStructDefn x
      | CUnion  x -> ppUnionDefn  x
      | CTypeDefn   x -> ppTypeDefn   x


  op ppStructDefn (s : String, vds : CVarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["struct ", (cId s), " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  op ppUnionDefn (s : String, vds : CVarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["union ", (cId s), " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  op ppVar (asHeader:Bool) (s : String, t : CType) : Pretty =
%    if generateCodeForMotes then
%      if asHeader then
%	prettysNone ([ppVarDecl (s, t),string ""])
%      else
%	emptyPretty()
%    else
      prettysNone ((if asHeader then [string "extern "] else []) 
		   ++ [ppVarDecl (s, t)])

  op ppFn (s : String, ts : CTypes, t : CType) : Pretty =
    (% writeLine ("Pretty printing "^s);
     % app (fn t -> writeLine(anyToString t)) ts;
     % writeLine(anyToString t);
     % writeLine "";

    prettysNone
      [(*string "extern ",*)
       ppType (t, prettysFill [strings [" ", (cId s), " "], ppPlainTypes ts]),
       string ";"]
     )

  op ppExps               (es : CExps) : Pretty = prettysLinearDelim ("(", ", ", ")") (map ppExp es)
  op ppExpsInOneline      (es : CExps) : Pretty = prettysNoneDelim   ("(", ", ", ")") (map (fn e -> ppExp_internal (e,true)) es)
  op ppExpsCurly          (es : CExps) : Pretty = prettysLinearDelim ("{", ", ", "}") (map ppExp es)
  op ppExpsCurlyInOneline (es : CExps) : Pretty = prettysNoneDelim   ("{", ", ", "}") (map (fn e -> ppExp_internal (e,true)) es)

  op ppVarDefn (asHeader:Bool) (s : String, t : CType, e : CExp) : Pretty =
    if asHeader then
      ppVar asHeader (s,t) 
    else
      blockFill	(0, [(0, prettysNone [ppType (t, strings [" ", (cId s)]), string " = "]),
                     (2, prettysNone [ppExp e, string ";"]),
                     (0, newline ())])

  op ppVarDefnAsDefine (s : String, (* t *)_: CType, e : CExp) : Pretty =
    blockNone (0, [(0, prettysNone [string "#define ", string (cId s), string " "]),
                   (2, prettysNone [ppExpInOneLine e]),
                   (0, newline ())])

  op ppPlainBlock (vds : CVarDecls1, ss : CStmts) : Pretty =
    if empty? vds then
      ppStmts ss
    else 
      prettysAll [ppVarDecls1 vds, (*emptyPretty (),*) ppStmts ss]

  op ppInBlock (s : CStmt) : Pretty =
    case s of
      | CBlock (vds, ss) -> ppPlainBlock (vds, ss)
      | _ -> ppStmt s
    

  %% The printer is set up to always call ppInBlock instead of ppBlock,
  %% but it's here for completeness.

  op ppBlock (vds : CVarDecls1, ss : CStmts) : Pretty =
    blockAll
    (0, [(0, string "{"),
         (2, ppPlainBlock (vds, ss)),
         (0, string "}"),
         (0, emptyPretty ())])

  op ppFnDefn (asHeader:Bool) (s : String, vds : CVarDecls, t : CType, b : CStmt) : Pretty =
    if asHeader then
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", (cId s), " "], ppArgs vds]),
	     string ";"]),
	   (0, emptyPretty ())])
    else
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", (cId s), " "], ppArgs vds]),
	     string " {"]),
	   (2, ppInBlock b),
	   (0, string "}"),
	   (0, emptyPretty ())])

  op ppAxiom (e : CExp) : Pretty =
    prettysAll [ppExp e, emptyPretty (), emptyPretty ()]

  op section (title : String, ps : Prettys) : Prettys =
    if empty? ps 
    then [] 

    else
      Cons (emptyPretty (),
        Cons (string title,
          Cons (emptyPretty (), ps)))

  op ppSpec (s : CSpec) : Pretty =
    ppSpec_internal false (s) 

  op ppHeaderSpec (s : CSpec) : Pretty =
    ppSpec_internal true (s) 

  op ppSpec_internal (asHeader:Bool) (s : CSpec) : Pretty =
    %let _ = writeLine "Starting sort..." in
    %let s = sortStructUnionTypeDefns s in
    %let typeDefns = topSortTypeDefns s.typeDefns in
    % let _ = writeLine "Topsort done..." in
    let includes             = map ppInclude             s.includes             in
    let defines              = map ppDefine              s.defines              in
    let constDefns           = map ppVarDefnAsDefine     s.constDefns           in
    let structUnionTypeDefns = map ppStructUnionTypeDefn s.structUnionTypeDefns in
    let vars =
%      if generateCodeForMotes then
%	if s.vars = [] then [] else
%	  [prettysNone [string "#define TOS_FRAME_TYPE KNAL_frame"]]
%	  ++
%	  [prettysNone [string "TOS_FRAME_BEGIN(KNAL_frame) {"]]
%	  ++
%	  (map (ppVar asHeader) s.vars)
%	  ++
%	  [prettysNone [string "#ifdef FRAMEVARS"]]
%	  ++
%	  [prettysNone [string "FRAMEVARS"]]
%	  ++
%	  [prettysNone [string "#endif"]]
%	  ++
%	  [prettysNone [string "}"]]
%	  ++
%	  [prettysNone [string "TOS_FRAME_END(KNAL_frame);"]]
%      else
	map (ppVar asHeader) s.vars
    in
    let fns         = map ppFn                 s.fns      in
    let varDefns    = map (ppVarDefn asHeader) s.varDefns in
    let fnDefns     = map (ppFnDefn asHeader)  s.fnDefns  in
    let axioms      = map ppAxiom              s.axioms   in
    prettysAll (section ("/* C spec */",               [])
                  ++ section ("/* Include files */",        includes)
                  ++ section ("/* Definitions */",          defines)
                  ++ section ("/* Constant Definitions */", constDefns)
                  ++ section ("/* Structs/Unions/Types */", structUnionTypeDefns)
                  ++ section ("/* Variables */",            vars)
                  ++ section ("/* Functions */",            fns)
                  ++ section ("/* Variable definitions */", varDefns)
                  ++ section ("/* Function definitions */", fnDefns)
                  ++ section ("/* Axioms */",               axioms)
                  ++ [emptyPretty ()])

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op ppSpecAsHeader(name:String, s:CSpec):Pretty =
    let defname = "__METASLANG_" ^ 
                  (map toUpperCase name) ^
		  "_H"
    in
    prettysAll ([emptyPretty(),
                 strings [ "#ifndef ", defname ],
                 strings [ "#define ", defname ],
                 ppSpec s,
                 string "#endif",
                 emptyPretty()])

%- --------------------------------------------------------------------------------
  op ppDeclsWithoutDefns(decls:CFnDecls) : Pretty =
    case decls of
      | [] -> emptyPretty()
      | _ ->
        prettysAll ([emptyPretty(), string "/* no code has been generated for the following functions: "]
                    ++ (map ppFn decls) ++ [emptyPretty(), string "*/"])

%- --------------------------------------------------------------------------------

  op ppFnDefnAppendFile (fndefn : CFnDefn, filename : String) : () =
    let fnPretty = ppFnDefn false fndefn in
    appendFile (filename, format (80, fnPretty))


%- --------------------------------------------------------------------------------

(*
  %% Topsort type definitions

  op topSortTypeDefns defns =
    let names = map (fn (name, _) -> name) defns in
    let sortedNames = 
	topSort (EQUAL,
                 fn name -> expand (name, defns),
                 names)
    in
    findTypeDefns (sortedNames, defns)
*)
  %% The names include undefined base sorts, which we ignore.

  op findTypeDefns (names : List String, defns : CTypeDefns) : CTypeDefns =
    case names of
      | [] -> []
      | name :: names ->
        case findTypeDefn (name, defns) of
          | None   -> findTypeDefns (names, defns)
          | Some d -> d :: findTypeDefns (names, defns)

  op expand (name : String, defns : CTypeDefns) : List String =
    case findTypeDefn (name, defns) of
      | None        -> []
      | Some (_, t) -> namesInType t

  op namesInType (t : CType) : List String =
    case t of
      | CBase   name         -> [name]
      | CPtr    t            -> namesInType t
      | CStruct _            -> []
      | CUnion  _            -> []
      | CFn     (ts, t)      -> (namesInType t) ++ (namesInTypes ts)
      | CArray  t            -> namesInType t
      | CArrayWithSize (_,t) -> namesInType t
      | CVoid                -> []
      | CChar                -> []
      | CShort               -> []
      | CInt                 -> []
      | CLong                -> []
      | CUnsignedChar        -> []
      | CUnsignedShort       -> []
      | CUnsignedInt         -> []
      | CUnsignedLong        -> []
      | CFloat               -> []
      | CDouble              -> []
      | CLongDouble          -> []

  op namesInTypes (ts : List CType) : List String =
    flatten (map namesInType ts)

  op findTypeDefn (x : String, defns : CTypeDefns) : Option CTypeDefn =
    findLeftmost (fn (y, _) -> x = y) defns

  op cId (id : String) : String =
    if id = "asm"       ||
       id = "auto"      ||
       id = "break"     ||
       id = "case"      ||
       id = "char"      ||
       id = "const"     ||
       id = "continue"  ||
       id = "default"   ||
       id = "define"    ||
       id = "do"        ||
       id = "double"    ||
       id = "elif"      ||
       id = "else"      ||
       id = "endif"     ||
       id = "entry"     ||
       id = "error"     ||
       id = "enum"      ||
       id = "extern"    ||
       id = "file"      ||
       id = "filemacro" ||
       id = "float"     ||
       id = "for"       ||
       id = "fortran"   ||
       id = "goto"      ||
       id = "if"        ||
       id = "ifdef"     ||
       id = "ifndef"    ||
       id = "include"   ||
       id = "int"       ||
       id = "line"      ||
       id = "linemacro" ||
       id = "long"      ||
       id = "pragma"    ||
       id = "register"  ||
       id = "return"    ||
       id = "short"     ||
       id = "signed"    ||
       id = "sizeof"    ||
       id = "static"    ||
       id = "stdc"      ||
       id = "struct"    ||
       id = "switch"    ||
       id = "typedef"   ||
       id = "union"     ||
       id = "undef"     ||
       id = "unsigned"  ||
       id = "void"      ||
       id = "volatile"  ||
       id = "while" 
      then 
      "_" ^ id 
    else 
      id

}

(*
spec TestCSpecs =

  import CSpecs
  import PrettyPrint

  op factSpec () : Spec =

    { includes    = ["stdio.h"],
      defines     = [],	 
      vars        = [("x", Int)],
      fns         = [("main", [], Void),
                     ("fact", [Int], Int)],
      axioms      = [],
      typeDefns   = [("intfn", Fn ([Int], Int))],
      structDefns = [("foo", [("a", Int), ("b", Char)])],
      unionDefns  = [],
      varDefns    = [("x", Int, Const (Int (true, 3)))],
      fnDefns     =
        [let printf = ("printf", [Array (Char) : Type, Int : Type], Void : Type) in
         let fact   = ("fact", [Int : Type], Int : Type) in
         ("main", [], Void,
          Exp (Apply (Fn printf,
                      [Const (String "fact (5) = %d\\n"),
                       Apply (Fn fact,
                              [Const (Int (true, 5))])]))),

         let n = ("n", Int : Type) in
         let r = ("r", Int : Type) in
         ("fact", [n], Int,
          Block
	  ([r],
	   [Exp (Binary (Set, Var r, Const (Int (true, 1)))),
	    While
	      (Binary (Gt, Var n, Const (Int (true, 0))),
	       Block
		 ([],
		  [Exp (Binary (SetMul, Var r, Var n)),
		   Exp (Binary (SetSub, Var n, Const (Int (true, 1))))])),
	    Return (Var r)]))]
    }

  op test (n : Nat) : () =
    toTerminal (format (n, ppSpec (factSpec ())))

end-spec
*)
