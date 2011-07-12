CPrint qualifying spec
{
  %import System  	% ../utilities/system-base.sl
  % import Topsort  	% ../data-structures/topsort.sl
  import C
  import /Languages/MetaSlang/Specs/Printer

  op Specware.currentDeviceAsString : () -> String % defined in toplevel.lisp

  op ppBaseType (s : String, p : Pretty) : Pretty =
    prettysNone [string s, p]

  op ppPlainType    : C_Type  -> Pretty
  op ppPlainTypes   : C_Types -> Pretty
  op ppExp          : C_Exp   -> Pretty
  op ppExpInOneLine : C_Exp   -> Pretty % needed for #defines

  op ppType (t : C_Type, p : Pretty) : Pretty =
    case t of
      | C_Void          -> ppBaseType  ("void"          , p)
      | C_Char          -> ppBaseType  ("char"          , p)

      | C_Int8          -> ppBaseType  ("int8_t"        , p)  % <stdint.h>
      | C_Int16         -> ppBaseType  ("int16_t"       , p)  % <stdint.h>
      | C_Int32         -> ppBaseType  ("int32_t"       , p)  % <stdint.h>
      | C_Int64         -> ppBaseType  ("int64_t"       , p)  % <stdint.h>
      | C_UInt8         -> ppBaseType  ("uint8_t"       , p)  % <stdint.h>
      | C_UInt16        -> ppBaseType  ("uint16_t"      , p)  % <stdint.h>
      | C_UInt32        -> ppBaseType  ("uint32_t"      , p)  % <stdint.h>
      | C_UInt64        -> ppBaseType  ("uint64_t"      , p)  % <stdint.h>

      | C_Size          -> ppBaseType  ("uint32_t"      , p)  % TODO: ? machine dependent?

      | C_Float         -> ppBaseType  ("float"         , p)
      | C_Double        -> ppBaseType  ("double"        , p)
      | C_LongDouble    -> ppBaseType  ("long double"   , p)

      | C_WChar         -> fail("ppType C_WChar not yet implemented")
      | C_UTF8          -> fail("ppType C_UTF8  not yet implemented")
      | C_UTF16         -> fail("ppType C_UTF16 not yet implemented")
      | C_UTF32         -> fail("ppType C_UTF32 not yet implemented")

      | C_Base   t      -> ppBaseType  (cId t                           , p) % TODO ??
      | C_Struct s      -> prettysNone [string "struct ", string (cId s), p] % TODO: ??
      | C_Union  u      -> prettysNone [string "union " , string (cId u), p] % TODO: ??

      | C_Ptr           t           -> ppType (t, prettysNone [string "*", p, string ""])
      | C_Array         t           -> ppType (t, prettysNone [string "(", p, string "[])"])
      | C_ArrayWithSize (bounds, t) -> ppType (t, prettysNone [p, string "[", ppExps bounds, string "]"])
      | C_Fn            (ts,     t) -> ppType (t, prettysNone [string " (*", p, string ") ", ppPlainTypes ts])

      | C_ConstField    -> ppBaseType  ("ConstField"    , p)
      | mystery -> fail ("Unexpected type to print "^anyToString mystery)

  op ppConst (c : C_Const) : Pretty =
    case c of
      | C_Char  c                 -> strings ["'", show c, "'"]
      | C_Int   (pos?, n)         -> strings [if pos? then "" else "-", show n]
      | C_Str   s                 -> strings ["\"", ppQuoteString s, "\""]
      | C_Macro s                 -> string s

      | C_Float (pos?, m, n, exp) -> let exp_strs = 
                                         case exp of
                                           | Some (pos?, e) -> ["E", if pos? then "" else "-", show e]
                                           | _ -> []
                                     in
                                     strings ([if pos? then "" else "-", show m, ".", show n] ++ exp_strs)

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

  op unaryPrefix? (u : C_UnaryOp) : Bool =
    case u of
      | C_PostInc -> false
      | C_PostDec -> false
      | _        -> true

  op ppUnary (u : C_UnaryOp) : Pretty =
    string (case u of
              | C_Contents -> "*"
              | C_Address  -> "&"
              | C_Negate   -> "-"
              | C_BitNot   -> "~"
              | C_LogNot   -> "!"
              | C_PreInc   -> "++"
              | C_PreDec   -> "--"
              | C_PostInc  -> "++"
              | C_PostDec  -> "--"
              | _ -> fail "Unexpected unary")

  op binaryToString (b:C_BinaryOp) : String = 
    case b of
      | C_Set           -> " = "
      | C_Add           -> " + "
      | C_Sub           -> " - "
      | C_Mul           -> " * "
      | C_Div           -> " / "
      | C_Mod           -> " % "
      | C_BitAnd        -> " & "
      | C_BitOr         -> " | "
      | C_BitXor        -> " ^ "
      | C_ShiftLeft     -> " << "
      | C_ShiftRight    -> " >> "
      | C_SetAdd        -> " += "
      | C_SetSub        -> " -= "
      | C_SetMul        -> " *= "
      | C_SetDiv        -> " /= "
      | C_SetMod        -> " %= "
      | C_SetBitAnd     -> " &= "
      | C_SetBitOr      -> " |= "
      | C_SetBitXor     -> " ^= "
      | C_SetShiftLeft  -> " <<= "
      | C_SetShiftRight -> " >>= "
      | C_LogAnd        -> " && "
      | C_LogOr         -> " || "
      | C_Eq            -> " == "
      | C_NotEq         -> " != "
      | C_Lt            -> " < "
      | C_Gt            -> " > "
      | C_Le            -> " <= "
      | C_Ge            -> " >= "
      | _ -> fail "Unexpected binary"

  op ppBinary (b : C_BinaryOp) : Pretty =
    string (binaryToString b)

  op ppExps          : C_Exps -> Pretty
  op ppExpsInOneLine : C_Exps -> Pretty
  % op ppPlainType       : Type -> Pretty

  (*
  op ppAssigns :  List[C_VarDecl * C_Exp] -> Pretty

  op ppAssigns(assigns) = 
      prettysFill (map (fn ((id,_),e)->
                          prettysNone [string id, string " = ", ppExp e, string ","]) 
                       assigns)
  *)

  op parens (p : Pretty) : Pretty =
    prettysNone [string "(", p, string ")"]

  %% Let (assigns,e) -> parens (prettysFill [ppAssigns assigns,ppExp e])

  op ppExp          (e : C_Exp) : Pretty = ppExp_internal (e, false)
  op ppExpInOneLine (e : C_Exp) : Pretty = ppExp_internal (e, true)

  op ppExp_internal (e : C_Exp, inOneLine: Bool) : Pretty =
    let prettysFill   = if inOneLine then prettysNone else prettysFill in
    let prettysLinear = if inOneLine then prettysNone else prettysLinear in
    case e of

      | C_Const      c            -> ppConst c

      | C_Fn         (s, ts, t)   -> string (cId s)

      | C_Var        (s, t)       -> string (cId s)

      | C_Apply      (e, es)      -> prettysFill [ppExp_internal (e, inOneLine), 
                                                  prettysNone [string " ", 
                                                               ppExpsInOneline es]]

      | C_Unary      (u, e)       -> prettysNone (if unaryPrefix? u then
                                                    [ppUnary u, 
                                                     ppExpRec (e, inOneLine)]
                                                  else
                                                    [ppExpRec (e, inOneLine), 
                                                     ppUnary u])

      | C_Binary     (b, e1, e2)  -> prettysFill [ppExpRec (e1, inOneLine), 
                                                  ppBinary b, 
                                                  ppExpRec (e2, inOneLine)]

      | C_Cast       (t, e)       -> parens (prettysNone [parens (ppPlainType t), 
                                                          string " ", 
                                                          ppExp_internal (e, inOneLine)])

      | C_StructRef  (C_Unary (Contents, e), s) ->  prettysNone [ppExpRec (e, inOneLine), 
                                                                 strings [" -> ", cId s]]

      | C_StructRef  (e, s)       -> prettysNone [ppExp_internal (e, inOneLine), 
                                                  strings [".", cId s]]

      | C_UnionRef   (e, s)       -> prettysNone [ppExp_internal (e, inOneLine), 
                                                  strings [".", cId s]]

      | C_ArrayRef   (e1, e2)     -> prettysNone [ppExpRec (e1, inOneLine), 
                                                  string "[", 
                                                  ppExp_internal (e2, inOneLine), 
                                                  string "]"]

      | C_IfExp      (e1, e2, e3) -> prettysLinear [prettysNone [ppExpRec (e1, inOneLine), 
                                                                 string " ? "],
                                                    prettysNone [ppExpRec (e2, inOneLine), 
                                                                 string " : "],
                                                    ppExpRec (e3, inOneLine)]

      | C_Comma      (e1, e2)     -> parens (prettysFill [ppExp_internal (e1, inOneLine), 
                                                          string ", ", 
                                                          ppExp_internal (e2, inOneLine)])

      | C_SizeOfType t            -> prettysNone [string "sizeof (", ppPlainType t, string ")"]

      | C_SizeOfExp  e            -> prettysNone [string "sizeof (", ppExp_internal (e, inOneLine), string ")"]

      | C_Field      es           -> prettysNone [if inOneLine then 
                                                    ppExpsCurlyInOneline es 
                                                  else 
                                                    ppExpsCurly es]

      | _ -> fail "Unexpected expression" 

  %% Print non-atomic expressions in parens.

  op ppExpRec (e : C_Exp, inOneLine : Bool) : Pretty =
    case e of
      | C_Const _ -> ppExp_internal(e,inOneLine)
      | C_Var   _ -> ppExp_internal(e,inOneLine)
      | C_Fn    _ -> ppExp_internal(e,inOneLine)
      | _ -> parens (ppExp_internal(e,inOneLine))

  op ppBlock   : C_Block -> Pretty
  op ppInBlock : C_Stmt  -> Pretty

  op ppStmt (s : C_Stmt) : Pretty =
    case s of
      | C_Exp e          -> prettysNone [ppExp e, string ";"]
      | C_Block b        -> ppBlock b
      | C_IfThen (e, s1) -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "}")])
      | C_If (e, s1, s2) -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "} else {"),
                                         (2, ppInBlock s2),
                                         (0, string "}")])
      | C_Return e       -> prettysNone [string "return ", ppExp e, string ";"]
      | C_ReturnVoid     -> prettysNone [string "return;"]
      | C_Break          -> string "break;"
      | C_Nop            -> string ";"
      | C_While (e, s)   -> blockAll (0, [(0, prettysNone [string "while (", ppExp e, string ") {"]),
                                         (2, ppInBlock s),
                                         (0, string "}")])
      | C_Label s        -> strings [(*"label ", *)s, ":"] %% Changed by Nikolaj
      | C_Goto s         -> strings ["goto ", cId s, ";"]
      | C_Switch (e, ss) -> blockAll (0, [(0, prettysNone [string "switch (", ppExp e, string ") {"]),
                                         (2, ppStmts ss),
                                         (0, string "}")])
      | C_Case c         -> prettysNone [string "case ", ppConst c, string ":"]
      | _ -> fail "Unexpected statement" 

  op ppStmts (ss : C_Stmts) : Pretty =
    prettysAll (map ppStmt ss)

  op ppComment (s : String) : Pretty =
   strings ["/* ", s, "*/"]

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

  op ppArg (s : String, t : C_Type) : Pretty =
    ppType (t, strings [" ", cId s])

  op ppArgs (vds : C_VarDecls) : Pretty =
    prettysLinearDelim ("(", ", ", ")") (map ppArg vds)

  op ppPlainType (t : C_Type) : Pretty =
    ppType (t, emptyPretty ())

  op ppPlainTypes (ts : C_Types) : Pretty =
    prettysLinearDelim ("(", ", ", ")") (map ppPlainType ts)
  
  op ppVarDecl (s : String, t : C_Type) : Pretty =
    prettysNone [ppArg (s, t), string ";"]

  op ppVarDecl1 (s : String, t : C_Type, e : Option C_Exp) : Pretty =
    case e of
      | None   -> prettysNone [ppArg (s, t), string ";"]
      | Some e -> prettysNone [ppArg (s, t), string " = ", ppExp(e), string ";"]

  op ppVarDecls (vds : C_VarDecls) : Pretty =
    prettysAll (map ppVarDecl vds)

  op ppVarDecls1 (vds : C_VarDecls1) : Pretty =
    prettysAll (map ppVarDecl1 vds)

  op ppTypeDefn (s : String, t : C_Type) : Pretty =
    let pp =  prettysNone [string "typedef ", ppVarDecl (s, t)] in
    case t of
      | C_Base "Any" ->
	blockAll (0, [(0,strings [ "#ifndef "^s^"_is_externally_defined"]),
                      (0,pp),
                      (0,string "#endif")])
      | _ -> pp 

  op ppStructUnionTypeDefn (structOrUnion) : Pretty =
    case structOrUnion of
      | C_Struct x -> ppStructDefn x
      | C_Union  x -> ppUnionDefn  x
      | C_TypeDefn   x -> ppTypeDefn   x


  op ppStructDefn (s : String, vds : C_VarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["struct ", cId s, " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  op ppUnionDefn (s : String, vds : C_VarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["union ", cId s, " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  op ppVar (asHeader:Bool) (s : String, t : C_Type) : Pretty =
%    if generateCodeForMotes then
%      if asHeader then
%	prettysNone ([ppVarDecl (s, t),string ""])
%      else
%	emptyPretty()
%    else
      prettysNone ((if asHeader then [string "extern "] else []) 
		   ++ [ppVarDecl (s, t)])

  op ppFn (s : String, ts : C_Types, t : C_Type) : Pretty =
    (% writeLine ("Pretty printing "^s);
     % app (fn t -> writeLine(anyToString t)) ts;
     % writeLine(anyToString t);
     % writeLine "";

    prettysNone
      [(*string "extern ",*)
       ppType (t, prettysFill [strings [" ", cId s, " "], ppPlainTypes ts]),
       string ";"]
     )

  op ppExps               (es : C_Exps) : Pretty = prettysLinearDelim ("(", ", ", ")") (map ppExp es)
  op ppExpsInOneline      (es : C_Exps) : Pretty = prettysNoneDelim   ("(", ", ", ")") (map (fn e -> ppExp_internal (e,true)) es)
  op ppExpsCurly          (es : C_Exps) : Pretty = prettysLinearDelim ("{", ", ", "}") (map ppExp es)
  op ppExpsCurlyInOneline (es : C_Exps) : Pretty = prettysNoneDelim   ("{", ", ", "}") (map (fn e -> ppExp_internal (e,true)) es)

  op ppVarDefn (asHeader:Bool) (s : String, t : C_Type, e : C_Exp) : Pretty =
    if asHeader then
      ppVar asHeader (s,t) 
    else
      blockFill	(0, [(0, prettysNone [ppType (t, strings [" ", cId s]), string " = "]),
                     (2, prettysNone [ppExp e, string ";"]),
                     (0, newline ())])

  op ppVarDefnAsDefine (s : String, (* t *)_: C_Type, e : C_Exp) : Pretty =
    blockNone (0, [(0, prettysNone [string "#define ", string (cId s), string " "]),
                   (2, prettysNone [ppExpInOneLine e]),
                   (0, newline ())])

  op ppPlainBlock (vds : C_VarDecls1, ss : C_Stmts) : Pretty =
    if empty? vds then
      ppStmts ss
    else 
      prettysAll [ppVarDecls1 vds, (*emptyPretty (),*) ppStmts ss]

  op ppInBlock (s : C_Stmt) : Pretty =
    case s of
      | C_Block (vds, ss) -> ppPlainBlock (vds, ss)
      | _ -> ppStmt s
    

  %% The printer is set up to always call ppInBlock instead of ppBlock,
  %% but it's here for completeness.

  op ppBlock (vds : C_VarDecls1, ss : C_Stmts) : Pretty =
    blockAll
    (0, [(0, string "{"),
         (2, ppPlainBlock (vds, ss)),
         (0, string "}"),
         (0, emptyPretty ())])

  op ppFnDefn (asHeader:Bool) (s : String, vds : C_VarDecls, t : C_Type, b : C_Stmt) : Pretty =
    if asHeader then
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", cId s, " "], ppArgs vds]),
	     string ";"]),
	   (0, emptyPretty ())])
    else
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", cId s, " "], ppArgs vds]),
	     string " {"]),
	   (2, ppInBlock b),
	   (0, string "}"),
	   (0, emptyPretty ())])

  op ppAxiom (e : C_Exp) : Pretty =
    prettysAll [ppExp e, emptyPretty (), emptyPretty ()]

  op section (title : String, ps : Prettys) : Prettys =
    if empty? ps then
      [] 
    else
      emptyPretty () :: string title :: emptyPretty () :: ps

  op ppSpec (s : C_Spec) : Pretty =
    ppSpec_internal false s 

  op ppHeaderSpec (s : C_Spec) : Pretty =
    ppSpec_internal true s 

  op ppSpec_internal (asHeader:Bool) (s : C_Spec) : Pretty =
    %let _ = writeLine "Starting sort..." in
    %let s = sortStructUnionTypeDefns s in
    %let typeDefns = topSortTypeDefns s.typeDefns in
    % let _ = writeLine "Topsort done..." in
    let headers              = map ppComment             s.headers              in
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
    let trailers    = map ppComment            s.trailers in
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

  op ppSpecAsHeader(name:String, s:C_Spec):Pretty =
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
  op ppDeclsWithoutDefns(decls:C_FnDecls) : Pretty =
    case decls of
      | [] -> emptyPretty()
      | _ ->
        prettysAll ([emptyPretty(), string "/* no code has been generated for the following functions: "]
                    ++ (map ppFn decls) ++ [emptyPretty(), string "*/"])

%- --------------------------------------------------------------------------------

  op ppFnDefnAppendFile (fndefn : C_FnDefn, filename : String) : () =
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

  op findTypeDefns (names : List String, defns : C_TypeDefns) : C_TypeDefns =
    case names of
      | [] -> []
      | name :: names ->
        case findTypeDefn (name, defns) of
          | None   -> findTypeDefns (names, defns)
          | Some d -> d :: findTypeDefns (names, defns)

  op expand (name : String, defns : C_TypeDefns) : List String =
    case findTypeDefn (name, defns) of
      | None        -> []
      | Some (_, t) -> namesInType t

  op namesInType (t : C_Type) : List String =
    case t of
      | C_Void                  -> []
      | C_Char                  -> []

      | C_Int8                  -> []
      | C_Int16                 -> []
      | C_Int32                 -> []
      | C_Int64                 -> []
      | C_UInt8                 -> []
      | C_UInt16                -> []
      | C_UInt32                -> []
      | C_UInt64                -> []

      | C_Size                  -> []

      | C_Float                 -> []
      | C_Double                -> []
      | C_LongDouble            -> []

      | C_WChar                 -> []
      | C_UTF8                  -> []
      | C_UTF16                 -> []
      | C_UTF32                 -> []

      | C_Base          name    -> [name]
      | C_Ptr           t       -> namesInType t
      | C_Struct        _       -> [] % TODO
      | C_Union         _       -> [] % TODO
      | C_Array         t       -> namesInType t
      | C_ArrayWithSize (_,t)   -> namesInType t
      | C_Fn            (ts, t) -> (namesInType t) ++ (namesInTypes ts)

      | C_ConstField            -> []

  op namesInTypes (ts : List C_Type) : List String =
    flatten (map namesInType ts)

  op findTypeDefn (x : String, defns : C_TypeDefns) : Option C_TypeDefn =
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
