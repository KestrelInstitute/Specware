(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CPrint qualifying spec
{
 % import System  	% ../utilities/system-base.sl
 % import Toptype  	% ../data-structures/toptype.sl

 import C
 import /Languages/MetaSlang/Specs/Printer

 op CNewline : Pretty = string "\n"

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
    | C_IntInf        -> ppBaseType  ("unbounded_int" , p) 

    | C_UInt8         -> ppBaseType  ("uint8_t"       , p)  % <stdint.h>
    | C_UInt16        -> ppBaseType  ("uint16_t"      , p)  % <stdint.h>
    | C_UInt32        -> ppBaseType  ("uint32_t"      , p)  % <stdint.h>
    | C_UInt64        -> ppBaseType  ("uint64_t"      , p)  % <stdint.h>
    | C_UIntInf       -> ppBaseType  ("unbounded_unsigned_int" , p) 
      
    | C_Size          -> ppBaseType  ("uint32_t"      , p)  % TODO: ? machine dependent?
      
    | C_Float         -> ppBaseType  ("float"         , p)
    | C_Double        -> ppBaseType  ("double"        , p)
    | C_LongDouble    -> ppBaseType  ("long double"   , p)
      
    | C_WChar         -> fail("ppType C_WChar not yet implemented")
    | C_UTF8          -> fail("ppType C_UTF8  not yet implemented")
    | C_UTF16         -> fail("ppType C_UTF16 not yet implemented")
    | C_UTF32         -> fail("ppType C_UTF32 not yet implemented")
      
    | C_Base   (t, ns) -> (case ns of
                            | Type   -> ppBaseType  (cId t                           , p)
                            | Struct -> prettysNone [string "struct ", string (cId t), p]
                            | Union  -> prettysNone [string "union " , string (cId t), p]
                            | Enum   -> prettysNone [string "enum " ,  string (cId t), p])
    | C_Ptr           t           -> ppType (t, prettysNone [string "*", p, string ""])
    | C_Array         t           -> ppType (t, prettysNone [string "(", p, string "[])"])
    | C_ArrayWithSize (bounds, t) -> ppType (t, prettysNone [p, string "[", ppExps bounds, string "]"])
    | C_Fn            (ts,     t) -> ppType (t, prettysNone [string " (*", p, string ") ", ppPlainTypes ts])
      
    | C_ConstField    -> ppBaseType  ("ConstField"    , p)

    | C_Problem msg -> 
      let _ = writeLine msg in
      prettysNone [strings ["\"", ppQuoteString msg, "\""], p]

    | mystery -> fail ("Unexpected type to print "^anyToString mystery)

 op ppConst (c : C_Const) : Pretty =
  case c of
    | C_Char  c                 -> strings ["'", show c, "'"]
    | C_Int   (pos?, n)         -> strings [if pos? then "" else "-", show n]
    | C_Str   s                 -> strings ["\"", ppQuoteString s, "\""]
    | C_Macro s                 -> string s
      
    | C_Float (pos?, m, n, exp) -> 
      let exp_strs = 
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

 op ppExp_internal (exp : C_Exp, inOneLine: Bool) : Pretty =
  let 
    def ppExpRec (e : C_Exp) : Pretty =
      %% Print non-atomic expressions in parens.
      let pretty = ppExp_internal(e,inOneLine) in
      %% we should compare precedences for e and exp, 
      %% but this handles extreme cases of highest and lowest precdence
      case e of
        | C_Const _ -> pretty % atom
        | C_Var   _ -> pretty
        | C_Fn    _ -> pretty
        | C_Unary (_, arg) -> 
          (case arg of
             | C_Var _ -> pretty % unary ops bind tightly around vars
             | _ -> parens pretty)
        | _ -> 
          case exp of
            | C_Binary (CSet, _, _) -> pretty % assignment binds very loosely
            | _ -> parens pretty
  in
  let prettysFill   = if inOneLine then prettysNone else prettysFill in
  let prettysLinear = if inOneLine then prettysNone else prettysLinear in
  case exp of

    | C_Const      c            -> ppConst c

    | C_Fn         (s, ts, t)   -> string (cId s)
      
    | C_Var        (s, t)       -> string (cId s)
      
    | C_Apply      (e, es)      -> prettysFill [ppExp_internal (e, inOneLine), 
                                                             ppExpsInOneline es]
      
    | C_Unary      (u, e)       -> prettysNone (if unaryPrefix? u then
                                                  [ppUnary u, 
                                                   ppExpRec e]
                                                else
                                                  [ppExpRec e, 
                                                   ppUnary u])
      
    | C_Binary     (b, e1, e2)  -> prettysFill [ppExpRec e1, 
                                                ppBinary b, 
                                                ppExpRec e2]
      
    | C_Cast       (t, e)       -> parens (prettysNone [parens (ppPlainType t), 
                                                        string " ", 
                                                        ppExp_internal (e, inOneLine)])
      
    | C_EnumRef    e            -> string (cId e)

    | C_StructRef  (C_Unary (Contents, e), s) ->
        prettysNone [ppExpRec e,
                     strings ["->", cId s]]
      
    | C_StructRef  (e, s)       -> prettysNone [ppExp_internal (e, inOneLine), 
                                                strings [".", cId s]]
      
    | C_UnionRef   (e, s)       -> prettysNone [ppExp_internal (e, inOneLine), 
                                                strings [".", cId s]]
      
    | C_ArrayRef   (e1, e2)     -> prettysNone [ppExpRec e1,
                                                string "[", 
                                                ppExp_internal (e2, inOneLine), 
                                                string "]"]
      
    | C_IfExp      (e1, e2, e3) -> prettysLinear [prettysNone [ppExpRec e1,
                                                               string " ? "],
                                                  prettysNone [ppExpRec e2,
                                                               string " : "],
                                                  ppExpRec e3]
      
    | C_Comma      (e1, e2)     -> parens (prettysFill [ppExp_internal (e1, inOneLine), 
                                                        string ", ", 
                                                        ppExp_internal (e2, inOneLine)])
      
    | C_SizeOfType t            -> prettysNone [string "sizeof (", ppPlainType t, string ")"]
      
    | C_SizeOfExp  e            -> prettysNone [string "sizeof (", ppExp_internal (e, inOneLine), string ")"]
      
    | C_Field      es           -> prettysNone [if inOneLine then 
                                                  ppExpsCurlyInOneline es 
                                                else 
                                                  ppExpsCurly es]
      
    | C_Ignore                  -> string "" % shouldn't arrive here (see ppStmt) but doesn't hurt

    | C_Problem msg ->
      let _ = writeLine msg in
      prettysNone [strings ["\"", ppQuoteString msg, "\""]]

    | _ -> fail ("Unexpected expression: " ^ anyToString exp)

 op ppBlock   : C_Block -> Pretty
 op ppInBlock : C_Stmt  -> Pretty

 op ppStmt (s : C_Stmt) : Pretty =
  case s of
    | C_Exp e           -> prettysNone [ppExp e, string ";"]
    | C_Block b         -> ppBlock b
    | C_IfThen (e, s1)  -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "}")])
    | C_If (e, s1, s2)  -> blockAll (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                         (2, ppInBlock s1),
                                         (0, string "} else {"),
                                         (2, ppInBlock s2),
                                         (0, string "}")])
    | C_Return C_Ignore -> string "return;"
    | C_Return e        -> prettysNone [string "return ", ppExp e, string ";"]
    | C_ReturnVoid      -> prettysNone [string "return;"]
    | C_Break           -> string "break;"
    | C_Nop             -> string ";"
    | C_While (e, s)    -> blockAll (0, [(0, prettysNone [string "while (", ppExp e, string ") {"]),
                                         (2, ppInBlock s),
                                         (0, string "}")])
    | C_Label s         -> strings [(*"label ", *)s, ":"] %% Changed by Nikolaj
    | C_Goto s          -> strings ["goto ", cId s, ";"]
    | C_Switch (e, ss)  -> blockAll (0, [(0, prettysNone [string "switch (", ppExp e, string ") {"]),
                                         (2, ppStmts ss),
                                         (0, string "}")])
    | C_Case c          -> prettysNone [string "case ", ppConst c, string ":"]
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
  prettysAll [strings ["#include \"", s, "\"\n"]]

 op ppVerbatim (s : String) : Pretty =
  strings [s]

 op ppDefine (name : String, defn : String) : Pretty =
  strings ["#define ", name, " ", defn]

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

 op ppStructUnionTypeDefn (structOrUnion) : Pretty =
  case structOrUnion of
    | Type   x -> ppTypeDefn   x
    | Struct x -> ppStructDefn x
    | Union  x -> ppUnionDefn  x
    | Enum   x -> ppEnumDefn   x

 op ppTypeDefn (s : String, t : C_Type) : Pretty =
  let pp = blockAll (0, [(0, prettysNone [string "typedef ", 
                                          ppVarDecl (s, t), 
                                          CNewline])])
  in
  case t of
    | C_Base ("Any", _) ->
      blockAll (0, [(0,strings [ "#ifndef "^s^"_is_externally_defined"]),
                    (0,pp),
                    (0,string "#endif")])
    | _ -> pp 

 op ppStructDefn (s : String, vds : C_VarDecls) : Pretty =
  blockAll (0, [(0, strings ["struct ", cId s, " {"]),
                (2, ppVarDecls vds),
                (0, string "};\n"),
                (0, emptyPretty ())])
  
 op ppUnionDefn (s : String, vds : C_VarDecls) : Pretty =
  blockAll (0, [(0, strings ["union ", cId s, " {"]),
                (2, ppVarDecls vds),
                (0, string "};\n"),
                (0, emptyPretty ())])

 op ppEnumDefn (s : String, tags : Strings) : Pretty =
  blockAll (0, [(0, strings ["enum ", cId s, " {"]),
                (2, strings tags),
                (0, string "};\n"),
                (0, emptyPretty ())])


 op ppVar (asHeader:Bool) (s : String, t : C_Type) : Pretty =
  %    if generateCodeForMotes then
  %      if asHeader then
  %	prettysNone ([ppVarDecl (s, t),string ""])
  %      else
  %	emptyPretty()
  %    else
  blockAll (0, [(0, prettysNone ((if asHeader then [string "extern "] else []) 
                                   ++ [ppVarDecl (s, t), CNewline]))])
                  

 op ppFn (s : String, ts : C_Types, t : C_Type) : Pretty =
  let args = case ts of
               | [] -> string "(void)"
               | _ -> ppPlainTypes ts
  in
  blockAll (0, [(0, prettysNone [ppType (t, prettysFill [strings [" ", cId s, " "], args]),
                                 string ";\n"])])
  
 op ppExps               (es : C_Exps) : Pretty = prettysLinearDelim ("(", ", ", ")") (map ppExp es)
 op ppExpsInOneline      (es : C_Exps) : Pretty = prettysNoneDelim   ("(", ", ", ")") (map (fn e -> ppExp_internal (e,true)) es)
 op ppExpsCurly          (es : C_Exps) : Pretty = prettysLinearDelim ("{", ", ", "}") (map ppExp es)
 op ppExpsCurlyInOneline (es : C_Exps) : Pretty = prettysNoneDelim   ("{", ", ", "}") (map (fn e -> ppExp_internal (e,true)) es)

 op ppVarDefn (asHeader:Bool) (s : String, t : C_Type, e : C_Exp) : Pretty =
  if asHeader then
    ppVar asHeader (s,t) 
  else
    blockFill (0, [(0, prettysNone [ppType (t, strings [" ", cId s]), string " = "]),
                   (2, prettysNone [ppExp e, string ";", CNewline])])

 op ppVarDefnAsDefine (s : String, (* t *)_: C_Type, e : C_Exp) : Pretty =
  blockNone (0, [(0, prettysNone [string "#define ", string (cId s), string " "]),
                 (2, prettysNone [ppExpInOneLine e]),
                 (0, CNewline)])

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
  blockAll (0, [(0, string "{"),
                (2, ppPlainBlock (vds, ss)),
                (0, string "}"),
                (0, emptyPretty ())])

 op ppFnDefn (asHeader:Bool) (s : String, vds : C_VarDecls, t : C_Type, b : C_Stmt) : Pretty =
  let args = case vds of 
               | [] -> string "(void)"
               | _ ->  ppArgs vds
  in
  let decl = ppType (t, prettysFill [strings [" ", cId s, " "], args]) in
  if asHeader then
    blockAll (0, [(0, prettysNone [decl, string ";\n"])])

  else
    blockAll (0, [(0, prettysNone [decl, string " {"]),
                  (2, ppInBlock b),
                  (0, string "}\n")])

 op ppAxiom (e : C_Exp) : Pretty =
  prettysAll [ppExp e, CNewline]

 op section (title : String, ps : Prettys) : Prettys =
  if empty? ps then
    [] 
  else
    newline () :: string (title ^ "\n") :: newline () :: ps

 op ppSpec (s : C_Spec) : Pretty =
  ppSpec_internal false s 

 op ppHeaderSpec (s : C_Spec) : Pretty =
  ppSpec_internal true s 

 op ppSpec_internal (asHeader:Bool) (s : C_Spec) : Pretty =
  %let _ = writeLine "Starting type..." in
  %let s = typeStructUnionTypeDefns s in
  %let typeDefns = topTypeTypeDefns s.typeDefns in
  % let _ = writeLine "Toptype done..." in
  let headers              = map ppComment             s.headers              in
  let hincludes            = map ppInclude             s.hincludes            in
  let cincludes            = map ppInclude             s.cincludes            in
  let includes             = hincludes ++ cincludes                           in % one of the two will be the empty list
  let hverbatims           = map ppVerbatim            s.hverbatims           in    
  let cverbatims           = map ppVerbatim            s.cverbatims           in    
  let verbatims            = hverbatims ++ cverbatims                         in % one of the two will be the empty list
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
                ++ section ("/* Verbatim Text */",        verbatims)
                ++ section ("/* Definitions */",          defines)
                ++ section ("/* Constant Definitions */", constDefns)
                ++ section ("/* Structs/Unions/Types */", structUnionTypeDefns)
                ++ section ("/* Variables */",            vars)
                ++ section ("/* Functions */",            fns)
                ++ section ("/* Variable definitions */", varDefns)
                ++ section ("/* Function definitions */", fnDefns)
                ++ section ("/* Axioms */",               axioms)
                ++ [CNewline])

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op ppSpecAsHeader(name:String, s:C_Spec):Pretty =
  let defname = "__METASLANG_" ^ (map toUpperCase name) ^ "_H" in
  prettysAll ([CNewline,
               strings [ "#ifndef ", defname ],
               strings [ "#define ", defname ],
               ppSpec s,
               string "#endif",
               CNewline])

 %---------------------------------------------------------------------------------
 op ppDeclsWithoutDefns(decls:C_FnDecls) : Pretty =
  case decls of
    | [] -> emptyPretty()
    | _ ->
      prettysAll ([CNewline, string "/* no code has been generated for the following functions: "]
                    ++ (map ppFn decls) 
                    ++ [CNewline, string "*/"])

 %---------------------------------------------------------------------------------

 op ppFnDefnAppendFile (fndefn : C_FnDefn, filename : String) : () =
  let fnPretty = ppFnDefn false fndefn in
  appendFile (filename, format (80, fnPretty))


 %---------------------------------------------------------------------------------

 (*
  %% Toptype type definitions

  op topTypeTypeDefns defns =
    let names = map (fn (name, _) -> name) defns in
    let typeedNames = 
	topType (EQUAL,
                 fn name -> expand (name, defns),
                 names)
    in
    findTypeDefns (typeedNames, defns)
 *)
 %% The names include undefined base types, which we ignore.

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
       
     | C_Base          (name, _) -> [name]
     | C_Ptr           t       -> namesInType t
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
      id    % "_" ^ id  % TODO -- think about this
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
