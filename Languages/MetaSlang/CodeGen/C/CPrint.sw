
CPrint qualifying spec {
  %import System  	% ../utilities/system-base.sl
  % import Topsort  	% ../data-structures/topsort.sl
  import C
  import /Languages/MetaSlang/Specs/Printer


  def ppBaseType (s : String, p : Pretty) : Pretty =
    prettysNone [string s, p]

  op ppPlainType    : Type  -> Pretty
  op ppPlainTypes   : Types -> Pretty
  op ppExp          : Exp   -> Pretty
  op ppExpInOneLine : Exp   -> Pretty % needed for #defines

  def ppType (t : Type, p : Pretty) : Pretty =
    case t
      of Void          -> ppBaseType ("void"          , p)
       | Char          -> ppBaseType ("char"          , p)
       | ConstField    -> ppBaseType ("ConstField"    , p)
       | Short         -> ppBaseType ("short"         , p)
       | Int           -> ppBaseType ("int"           , p)
       | Long          -> ppBaseType ("long"          , p)
       | UnsignedChar  -> ppBaseType ("unsigned char" , p)
       | UnsignedShort -> ppBaseType ("unsigned short", p)
       | UnsignedInt   -> ppBaseType ("unsigned int"  , p)
       | UnsignedLong  -> ppBaseType ("unsigned long" , p)
       | Float         -> ppBaseType ("float"         , p)
       | Double        -> ppBaseType ("double"        , p)
       | LongDouble    -> ppBaseType ("long double"   , p)
       | Base   t      -> ppBaseType (t               , p)
       | Struct s      -> prettysNone [string "struct ", string s, p]
       | Union  u      -> prettysNone [string "union ",  string u, p]
       | Ptr    t      -> ppType (t, prettysNone [string "*", p, string ""])
       | Array  t      -> ppType (t, prettysNone [string "(",  p, string "[])"])
       | ArrayWithSize(conststr,t)  -> ppType (t, prettysNone [(*string "(",*)  p, 
							strings ["[",conststr,"]"]])
       | Fn (ts, t)    -> ppType
                            (t, prettysNone
                                  [string " (*", p, string ") ",
                                   ppPlainTypes ts])
       | _ -> System.fail ("Unexpected type to print "^anyToString t)

  def ppConst (v : Val) : Pretty =
    case v
      of Char   c           -> strings ["'", Char.toString c, "'"]
       | Int    (b, n)      -> strings [if b then "" else "-", Nat.toString n]
%       | Float  (b, n1, n2) -> strings [if b then "" else "-", Nat.toString n1, ".", Nat.toString n2]
       | Float  f           -> string f
       | String s           -> strings ["\"", ppQuoteString(s), "\""]
       | _ -> System.fail "Unexpected const to print"

  def ppQuoteString(s:String):String =
    let def ppQuoteCharList(clist: List Char) =
	      case clist
		of [] -> []
                 | #\" :: clist -> List.concat([#\\,#\"],ppQuoteCharList(clist))
		 | c :: clist -> List.cons(c,ppQuoteCharList(clist))
    in
    String.implode(ppQuoteCharList(String.explode(s)))

  def unaryPrefix? (u : UnaryOp) : Boolean =
    case u
      of PostInc -> false
       | PostDec -> false
       | _       -> true

  def ppUnary (u : UnaryOp) : Pretty =
    string
    (case u
       of Contents -> "*"
        | Address  -> "&"
        | Negate   -> "-"
        | BitNot   -> "~"
        | LogNot   -> "!"
        | PreInc   -> "++"
        | PreDec   -> "--"
        | PostInc  -> "++"
        | PostDec  -> "--"
	| _ -> System.fail "Unexpected unary"
     )

  def binaryToString(b:BinaryOp) : String = 
     case b
       of Set           -> " = "
        | Add           -> " + "
        | Sub           -> " - "
        | Mul           -> " * "
        | Div           -> " / "
        | Mod           -> " % "
        | BitAnd        -> " & "
        | BitOr         -> " | "
        | BitXor        -> " ^ "
        | ShiftLeft     -> " << "
        | ShiftRight    -> " >> "
        | SetAdd        -> " += "
        | SetSub        -> " -= "
        | SetMul        -> " *= "
        | SetDiv        -> " /= "
        | SetMod        -> " %= "
        | SetBitAnd     -> " &= "
        | SetBitOr      -> " |= "
        | SetBitXor     -> " ^= "
        | SetShiftLeft  -> " <<= "
        | SetShiftRight -> " >>= "
        | LogAnd        -> " && "
        | LogOr         -> " || "
        | Eq            -> " == "
        | NotEq         -> " != "
        | Lt            -> " < "
        | Gt            -> " > "
        | Le            -> " <= "
        | Ge            -> " >= "
	| _ -> System.fail "Unexpected binary"

  def ppBinary (b : BinaryOp) : Pretty =
      string(binaryToString b)

  op ppExps            : Exps -> Pretty
  op ppExpsInOneLine   : Exps -> Pretty
  % op ppPlainType       : Type -> Pretty

  (*
  op ppAssigns :  List[VarDecl * Exp] -> Pretty

  def ppAssigns(assigns) = 
      prettysFill(List.map (fn((id,_),e)->
			    prettysNone [string id,string " = ",ppExp e,string ","]) 
		  assigns)
  *)

  def parens (p : Pretty) : Pretty =
    prettysNone [string "(", p, string ")"]

  %% Let (assigns,e) -> parens (prettysFill [ppAssigns assigns,ppExp e])

  def ppExp(e) = ppExp_internal (e,false)
  def ppExpInOneLine(e) = ppExp_internal (e,true)

  op ppExp_internal : Exp * Boolean -> Pretty
  def ppExp_internal (e : Exp, inOneLine: Boolean) : Pretty =
    let prettysFill_ = if inOneLine then prettysNone else prettysFill in
    let prettysLinear = if inOneLine then prettysNone else prettysLinear in
    case e
      of Const v            -> ppConst v
       | Fn (s, ts, t)      -> string s
       | Var (s, t)         -> string s
       | Apply (e, es)      -> prettysFill_ [ppExp_internal(e,inOneLine), prettysNone [string " ", ppExpsInOneline es]]
       | Unary (u, e)       -> prettysNone
                                 (if unaryPrefix? u
                                  then [ppUnary u, ppExpRec(e,inOneLine)]
                                  else [ppExpRec(e,inOneLine), ppUnary u])
       | Binary (b, e1, e2) -> prettysFill_ [ppExpRec(e1,inOneLine), ppBinary b, ppExpRec(e2,inOneLine)]
       | Cast (t, e)        -> parens (prettysNone [parens (ppPlainType t), string " ", ppExp_internal(e,inOneLine)])
       | StructRef (Unary (Contents, e), s) -> 
			       prettysNone [ppExpRec(e,inOneLine), strings [" -> ", s]]
       | StructRef (e, s)   -> prettysNone [ppExp_internal(e,inOneLine), strings [".", s]]
       | UnionRef (e, s)    -> prettysNone [ppExp_internal(e,inOneLine), strings [".", s]]
       | ArrayRef (e1, e2)  -> prettysNone [ppExpRec(e1,inOneLine), string "[", ppExp_internal(e2,inOneLine), string "]"]
       | IfExp (e1, e2, e3) -> prettysLinear
                                 [prettysNone [ppExpRec(e1,inOneLine), string " ? "],
                                  prettysNone [ppExpRec(e2,inOneLine), string " : "],
                                  ppExpRec(e3,inOneLine)]
       | Comma (e1, e2)     -> parens (prettysFill_ [ppExp_internal(e1,inOneLine), string ", ", ppExp_internal(e2,inOneLine)])
       | SizeOfType t       -> prettysNone [string "sizeof (", ppPlainType t, string ")"]
       | SizeOfExp e        -> prettysNone [string "sizeof (", ppExp_internal(e,inOneLine), string ")"]
       | Field es -> prettysNone [if inOneLine then ppExpsCurlyInOneline es 
					       else ppExpsCurly es]
       | _ -> System.fail "Unexpected expression" 

  %% Print non-atomic expressions in parens.

  def ppExpRec (e : Exp, inOneLine : Boolean) : Pretty =
      case e
	of Const _ -> ppExp_internal(e,inOneLine)
	 | Var _ -> ppExp_internal(e,inOneLine)
	 | Fn _ -> ppExp_internal(e,inOneLine)
	 | _ -> parens (ppExp_internal(e,inOneLine))

  op ppBlock   : Block -> Pretty
  op ppInBlock : Stmt -> Pretty

  def ppStmt (s : Stmt) : Pretty =
    case s
      of Exp e          -> prettysNone [ppExp e, string ";"]
       | Block b        -> ppBlock b
       | IfThen (e, s1) -> blockAll
                           (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                (2, ppInBlock s1),
                                (0, string "}")])
       | If (e, s1, s2) -> blockAll
                           (0, [(0, prettysNone [string "if (",  ppExp e, string ") {"]),
                                (2, ppInBlock s1),
                                (0, string "} else {"),
                                (2, ppInBlock s2),
                                (0, string "}")])
       | Return e       -> prettysNone [string "return ", ppExp e, string ";"]
       | ReturnVoid     -> prettysNone [string "return;"]
       | Break          -> string "break;"
       | Nop            -> string ";"
       | While (e, s)   -> blockAll
                           (0, [(0, prettysNone [string "while (", ppExp e, string ") {"]),
                                (2, ppInBlock s),
                                (0, string "}")])
       | Label s        -> strings [(*"label ", *)s, ":"] %% Changed by Nikolaj
       | Goto s         -> strings ["goto ", s, ";"]
       | Switch (e, ss) -> blockAll
                           (0, [(0, prettysNone [string "switch (", ppExp e, string ") {"]),
                                (2, ppStmts ss),
                                (0, string "}")])
       | Case v         -> prettysNone [string "case ", ppConst v, string ":"]
       | _ -> System.fail "Unexpected statement" 

  def ppStmts (ss : Stmts) : Pretty =
    prettysAll (List.map ppStmt ss)

  def ppInclude (s : String) : Pretty =
    prettysAll
    [strings ["#include \"", s, "\""],
     emptyPretty ()]     

  def ppDefine (s : String) : Pretty =
    strings ["#define ", s]

  def ppArg (s : String, t : Type) : Pretty =
    ppType (t, strings [" ", s])

  def ppArgs (vds : VarDecls) : Pretty =
    prettysLinearDelim
      ("(", ", ", ")")
      (List.map ppArg vds)

  def ppPlainType (t : Type) : Pretty =
    ppType (t, emptyPretty ())

  def ppPlainTypes (ts : Types) : Pretty =
    prettysLinearDelim
      ("(", ", ", ")")
      (List.map ppPlainType ts)
  
  def ppVarDecl (s : String, t : Type) : Pretty =
    prettysNone [ppArg (s, t), string ";"]

  def ppVarDecl1 (s : String, t : Type, e : Option(Exp)) : Pretty =
    case e of
      | None -> prettysNone [ppArg (s, t), string ";"]
      | Some e -> prettysNone [ppArg(s,t), string " = ", ppExp(e), string ";"]

  def ppVarDecls (vds : VarDecls) : Pretty =
    prettysAll (List.map ppVarDecl vds)

  def ppVarDecls1 (vds : VarDecls1) : Pretty =
    prettysAll (List.map ppVarDecl1 vds)

  def ppTypeDefn (s : String, t : Type) : Pretty =
    let pp =  prettysNone [string "typedef ", ppVarDecl (s, t)] in
    case t
      of  Base "Any" ->
	blockAll
	(0, [(0,strings [ "#ifndef "^s^"_is_externally_defined"]),
	     (0,pp),
	     (0,string "#endif")])
	| _ -> pp 

  def ppStructUnionTypeDefn (structOrUnion) : Pretty =
    case structOrUnion of
      | Struct X -> ppStructDefn X
      | Union X -> ppUnionDefn X
      | TypeDefn X -> ppTypeDefn X


  def ppStructDefn (s : String, vds : VarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["struct ", s, " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  def ppUnionDefn (s : String, vds : VarDecls) : Pretty =
    blockAll
    (0, [(0, strings ["union ", s, " {"]),
         (2, ppVarDecls vds),
         (0, string "};"),
         (0, emptyPretty ())])

  def ppVar (asHeader:Boolean) (s : String, t : Type) : Pretty =
%    if generateCodeForMotes then
%      if asHeader then
%	prettysNone ([ppVarDecl (s, t),string ""])
%      else
%	emptyPretty()
%    else
      prettysNone ((if asHeader then [string "extern "] else []) 
		   @ [ppVarDecl (s, t)])

  def ppFn (s : String, ts : Types, t : Type) : Pretty =
    (% String.writeLine ("Pretty printing "^s);
     % List.app (fn(t) -> String.writeLine(anyToString t)) ts;
     % String.writeLine(anyToString t);
     % String.writeLine "";

    prettysNone
      [(*string "extern ",*)
       ppType (t, prettysFill [strings [" ", s, " "], ppPlainTypes ts]),
       string ";"]
     )

  def ppExps (es : Exps) : Pretty =
    prettysLinearDelim
      ("(", ", ", ")")
      (List.map ppExp es)

  def ppExpsInOneline (es : Exps) : Pretty =
    prettysNoneDelim
      ("(", ", ", ")")
      (List.map (fn(e) -> ppExp_internal(e,true)) es)

  def ppExpsCurly (es : Exps) : Pretty =
    prettysLinearDelim
      ("{", ", ", "}")
      (List.map ppExp es)

  def ppExpsCurlyInOneline (es : Exps) : Pretty =
    prettysNoneDelim
      ("{", ", ", "}")
      (List.map (fn(e) -> ppExp_internal(e,true)) es)

  def ppVarDefn (asHeader:Boolean) (s : String, t : Type, e : Exp) : Pretty =
    if asHeader then ppVar asHeader (s,t) else
	blockFill
	(0, [(0, prettysNone [ppType (t, strings [" ", s]), string " = "]),
	     (2, prettysNone [ppExp e, string ";"]),
	     (0, PrettyPrint.newline ())])

  def ppVarDefnAsDefine (s : String, (* t *)_: Type, e : Exp) : Pretty =
	blockNone
	(0, [(0, prettysNone [string "#define ", string s, string " "]),
	     (2, prettysNone [ppExpInOneLine e]),
	     (0, PrettyPrint.newline ())])

  def ppPlainBlock (vds : VarDecls1, ss : Stmts) : Pretty =
    if   (null vds)
    then (ppStmts ss)
    else prettysAll [ppVarDecls1 vds, (*emptyPretty (),*) ppStmts ss]

  def ppInBlock (s : Stmt) : Pretty =
    case s
      of Block (vds, ss) -> ppPlainBlock (vds, ss)
       | _               -> ppStmt s
    

  %% The printer is set up to always call ppInBlock instead of ppBlock,
  %% but it's here for completeness.

  def ppBlock (vds : VarDecls1, ss : Stmts) : Pretty =
      
    blockAll
    (0, [(0, string "{"),
         (2, ppPlainBlock (vds, ss)),
         (0, string "}"),
         (0, emptyPretty ())])

  def ppFnDefn (asHeader:Boolean) (s : String, vds : VarDecls, t : Type, b : Stmt) : Pretty =
    if asHeader then
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", s, " "], ppArgs vds]),
	     string ";"]),
	   (0, emptyPretty ())])
    else
      blockAll
      (0, [(0, prettysNone
	    [ppType (t, prettysFill [strings [" ", s, " "], ppArgs vds]),
	     string " {"]),
	   (2, ppInBlock b),
	   (0, string "}"),
	   (0, emptyPretty ())])

  def ppAxiom (e : Exp) : Pretty =
    prettysAll [ppExp e, emptyPretty (), emptyPretty ()]

  def section (title : String, ps : Prettys) : Prettys =
    if List.null ps 
    then [] 

    else
      Cons (emptyPretty (),
        Cons (string title,
          Cons (emptyPretty (), ps)))

  def ppSpec (s : CSpec) : Pretty =
    ppSpec_internal false (s) 

  def ppHeaderSpec (s : CSpec) : Pretty =
    ppSpec_internal true (s) 

  def ppSpec_internal (asHeader:Boolean) (s : CSpec) : Pretty =
    %let _ = writeLine "Starting sort..." in
    %let s = sortStructUnionTypeDefns s in
    %let typeDefns = topSortTypeDefns s.typeDefns in
    % let _ = String.writeLine "Topsort done..." in
    let includes    = List.map ppInclude    s.includes         in
    let defines     = List.map ppDefine     s.defines          in
    let constDefns  = List.map ppVarDefnAsDefine  s.constDefns in
    let structUnionTypeDefns = List.map ppStructUnionTypeDefn s.structUnionTypeDefns in
    let vars =
%      if generateCodeForMotes then
%	if s.vars = [] then [] else
%	  [prettysNone [string "#define TOS_FRAME_TYPE KNAL_frame"]]
%	  @
%	  [prettysNone [string "TOS_FRAME_BEGIN(KNAL_frame) {"]]
%	  @
%	  (List.map (ppVar asHeader) s.vars)
%	  @
%	  [prettysNone [string "#ifdef FRAMEVARS"]]
%	  @
%	  [prettysNone [string "FRAMEVARS"]]
%	  @
%	  [prettysNone [string "#endif"]]
%	  @
%	  [prettysNone [string "}"]]
%	  @
%	  [prettysNone [string "TOS_FRAME_END(KNAL_frame);"]]
%      else
	List.map (ppVar asHeader) s.vars
    in
    let fns         = List.map ppFn         s.fns              in
    let varDefns    = List.map (ppVarDefn asHeader)    s.varDefns         in
    let fnDefns     = List.map (ppFnDefn asHeader)     s.fnDefns          in
    let axioms      = List.map ppAxiom      s.axioms           in
    % let _ = String.writeLine "Components printed..." in
    prettysAll
    (       section ("/* C spec */",               [])
     List.++ section ("/* Include files */",        includes)
     List.++ section ("/* Definitions */",          defines)
     List.++ section ("/* Constant Definitions */", constDefns)
     List.++ section ("/* Structs/Unions/Types */", structUnionTypeDefns)
     List.++ section ("/* Variables */",            vars)
     List.++ section ("/* Functions */",            fns)
     List.++ section ("/* Variable definitions */", varDefns)
     List.++ section ("/* Function definitions */", fnDefns)
     List.++ section ("/* Axioms */",               axioms)
     List.++ [emptyPretty ()])

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  def ppSpecAsHeader(name:String, s:CSpec):Pretty =
    let defname = "__METASLANG_" ^ 
                  (String.map Char.toUpperCase name) ^
		  "_H"
    in
    prettysAll(
	       [emptyPretty()]
	       List.++ ([strings [ "#ifndef ", defname ]])
	       List.++ ([strings [ "#define ", defname ]])
	       List.++ ([ppSpec(s)])
	       List.++ ([string "#endif"])
	       List.++ [emptyPretty()]
	       )

%- --------------------------------------------------------------------------------
  def ppDeclsWithoutDefns(decls:FnDecls) : Pretty =
    case decls
      of [] -> emptyPretty()
       | _ ->
	prettysAll(
		   [emptyPretty()]
		   List.++ ([string "/* no code has been generated for the following functions: "])
		   List.++ (List.map ppFn decls)
		   List.++ [emptyPretty()]
		   List.++ ([string "*/"])
		   )
%- --------------------------------------------------------------------------------

  def ppFnDefnAppendFile(fndefn:C.FnDefn, filename) =
    let fnPretty = ppFnDefn false fndefn in
    PrettyPrint.appendFile(filename,PrettyPrint.format(80,fnPretty))


%- --------------------------------------------------------------------------------

(*
  %% Topsort type definitions

  def topSortTypeDefns defns =
    let names = List.map (fn (name, _) -> name) defns in
    let sortedNames = 
	Topsort.topSort
	      (EQUAL,
	       fn name -> expand (name, defns),
	       names)
    in
    findTypeDefns (sortedNames, defns)
*)
  %% The names include undefined base sorts, which we ignore.

  def findTypeDefns (names, defns) =
    case names
      of [] -> []
       | name :: names ->
         (case findTypeDefn (name, defns)
            of None   -> findTypeDefns (names, defns)
             | Some d -> List.cons (d, findTypeDefns (names, defns)))

  op expand : String * TypeDefns -> List String

  def expand (name, defns) =
    case findTypeDefn (name, defns)
      of None        -> []
       | Some (_, t) -> namesInType t

  def namesInType t =
    case t
      of Base name     -> [name]
       | Ptr    t      -> namesInType t
       | Struct _      -> []
       | Union  _      -> []
       | Fn (ts, t)    -> List.++ (namesInType t, namesInTypes ts)
       | Array  t      -> namesInType t
       | ArrayWithSize  (_,t)      -> namesInType t
       | Void          -> []
       | Char          -> []
       | Short         -> []
       | Int           -> []
       | Long          -> []
       | UnsignedChar  -> []
       | UnsignedShort -> []
       | UnsignedInt   -> []
       | UnsignedLong  -> []
       | Float         -> []
       | Double        -> []
       | LongDouble    -> []

  def namesInTypes ts =
    List.flatten (List.map namesInType ts)

  op  findTypeDefn : String * TypeDefns -> Option TypeDefn

  def findTypeDefn (x, defns) =
    List.find (fn (y, _) -> x = y) defns

}

(*
spec TestCSpecs =

  import CSpecs
  import PrettyPrint

  def factSpec () : Spec =

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

  def test (n : Nat) : () =
    toTerminal (format (n, ppSpec (factSpec ())))

end-spec
*)
