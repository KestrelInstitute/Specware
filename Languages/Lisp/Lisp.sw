% Synchronized with version 1.1 of SW4/Languages/MetaSlang/ToLisp/Lisp.sl

ListADT qualifying spec
  import /Library/Legacy/Utilities/Lisp
  import /Library/Legacy/DataStructures/ListPair
  import /Library/Legacy/DataStructures/TopSort
  import /Library/Legacy/DataStructures/MergeSort
  import /Library/Structures/Data/Maps/SimpleAsSTHarray
  import /Library/Structures/Data/Sets/AsSTHarray
  import /Library/PrettyPrinter/BjornerEspinosa
  import Suppress

  type LispSpec =
    { 
      name	     : String,
      extraPackages  : Strings,
      getter_setters : List (String * String),
      ops            : Strings,
      axioms         : LispTerms,
      opDefns        : Definitions }

  type Definition = String * LispTerm

  %% Following musing by jlm:
  %%
  %% TODO: Fix Lambda, Let, Letrec, Flet, etc. to include declarations and documentation?
  %%
  %%         to suppress vacuous warnings:
  %%            (declare (ignore x))
  %%         to optimize code:
  %%            (declare (simple-string s))   
  %%            (declare (simple-vector args))
  %%            (declare (integer n)) 
  %%            (declare (optimize (speed 3)))
  %%         doc string:
  %%            "Version 6.1, optimized for speed 3"
  %%
  %% TODO:  Define lisp special forms? 
  %%        Lambda forms, and application are part of syntax.
  %%        Beyond that, there are exactly 25 special forms in ANSI Common Lisp, as follows:
  %%
  %%            BLOCK
  %%            CATCH
  %%            EVAL-WHEN
  %%            IF
  %%            FLET
  %%            FUNCTION
  %%            GO
  %%            LABELS
  %%            LET
  %%            LET*
  %%            LOAD-TIME-VALUE
  %%            LOCALLY
  %%            MACROLET
  %%            MULTIPLE-VALUE-CALL
  %%            MULTIPLE-VALUE-PROG1
  %%            PROGN
  %%            QUOTE
  %%            PROGV
  %%            RETURN-FROM
  %%            SETQ
  %%            SYMBOL-MACROLET
  %%            TAGBODY
  %%            THE
  %%            THROW
  %%            UNWIND-PROTECT
  %%
  %%        E.g., see  http://www.franz.com/support/documentation/6.1/ansicl/subsubsu/specialf.htm
  %%        Note that const, op, var, set, apply, etc. are not among these! 

 type LispTerm =

    | Const   Val
    | Op      String
    | Var     String
    | Set     String   * LispTerm
    | Lambda  Strings  * LispDecls * LispTerm
    | Apply   LispTerm * LispTerms
    | If      LispTerm * LispTerm  * LispTerm
    | IfThen  LispTerm * LispTerm 
    | Let     Strings  * LispTerms * LispTerm
    | Letrec  Strings  * LispTerms * LispTerm
    | Seq     LispTerms

  type LispDecl =
    | Ignore  Strings

  type Val =
    | Boolean   Bool
    | Nat       Nat
    | Char      Char
    | String    String
    | Symbol    String * String
    | Parameter String
    | Cell      Lisp.LispCell

  type LispSpecs   = List LispSpec
  type Strings     = List String
  type LispTerms   = List LispTerm
  type LispDecls   = List LispDecl
  type Definitions = List Definition

  op emptySpec : LispSpec

  def emptySpec =
    { name    = "BASESPECS",
      extraPackages  = [],
      getter_setters = [],
      ops     = [],
      axioms  = [],
      opDefns = [] }

  op  ops: LispTerm * Set.Set String -> Set.Set String
  def ops(term:LispTerm,names) =
      case term 
        of Const(Parameter name) -> Set.insert names name
	 | Const _ -> names
         | Op      name -> Set.insert names name
         | Var     _ -> names
         | Set     (_,term) -> ops(term,names)
         | Lambda  (_,_,term) -> ops(term,names)
         | Apply   (term,terms) -> List.foldl (fn (names,tm) -> ops(tm,names)) (ops(term,names)) terms
         | If      (t1,t2,t3) -> ops(t1,ops(t2,ops(t3,names)))
         | IfThen  (t1,t2) -> ops(t1,ops(t2,names))
         | Let     (_,terms,body) -> List.foldl (fn (names,tm) -> ops(tm,names)) (ops(body,names)) terms
         | Letrec  (_,terms,body) -> List.foldl (fn (names,tm) -> ops(tm,names)) (ops(body,names)) terms
         | Seq     terms -> List.foldr ops names terms

  op moveDefparamsToEnd?: Bool = true

  op nonLambdaDef?((_, body): Definition): Bool =
    ~(embed? Lambda body)

  op makeDefNil((nm, _): Definition): Definition =
    (nm, Const(Boolean false))          % nil

  op  typeDefs: Definitions -> Definitions
  def typeDefs(defs) = 
      let defs = sortGT (fn ((nm1,_),(nm2,_)) -> nm2 <= nm1) defs in
      let defMap = 
	  List.foldl (fn(map, (name,term))-> STHMap.update(map,name,(name,term)))
	  STHMap.emptyMap defs
      in
      let map = 
	  List.foldl
	    (fn(map, (name,term)) -> 
		let opers = ops(term,Set.empty) in
		let opers = Set.toList opers in
		STHMap.update(map,name,opers))
	     STHMap.emptyMap defs
       in
       let find = fn name -> (case STHMap.apply(map,name) of None -> [] | Some l -> l) in
       let names = TopSort.topSort(EQUAL,find,List.map (fn(n,_)-> n) defs) in
       let defs  = List.mapPartial (fn name -> STHMap.apply(defMap,name)) names in
       let defs =
           if moveDefparamsToEnd?
             then
               let defparams = filter nonLambdaDef? defs in
               let defs = List.map (fn defn ->
                                      if nonLambdaDef? defn
                                        then makeDefNil defn
                                      else defn)
                            defs
               in
               defs ++ defparams
             else defs
       in
       defs

  %% Printing of characters is temporarily wrong due to bug in lexer.

  def ppDecl (decl : LispDecl) : PrettyPrint.Pretty =
     case decl of
       | Ignore names -> prettysLinearDelim ("(declare (ignore ", " ", ")) ")
                                            (List.map string names)

  def ppTerm (t : LispTerm) : PrettyPrint.Pretty =
    case t

      of Const v ->
        (case (v : Val)
          of Boolean b      -> string (if b then "t" else "nil")
           | Nat     n      -> string (Nat.show n)
           | Char    c      -> strings ["\#\\", Char.show c]  % backslash before hash to appease emacs
           | String  s      -> string s
           | Symbol  (p, s) -> strings ["'", p, "::", s]
	   | Cell cell      -> strings ["'", anyToString cell]
	   | Parameter s    -> string s)
        
       | Op s -> strings ["#'", s]

       | Var s -> string s

       | Set (s, t) ->
         blockFill
         (0, [(0, strings ["(setq ", s, " "]),
              (2, prettysNone [ppTerm t, string ")"])])

       | Lambda (ss, decls, t) ->
         blockFill
         (0, [(0, prettysLinearDelim
                    ("#'(lambda (", " ", ") ")
                    (List.map string ss)),
	      (3, prettysAll ((List.map ppDecl decls) ++ 
			      [prettysNone [ppTerm t, string ")"]]))])
       | Apply (Op "list", [Const(Parameter v)]) ->
	 % (list :foo) -> '(:foo)   optimization for nullary constructors
	 if v@0 = #:
	   then strings ["'(", v, ")"]
	   else strings ["(list ", v, ")"]
       | Apply (Op s, ts) ->
         prettysLinearDelim
           ("(", " ",")")
           (Cons (string s, List.map ppTerm ts))

       | Apply (t, ts) ->
         prettysLinearDelim
           ("(funcall ", " ",")")
           (Cons (ppTerm t, List.map ppTerm ts))

       | If (p, c, a) ->
         prettysLinearDelim
           ("(if ", " ", ")")
           [ppTerm p, ppTerm c, ppTerm a]

       | IfThen (p, c) ->
         prettysLinearDelim
           ("(if ", " ", ")")
           [ppTerm p, ppTerm c]

       | Let (ss, ts, t) ->
         blockFill
         (0, [(0, prettysAllDelim
                  ("(let (", "", ") ")
                  (ListPair.map
                    (fn (s, t) ->
                      prettysFillDelim
                        ("(", " ", ")")
                        [string s, ppTerm t])
                    (ss, ts))),
              (2, prettysNone [ppTerm t, string ")"])])

       | Letrec (ss, ts, t) ->
         blockFill
         (0, [(0, string "(labels "),
              (2, prettysAllDelim
                  ("(", "", ") ")
                  (ListPair.map
                    (fn (s, Lambda (args, decls, body)) ->
                      prettysFillDelim
                        ("(", " ", ")")
                        [string s,
                         prettysLinearDelim
                           ("(", " ", ")")
                           (List.map string args),
			 prettysAll ((List.map ppDecl decls) ++ [prettysNone [ppTerm body]])
			])
                    (ss, ts))),
              (2, prettysNone [ppTerm t, string ")"])])

       | Seq ts ->
         prettysLinearDelim
           ("(progn ", " ", ")")
           (List.map ppTerm ts)

  op warnAboutSuppressingDefuns?: Bool = false

  def ppOpDefn(s : String,term:LispTerm) : PrettyPrint.Pretty = 
    if  s in? SpecToLisp.SuppressGeneratedDefuns then
      let comment = ";;; Suppressing generated def for " ^ s in
      let _ = if warnAboutSuppressingDefuns?
                then toScreen(comment ^ "\n")
                else ()
      in
      blockFill (0, [(0, string comment), (0, PrettyPrint.newline ())])
    else
      case term
	of Lambda (args, decls, body) -> 
	    blockFill
	      (0, [(0, string "(defun "),
	           (0, string s),
	           (0, prettysLinearDelim
	                 (" (", " ", ") ")
	                 (List.map string args)),
		   (2, prettysAll ((List.map ppDecl decls) ++ 
				   [prettysNone [ppTerm body, string ")"]])),
		   (0, PrettyPrint.newline ())])
	 | _ -> 
	    blockFill
	      (0, [(0, string "(defparameter "),
	           (0, string s),
                   (0, string " "),
	           (2, prettysNone [ppTerm term,string ")"]),
	           (0, PrettyPrint.newline ())])

  def section (title : String, ps : Prettys) : Prettys =
    (Cons (emptyPretty (),
      Cons (string title,
        Cons (emptyPretty (), ps)))) : Prettys

  op ppDefToStream: Definition * Stream -> ()
  def ppDefToStream(ldef,stream) =
    let p = ppOpDefn ldef in
    let t = format (80, p) in
    (toStreamT (t,
	       fn ((_,string), ()) -> streamWriter(stream,string),
	       (),
	       fn (n,()) -> streamWriter(stream,newlineAndBlanks n));
     streamWriter(stream,"\n"))

  op ppSpecToFile : LispSpec * String * String -> ()
  
  op maxDefsPerFile: Int = 1000

  def ppSpecToFile (spc, file, preamble) =
    %% Rewritten to not use ppSpec which requires a lot of space for large specs
    let defs = typeDefs(spc.opDefns) 	in
    let name = spc.name 		in
    IO.withOpenFileForWrite
      (file,
       fn stream ->
	(streamWriter(stream,preamble);
	 streamWriter(stream,";;; Lisp spec\n\n");
	 app (fn pkgName -> streamWriter (stream,
					  "(defpackage :" ^ pkgName ^ ")\n"))
	  (sortGT (fn (x,y) -> y <= x) spc.extraPackages);
	streamWriter(stream,"\n(defpackage :" ^ name ^ ")");
	streamWriter(stream,"\n(in-package :" ^ name ^ ")\n\n");

	streamWriter(stream,";;; Definitions\n\n");

        %% streamWriter(stream,"(defmacro System-spec::setq-2 (x y) `(setq ,x ,y))\n\n");
        let getter_setters = [] in
        app (fn (getter, setter) -> streamWriter (stream, "(defsetf" ^ getter ^ " " ^ setter ^ ")\n"))
            spc.getter_setters;

        if length defs < maxDefsPerFile
          then app (fn ldef -> ppDefToStream(ldef,stream)) defs
        else
        let fileNameBase = subFromTo(file, 0, length file - 5) in   % Remove ".lisp"
        let def writeSubFiles(rem_defs, i) =
              if rem_defs = [] then ()
              else
              let post_fix = "--"^show i in
              let subfileBase = fileNameBase^post_fix in
              let subfile = subfileBase^".lisp" in
              let num_remaining = length rem_defs in
              (IO.withOpenFileForWrite
                 (subfile,
                  fn substream ->
                    (streamWriter(substream, "(in-package :" ^ name ^ ")\n\n");
                     app (fn ldef -> ppDefToStream(ldef, substream))
                       (subFromTo(rem_defs, 0, min(maxDefsPerFile, num_remaining)))));
               streamWriter(stream, "
(eval-when (:compile-toplevel)
  (compile-file (make-pathname :name (concatenate 'string (pathname-name *compile-file-pathname*) \"" ^ post_fix ^ "\")
                               :defaults *compile-file-pathname*)))
(load (make-pathname :name (concatenate 'string (pathname-name *load-pathname*) \"" ^ post_fix ^ "\")
                     :defaults *load-pathname*))\n");
               writeSubFiles(subFromTo(rem_defs, min(maxDefsPerFile, num_remaining), num_remaining), i + 1))
         in writeSubFiles(defs, 1)))
      

  def ppSpec (s : LispSpec) : PrettyPrint.Pretty =
      let defs = typeDefs(s.opDefns) 	in
      let name = s.name 		in
      prettysAll
     (
     (section (";;; Lisp spec",
	       (List.map (fn pkgName -> string ("(defpackage \"" ^ pkgName ^ "\")"))
	          s.extraPackages)
	       ++
	       [string ("(defpackage :" ^ name ^ ")"),
		string ("(in-package :" ^ name ^ ")")])) 
     ++ 
     (section (";;; Definitions",     List.map ppOpDefn     defs))
%     List.++ [string "#||"] 
%     List.++ section (";;; Axioms",             List.map ppTerm       s.axioms)
%     List.++ [string "||#", emptyPretty ()]
    )

  op ppSpecToTerminal : LispSpec -> ()

  def ppSpecToTerminal spc =
    let p = ppSpec spc in
    let t = format (80, p) in
    toTerminal t

  op ppSpecsToFile : LispSpecs * String * Text -> ()

  def ppSpecsToFile (specs, file, preamble) =
    let ps = List.map ppSpec specs in
    let p  = prettysAll ps in
    let t  = format (80, p) in
    toFile (file, t ++ preamble)

% 
% various utilities for constructing terms:
%

op  mkLVar    : String  -> LispTerm
op  mkLOp     : String  -> LispTerm
op  mkLQuote  : String  -> LispTerm
op  mkLNat    : Nat     -> LispTerm
op  mkLInt    : Int     -> LispTerm
op  mkLChar   : Char    -> LispTerm
op  mkLBool   : Bool    -> LispTerm
op  mkLString : String  -> LispTerm
op  mkLIntern : String  -> LispTerm
op  mkLLambda : Strings  * LispDecls      * LispTerm -> LispTerm
op  mkLIf     : LispTerm * LispTerm       * LispTerm -> LispTerm
op  mkLLet    : Strings  * List(LispTerm) * LispTerm -> LispTerm
op  mkLLetRec : Strings  * List(LispTerm) * LispTerm -> LispTerm
op  mkLApply  : LispTerm * List(LispTerm)            -> LispTerm

def mkLOp s = Op s
def mkLVar s = Var s
def mkLLambda(args,decls,body):LispTerm = 
    Lambda(args,decls,body)
def mkLApply(f,terms) = Apply(f,terms)
def mkLIf(t1,t2,t3) = If(t1,t2,t3)
def mkLLet(vars,terms,term) = 
    if empty? vars then term else Let(vars,terms,term)
def mkLLetRec(vars,terms,term) = Letrec(vars,terms,term)
op mkLSeq(terms: List LispTerm): LispTerm = Seq(terms)

def mkLQuote id = mkLOp ("'" ^ id) 

def mkLNat n = Const(Nat n)
def mkLInt n = if n >= 0
		then mkLNat n
	      else mkLApply(mkLOp "-",[mkLNat (- n)])
def mkLChar ch = Const(Char ch)
def mkLBool b = Const(Boolean b)

def mkLString s =  
    Const(String (IO.formatString1("~S",s)))

def oldMkLString s = 
    translate (fn #" -> "\\\"" | #\\ -> "\\\\" | ch -> Char.show ch) s 

def mkLIntern s = Const(Parameter(":|" ^ s ^ "|"))



op mkDefinition: [A] String * String * A -> (String * Definition)
def mkDefinition(modulename,name,lispterm) =
  let t = Const(Cell (Lisp.cell lispterm)) in
  (modulename,(name,t))

op mkDefinitionWithOp: [A] String * String * String * A -> (String * Definition)
def mkDefinitionWithOp(modulename,name,opname,lispterm) =
  let t = mkLApply(mkLOp opname,[Const(Cell (Lisp.cell lispterm))]) in
  (modulename,(name,t))

op addDefinition: String * Definition * LispSpec -> LispSpec
def addDefinition(modulename,defn,lspc) =
  %let _ = String.writeLine("module: "^modulename^", package: "^lspc.name) in
  let mname = String.map Char.toUpperCase modulename in
  let sname = String.map Char.toUpperCase lspc.name in
  if mname = sname then
  {
   name = lspc.name,
   extraPackages = lspc.extraPackages,
   getter_setters = [],
   ops = lspc.ops,
   axioms = lspc.axioms,
   opDefns = defn::lspc.opDefns
  }
  else lspc

% addDefinitions to LispSpec
op addDefinitions: List (String*Definition) * LispSpec -> LispSpec
def addDefinitions(defns,lspc) =
  List.foldl (fn(lspc,(modulename,defn))
	       -> addDefinition(modulename,defn,lspc)) lspc defns

end-spec

(*

spec TestLispSpecs =

  import LispSpecs
  import PrettyPrint

  def factSpec () : Spec =

    { 
      name 	  = "Fact",
      ops         = ["fact"],
      extraPackages = [],
      axioms      = [],

      opDefns     =
        [("fact",
          Lambda
           (["n"],
            Letrec
              (["fact-iter"],
               [Lambda
                 (["n", "r"],
                  If (Apply (Op " = ", [Var "n", Const (Nat 0)]),
                      Var "r",
                      Apply (Op "fact-iter",
                             [Apply (Op "-", [Var "n", Const (Nat 1)]),
                              Apply (Op "*", [Var "n", Var "r"])])))],
               Apply (Op "fact-iter",
                      [Var "n", Const (Nat 1)]))))]
    }

  def test (n : Nat) : () =
    toTerminal (format (n, ppSpec (factSpec ())))

end-spec

*)
