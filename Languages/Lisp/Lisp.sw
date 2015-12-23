(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% Synchronized with version 1.1 of SW4/Languages/MetaSlang/ToLisp/Lisp.sl

ListADT qualifying spec

import /Library/Legacy/Utilities/Lisp
import /Library/Legacy/DataStructures/ListPair
import /Library/Legacy/DataStructures/TopSort
import /Library/Legacy/DataStructures/MergeSort
import /Library/Structures/Data/Maps/SimpleAsSTHarray
import /Library/Structures/Data/Sets/AsSTHarray
import /Library/PrettyPrinter/BjornerEspinosa
import /Languages/MetaSlang/CodeGen/Generic/SliceSpec
import Suppress

type LispSpec = {name	        : String,
                 extraPackages  : Strings,
     
                 %% these come from #translate pragmas...
                 includes       : Strings,
                 verbatims      : Verbatims,

                 getter_setters : List (String * String),
                 ops            : Strings,
                 axioms         : LispTerms,
                 opDefns        : Definitions,
                 forms          : LispTerms }

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

type LispTerm = | Const   Val
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
                                                                  
type LispDecl = | Ignore  Strings
                  
type Val =      | Boolean   Bool
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

op lispFileLineLength: Nat = 200
op minIndent: Nat = 1

op emptySpec : LispSpec = 
 {name           = "BASESPECS",
  extraPackages  = [],
  includes       = [],
  verbatims      = {pre = [], post = []},
  getter_setters = [],
  ops            = [],
  axioms         = [],
  opDefns        = [],
  forms          = []}

op ops (term : LispTerm, names : Set.Set String) : Set.Set String =
 case term of
   | Const   (Parameter name) -> Set.insert names name
   | Const   _                -> names
   | Op      name             -> Set.insert names name
   | Var     _                -> names
   | Set     (_,  term)       -> ops(term,names)
   | Lambda  (_,_,term)       -> ops(term,names)
   | Apply   (term, terms)    -> foldl (fn (names,tm) -> ops (tm, names)) (ops (term, names)) terms
   | If      (t1, t2, t3)     -> ops (t1,ops (t2, ops (t3, names)))
   | IfThen  (t1, t2)         -> ops (t1,ops (t2, names))
   | Let     (_, terms, body) -> foldl (fn (names, tm) -> ops (tm, names)) (ops (body, names)) terms
   | Letrec  (_, terms, body) -> foldl (fn (names, tm) -> ops (tm, names)) (ops (body, names)) terms
   | Seq     terms            -> foldr ops names terms

op moveDefparamsToEnd? : Bool = true

op nonLambdaDef? ((_, body) : Definition) : Bool =
 ~(embed? Lambda body)

op makeDefNil ((nm, _) : Definition) : Definition =
 (nm, Const (Boolean false))          % nil

op typeDefs (defs : Definitions) : Definitions =
 let defs   = sortGT (fn ((nm1,_),(nm2,_)) -> nm2 <= nm1) defs in
 let defMap = foldl (fn(map, (name,term))-> STHMap.update(map,name,(name,term)))
                    STHMap.emptyMap
                    defs
 in
 let map = 
     foldl (fn (map, (name, term)) -> 
              let opers = ops(term,Set.empty) in
              let opers = Set.toList opers in
              STHMap.update (map, name, opers))
           STHMap.emptyMap 
           defs
 in
 let 
   def find name = 
     case STHMap.apply (map, name) of 
       | None -> [] 
       | Some l -> l 
 in
 let names = topSort (EQUAL, find, List.map (fn (n, _) -> n) defs)    in
 let defs  = mapPartial (fn name -> STHMap.apply (defMap, name)) names in
 let defs  = if moveDefparamsToEnd? then
               let defparams = filter nonLambdaDef? defs in
               let defs = List.map (fn defn ->
                                      if nonLambdaDef? defn then
                                        makeDefNil defn
                                      else 
                                        defn)
                            defs
               in
               defs ++ defparams
             else 
               defs
 in
 defs

%% Printing of characters is temporarily wrong due to bug in lexer.

op ppDecl (decl : LispDecl) : Pretty =
 case decl of
   | Ignore names -> prettysLinearDelim ("(declare (ignore ", " ", ")) ")
                                        (map string names)

op allSelfQuoting? (tms: LispTerms) : Bool =
 forall? (fn tm -> case tm of
                     | Const (Nat     _) -> true
                     | Const (Char    _) -> true
                     | Const (String  _) -> true
                     | Const (Boolean _) -> true
                     | _ -> false)
         tms


op ppTerm (t : LispTerm) : Pretty =
 case t of
   | Const v    -> (case (v : Val) of
                      | Boolean b      -> string (if b then "t" else "nil")
                      | Nat     n      -> string (Nat.show n)
                      | Char    c      -> strings ["\#\\", Char.show c]  % backslash before hash to appease emacs
                      | String  s      -> string s
                      | Symbol  (p, s) -> strings ["'", p, "::", s]
                      | Cell cell      -> strings ["'", anyToString cell]
                      | Parameter s    -> string s)
        
   | Op s       -> strings ["#'", s]

   | Var s      -> string s

   | Set (s, t) -> 
     blockFill (0, [(0, strings ["(setq ", s, " "]),
                    (minIndent, prettysNone [ppTerm t, string ")"])])

   | Lambda (ss, decls, t) -> 
     blockFill (0, [(0, prettysLinearDelim
                       ("#'(lambda (", " ", ") ")
                       (map string ss)),
                    (minIndent+2, prettysAll ((map ppDecl decls) ++ [prettysNone [ppTerm t, string ")"]]))])

   | Apply (Op "list", params) | allSelfQuoting? params ->
     prettysFillDelim ("'(", " ",")")
     (map ppTerm params)

   | Apply (Op "list", [Const (Parameter v)]) ->
     % (list :foo) -> '(:foo)   optimization for nullary constructors
     if v@0 = #: then
       strings ["'(", v, ")"]
     else 
       strings ["(list ", v, ")"]

   | Apply (Op s, ts) ->
     prettysFillDelim ("(", " ",")")
       (Cons (string s, map ppTerm ts))

   | Apply (t, ts) ->
     prettysLinearDelim ("(funcall ", " ",")")
                        (Cons (ppTerm t, map ppTerm ts))

   | If (p, c, a) ->
     prLines minIndent [prLines (2*minIndent) [prConcat[string "(if ", ppTerm p], ppTerm c], prConcat [ppTerm a, string ")"]]

   | IfThen (p, c) ->
     prettysLinearDelim ("(if ", " ", ")")
                        [ppTerm p, ppTerm c]

   | Let (ss, ts, t) ->
     blockAll (0, [(0, prettysAllDelim
                      ("(let (", "", ") ")
                      (ListPair.map (fn (s, t) ->
                                       prettysFillDelim
                                       ("(", " ", ")")
                                       [string s, ppTerm t])
                         (ss, ts))),
                   (minIndent, prettysNone [ppTerm t, string ")"])])

   | Letrec (ss, ts, t) ->
     blockAll (0, [(0, string "(labels "),
                    (minIndent, prettysAllDelim
                       ("(", "", ") ")
                       (ListPair.map (fn (s, Lambda (args, decls, body)) ->
                                        prettysAllDelim
                                        ("(", " ", ")")
                                        [prConcat[string s, string " ",
                                                  prettysLinearDelim ("(", " ", ")")
                                                    (map string args)],
                                         prettysAll ((map ppDecl decls) ++ [prettysNone [ppTerm body]])
                                         ])
                                     (ss, ts))),
                    (minIndent, prettysNone [ppTerm t, string ")"])])

   | Seq ts ->
     let ts = expandSeqs ts in
     prettysLinearDelim ("(progn ", " ", ")")
                        (map ppTerm ts)

op expandSeqs(tms: LispTerms): LispTerms =
  case tms of
    | [] -> []
    | (Seq s_tms) :: r_tms -> expandSeqs s_tms ++ expandSeqs r_tms
    | tm :: r_tms -> tm :: expandSeqs r_tms

op warnAboutSuppressingDefuns? : Bool = false

op ppOpDefn (s : String, term : LispTerm) : Pretty = 
 if s in? SpecToLisp.SuppressGeneratedDefuns then
   let comment = ";;; Suppressing generated def for " ^ s in
   let _ = if warnAboutSuppressingDefuns? then
             toScreen (comment ^ "\n")
           else
             ()
   in
   blockFill (0, [(0, string comment), (0, newline ())])
 else
   case term of
     | Lambda (args, decls, body) ->
       prLines minIndent [prBreak minIndent [string "(defun ", string s,
                                             prettysLinearDelim (" (", " ", ") ")
                                               (map string args)],
                          prettysAll ((map ppDecl decls) ++ [prettysNone [ppTerm body, string ")"]]),
                          emptyPretty()]
     | _ -> 
       blockFill (0, [(0, string "(defparameter "),
                      (0, string s),
                      (0, string " "),
                      (minIndent, prettysNone [ppTerm term,string ")"]),
                      (0, newline ())])

op section (title : String, ps : Prettys) : Prettys =
 Cons (emptyPretty (),
       Cons (string title,
             Cons (emptyPretty (), ps)))

op ppDefToStream (ldef : Definition, stream : Stream) : () =
 let p = ppOpDefn ldef in
 let t = format (lispFileLineLength, p) in
 let _ = toStreamT (t,
                    fn (_,string) -> streamWriter (stream, string),
                    fn (n)        -> streamWriter (stream, newlineAndBlanks n))
 in
 streamWriter (stream, "\n")

  
op maxDefsPerFile: Int = 25000         % Not sure this really matters

op ppSpecToFile (spc : LispSpec, file : String, preamble : String) : () =
 %% Rewritten to not use ppSpec which requires a lot of space for large specs
 let defs = typeDefs(spc.opDefns) in
 let 
   def writer stream =
     let _ = streamWriter (stream, preamble)            in
     let _ = streamWriter (stream, ";;; Lisp spec\n\n") in
     let _ = app (fn pkgName  -> 
                    streamWriter (stream, "(defpackage :" ^ pkgName ^ ")\n"))
                 (sortGT (fn (x,y) -> y <= x) spc.extraPackages)
     in
     let _ = streamWriter (stream, "\n(defpackage :" ^ spc.name ^ ")")     in
     let _ = streamWriter (stream, "\n(in-package :" ^ spc.name ^ ")\n\n") in
     let _ = case spc.verbatims.pre of
               | [] -> ()
               | verbatims -> 
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = streamWriter (stream,";;; Pre-verbatims from pragmas:\n")                                              in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = app (fn verbatim -> streamWriter (stream, verbatim)) verbatims                                         in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = streamWriter (stream,";;; end of pre-verbatims\n")                                                     in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 streamWriter (stream,"\n")                                  
     in
     let _ = streamWriter (stream, "\n(in-package :" ^ spc.name ^ ")\n\n") in
     let _ = streamWriter (stream, ";;; Definitions\n\n") in
    %let _ = streamWriter (stream, "(defmacro System-spec::setq-2 (x y) `(setq ,x ,y))\n\n") in
     let _ = app (fn (getter, setter) -> 
                    streamWriter (stream, "(defsetf " ^ getter ^ " " ^ setter ^ ")\n"))
                 spc.getter_setters
     in
     let _ = if length defs < maxDefsPerFile then
               app (fn ldef -> ppDefToStream(ldef,stream)) defs
             else
               let fileNameBase = subFromTo(file, 0, length file - 5) in   % Remove ".lisp"
               let 

                 def preamble postfix = "
(eval-when (:compile-toplevel)
  (compile-file (make-pathname :name (concatenate 'string (pathname-name *compile-file-pathname*) \"" ^ postfix ^ "\")
                               :defaults *compile-file-pathname*)))
(load (make-pathname :name (concatenate 'string (pathname-name *load-pathname*) \"" ^ postfix ^ "\")
                     :defaults *load-pathname*))\n"

                 def writeSubFiles (rem_defs, i) =
                   if rem_defs = [] then 
                     ()
                   else
                     let postfix       = "--" ^ show i          in
                     let subfileBase   = fileNameBase ^ postfix in
                     let subfile       = subfileBase ^ ".lisp"  in
                     let num_remaining = length rem_defs        in
                     let _ = 
                         IO.withOpenFileForWrite (subfile, 
                                                  fn substream ->
                                                    let _ = streamWriter (substream, "(in-package :" ^ spc.name ^ ")\n\n") in
                                                    app (fn ldef -> ppDefToStream (ldef, substream))
                                                             (subFromTo (rem_defs,
                                                                         0, 
                                                                         min (maxDefsPerFile, num_remaining))))
                     in
                     let _ = streamWriter (stream, preamble postfix) in
                     writeSubFiles (subFromTo (rem_defs, 
                                               min (maxDefsPerFile, num_remaining), 
                                               num_remaining),
                                    i + 1)
               in 
               let _ = writeSubFiles (defs, 1) in
               ()
     in
     let _ = app (fn fm ->
                    let t = format (120, ppTerm fm) in
                    let _ = toStreamT (t,
                                       fn (_, string) -> streamWriter (stream, string),
                                       fn (n)         -> streamWriter (stream, newlineAndBlanks n))
                    in
                    streamWriter(stream,"\n"))
                 spc.forms
     in
     let _ = case spc.verbatims.post of
               | [] -> ()
               | verbatims -> 
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = streamWriter (stream,";;; Post-verbatims from pragmas:\n")                                             in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = app (fn verbatim -> streamWriter (stream, verbatim)) verbatims                                         in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 let _ = streamWriter (stream,";;; end of post-verbatims\n")                                                    in
                 let _ = streamWriter (stream,";;; ------------------------------------------------------------------------\n") in
                 streamWriter (stream,"\n")
     in
     let _ = streamWriter (stream, "\n;;; End-of-file\n") in
     ()
 in
 IO.withOpenFileForWrite (file, writer)

op ppSpec (s : LispSpec) : Pretty =
 let defs = typeDefs(s.opDefns)	in
 let name = s.name              in
 prettysAll ((section (";;; Lisp spec",
                       (map (fn pkgName -> string ("(defpackage \"" ^ pkgName ^ "\")"))
                                 s.extraPackages)
                         ++
                         [string ("(defpackage :" ^ name ^ ")"),
                          string ("(in-package :" ^ name ^ ")")])) 
               ++ 
               (section (";;; Definitions",     map ppOpDefn     defs))
               %     ++ [string "#||"] 
               %     ++ section (";;; Axioms",             map ppTerm       s.axioms)
               %     ++ [string "||#", emptyPretty ()]
               )

op ppSpecToTerminal (spc : LispSpec) : () =
 let p = ppSpec spc in
 let t = format (80, p) in
 toTerminal t

op ppSpecsToFile (specs : LispSpecs, file : String, preamble : Text) : () =
 let ps = map ppSpec specs in
 let p  = prettysAll ps in
 let t  = format (lispFileLineLength, p) in
 toFile (file, t ++ preamble)

% 
% various utilities for constructing terms:
%

op mkLVar    (s  : String)  : LispTerm = Var s
op mkLOp     (s  : String)  : LispTerm = Op  s
op mkLQuote  (id : String)  : LispTerm = mkLOp ("'" ^ id) 
op mkLBool   (b  : Bool)    : LispTerm = Const (Boolean b)
op mkLChar   (c  : Char)    : LispTerm = Const (Char    c)
op mkLString (s  : String)  : LispTerm = Const (String (IO.formatString1 ("~S", s)))
op mkLNat    (n  : Nat)     : LispTerm = Const (Nat     n)
op mkLInt    (n  : Int)     : LispTerm = if n >= 0 then
                                            mkLNat n
                                          else 
                                            mkLApply (mkLOp "-", [mkLNat (- n)])


op mkLIntern (s : String)   : LispTerm = Const (Parameter (":|" ^ s ^ "|"))
op mkLLambda (args  : Strings, 
              decls : LispDecls, 
              body  : LispTerm)
 : LispTerm =
 Lambda (args, decls, body)

op mkLIf  (t1 : LispTerm, t2 : LispTerm, t3 : LispTerm) : LispTerm = If (t1, t2, t3)
op mkLLet (vars : Strings, terms : List LispTerm, term : LispTerm) 
 : LispTerm =
 if empty? vars then 
     term 
 else 
     Let(vars,terms,term)

op mkLLetRec (vars  : Strings, 
              terms : List LispTerm, 
              term  : LispTerm) 
 : LispTerm = 
 Letrec (vars, terms, term)

op mkLApply (f    : LispTerm, 
             args : List LispTerm) 
 : LispTerm = 
 Apply (f, args)

op mkLSeq (terms : List LispTerm) : LispTerm = 
 Seq terms

op [A] mkDefinition (modulename : String, 
                     name       : String, 
                     lispterm   : A)
 : String * Definition =
 let t = Const(Cell (Lisp.cell lispterm)) in
 (modulename, (name, t))

op [A] mkDefinitionWithOp (modulename : String,
                           name       : String,
                           opname     : String,
                           lispterm   : A) 
 : String * Definition =
 let t = mkLApply (mkLOp opname, [Const (Cell (Lisp.cell lispterm))]) in
 (modulename, (name, t))

op addDefinition (modulename : String,
                  defn       : Definition,
                  lspc       : LispSpec) 
 : LispSpec =
 %let _ = String.writeLine("module: "^modulename^", package: "^lspc.name) in
 let mname = String.map Char.toUpperCase modulename in
 let sname = String.map Char.toUpperCase lspc.name in
if mname = sname then
     lspc << {getter_setters = [],
              opDefns = defn::lspc.opDefns}
else 
     lspc

% addDefinitions to LispSpec
op addDefinitions (defns : List (String * Definition), 
                   lspc  : LispSpec) 
 : LispSpec =
 foldl (fn(lspc,(modulename,defn)) ->
               addDefinition (modulename, defn, lspc)) 
            lspc 
            defns

end-spec

(*

spec TestLispSpecs =

import LispSpecs
import PrettyPrint

op factSpec () : Spec =
 {name 	        = "Fact",
  ops           = ["fact"],
  extraPackages = [],
  axioms        = [],
  opDefns       = [("fact",
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

op test (n : Nat) : () =
 toTerminal (format (n, ppSpec (factSpec ())))

end-spec

*)
