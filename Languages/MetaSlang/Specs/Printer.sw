(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*
 * This works but it's a mess. This will be refactored and perhaps
 * rewritten.
 *
 * MetaSlang pretty printer.
 * This module contains utilities for printing terms, types, and patterns to 
 * strings, files, or standard out.
 *
 * Formats supported are:
 *
 *  - Ascii
 *  - HTML
 *  - LaTeX
 *  - pdfLaTeX

 *  - highligthable Ascii
 *)

%% 
%% General comment.
%% This pretty printer targets different format (HTML, LaTeX, Pdf,Ascii)
%% At the same time it is possible to pretty print with path information
%% stored in a markTable variable in a context that is passed down.
%% This adds a lot of clutter to the code. Alternative ways for separating
%% concerns are speculated upon in the file "pretty-printing.sl", and
%% assembled in the document ../doc/deforestation/main.ps.
%% 

% FIXME / TODO: I do not think the path information maintained here is
% ever used by anything...

AnnSpecPrinter qualifying spec 
 import /Languages/SpecCalculus/AbstractSyntax/SCTerm  % SCTerm
 import /Languages/MetaSlang/AbstractSyntax/PrinterSig % printTerm, printType, printPattern
 import /Languages/MetaSlang/AbstractSyntax/Printer
 import AnnSpec
 % import /Library/IO/Primitive/IO                    % getEnv
 import /Library/Legacy/DataStructures/IntSetSplay    % indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay    % markTable's

 import /Languages/SpecCalculus/Semantics/Environment
 % op SpecCalc.getBaseSpec : () -> Spec % defined in /Languages/SpecCalculus/Semantics/Environment
 op printPragmas?: Bool = true

 %% ========================================================================

 type ParentType = | Top | ArrowLeft | ArrowRight | Product | CoProduct | Quotient | Subtype 

 type ParentTerm = | Top | Nonfix | Infix Associativity * Nat

 type PrContext = {
                   pp                 : ATermPrinter,
                   printType          : Bool,
                   topPrintType       : Bool,
                   markSubterm        : Bool,
                   markNumber         : Ref Nat,
                   markTable          : Ref (NatMap.Map (List Nat)),
                   indicesToDisable   : IntSet.Set,
                   sosIndicesToEnable : IntSet.Set
                  }
 
 type IndexLines = Int * Lines

 %% ========================================================================

 op printTyVars                  : TyVars            -> String 
%op printType                    : [a] AType       a -> String 
%op printPattern                 : [a] APattern    a -> String
 op printTypeScheme              : [a] ATypeScheme a -> String 
 op printTermScheme              : [a] ATermScheme a -> String 
% op printTermWithTypes: [a] ATerm       a -> String
 op printSpec                    : [a] ASpec       a -> String
 op latexSpec                    : [a] ASpec       a -> String

 op printSpecToFile              : [a] String * ASpec a -> ()
 op printFlatSpecToFile          : [a] String * ASpec a -> ()
 op latexSpecToFile              : [a] String * ASpec a -> ()
 op printSpecFlatToTerminal      : [a]          ASpec a -> ()
 op printSpecToTerminal          : [a]          ASpec a -> ()
 op printSpecWithTypesToTerminal : [a]          ASpec a -> ()

 op isShortTuple                 : [a] Nat * List (Id * a) -> Bool
 op ppTerm                       : [a] PrContext -> Path * ParentTerm -> ATerm    a -> Pretty
 op ppType                       : [a] PrContext -> Path * ParentType -> AType    a -> Pretty
 op ppPattern                    : [a] PrContext -> Path * Bool * Bool-> APattern a -> Pretty
 op termToPretty                 : [a] ATerm a -> Pretty
 op printTermToTerminal          : [a] ATerm a -> ()
%op printType                    : [a] AType a -> String
 op printTypeToTerminal          : [a] AType a -> ()
%op printTypeScheme              : [a] ATypeScheme a -> String
%op printPattern                 : [a] APattern a -> String
%op printTermWithTypes           : [a] ATerm a -> String
 op ppProperty                   : [a] PrContext -> Nat * AProperty a -> Line
 op ppSpec                       : [a] PrContext -> ASpec a -> Pretty  
 op ppSpecR                      : [a] PrContext -> ASpec a -> Pretty
 op ppSpecHidingImportedStuff    : [a] PrContext -> Spec -> ASpec a -> Pretty
 op ppSpecAll                    : [a] PrContext -> ASpec a -> Pretty
 op ppSpecFlat                   : [a] PrContext -> ASpec a -> Pretty
 op specToPrettyVerbose          : [a] ASpec a -> Pretty
 op specToPrettyVerboseXSymbol   : [a] ASpec a -> Pretty
 op specToPrettyFlat             : [a] ASpec a -> Pretty
 op specToPretty                 : [a] ASpec a -> Pretty
 op specToPrettyXSymbol          : [a] ASpec a -> Pretty
 op specToPrettyR                : [a] ASpec a -> Pretty
%op printSpec                    : [a] ASpec a -> String
 op printSpecXSymbol             : [a] ASpec a -> String
 op printSpecVerbose             : [a] ASpec a -> String
 op printSpecVerboseXSymbol      : [a] ASpec a -> String
 op printSpecFlat                : [a] ASpec a -> String
%op printSpecToTerminal          : [a] ASpec a -> ()
%op printSpecToFile              : [a] String * ASpec a -> ()
 op printMarkedSpecToFile        : [a] String * String * IntSet.Set * IntSet.Set * ASpec a ->          NatMap.Map (List Nat)
 op printMarkedSpecToString      : [a]                   IntSet.Set * IntSet.Set * ASpec a -> String * NatMap.Map (List Nat)
%op printSpecWithTypesToTerminal : [a] ASpec a -> ()
 op latexSpecToPretty            : [a] ASpec a -> Pretty
%op latexSpec                    : [a] ASpec a -> String
%op latexSpecToFile              : [a] String * ASpec a -> ()
 op htmlSpecToPretty             : [a] ASpec a -> Pretty
 op htmlSpecToFile               : [a] String * ASpec a -> ()

 %% ========================================================================

% def toString = PrettyPrint.toString

 def isShortTuple (i, row) = 
   case row of
     | []           -> true
     | (lbl, r) :: row -> lbl = Nat.show i && isShortTuple (i + 1, row)
      
 def initialize (pp, printType?) : PrContext = 
   {pp                 = pp,
    printType          = printType?,
    topPrintType       = printType?,
    markSubterm        = false,
    markNumber         = Ref 0,
    markTable          = Ref NatMap.empty,
    indicesToDisable   = IntSet.empty,
    sosIndicesToEnable = IntSet.empty}
 
 def initializeMark (pp, indicesToDisable, sosIndicesToEnable) : PrContext = 
   {pp                 = pp,
    printType          = false,
    topPrintType       = false,
    markSubterm        = true, 
    markNumber         = (Ref 0),
    markTable          = Ref NatMap.empty,
    indicesToDisable   = indicesToDisable,
    sosIndicesToEnable = sosIndicesToEnable}
 
 def printType?   (c:PrContext) = c.printType
 def markSubterm? (c:PrContext) = c.markSubterm
 
 def [a] termFixity (term : ATerm a) : Fixity = 
   case term of
     | Fun (termOp, srt, _) -> 
       (case termOp of
          | Op(Qualified("List", "Cons"), _) -> Infix (Right, 24)
	  | Op (_, fixity) -> (case fixity of
				 | Unspecified  -> Nonfix
				 | Constructor0 -> Nonfix
				 | Constructor1 -> Nonfix
				 | _ -> fixity)
          | Embed(Qualified(_, "Cons"), true) -> Infix (Right, 24)
	  | And            -> Infix (Right, 15) 
	  | Or             -> Infix (Right, 14) 
	  | Implies        -> Infix (Right, 13) 
	  | Iff            -> Infix (Right, 12) 
	  | Equals         -> Infix (Left, 20) % was 10 ??
	  | NotEquals      -> Infix (Left, 20)
	  | RecordMerge    -> Infix (Left, 25)
	  | _              -> Nonfix)
     | _ -> Nonfix
 
 op escapeString(s: String): String =
   if exists? (fn c -> c = #\\ || c = #\" || c = #\n || c = #\t) s
     then translate (fn #\\ -> "\\\\"
                      | #\" -> "\\\""
                      | #\n -> "\\n"
                      | #\t -> "\\t"
                      | c -> show c)
            s
     else s

%def mkAEquals (srt,pos) = Fun (Equals, srt, pos)

 def [a] printOp (context, 
		  pp     : ATermPrinter, 
		  termOp : AFun  a, 
		  srt    : AType a, 
		  a      : a) 
   : Pretty = 
   case termOp of
     | Op          (idInfo, _) -> pp.ppOpId (idInfo)
     | Bool        b           -> pp.fromString (Bool.show b)
     | Nat         n           -> pp.fromString (Nat.show n)
     | String      s           -> pp.fromString ("\""^escapeString s^"\"")   % "abc"
     | Char        c           -> pp.fromString ("\#"^escapeString(show c))  % \ to appease emacs
     | Embed       (qid, _)    -> pp.ppOpId qid  %"embed("^s^")"
     | Project     s           -> pp.fromString ("project "^s^" ")
     | RecordMerge             -> pp.fromString "<<"
     | Embedded    qid         -> prConcat [pp.fromString "embed? ", pp.ppOpId qid]
     | Quotient    qid         -> pp.fromString ("quotient[" ^ show qid ^ "] ")
     | Choose      qid         -> pp.fromString ("choose["   ^ show qid ^ "] ")
     | PQuotient   qid         -> pp.fromString ("quotient[" ^ show qid ^ "] ")
     | PChoose     qid         -> pp.fromString ("choose["   ^ show qid ^ "] ")
     | Not                     -> pp.Not
     | And                     -> pp.And
     | Or                      -> pp.Or
     | Implies                 -> pp.Implies
     | Iff                     -> pp.Iff
     | Equals                  -> pp.Equals
     | NotEquals               -> pp.NotEquals
     | OneName     (x, _)      -> pp.fromString x
     | TwoNames    (x, y, _)   -> pp.fromString (if x = UnQualified then y else x^"."^ y)
     
     | Relax                   -> let p = case srt of Arrow (Subtype (_, p, _), _, _) -> p | _ -> mkTrueA a in
                                  prettysFill [pp.fromString "relax", 
					       string "(",
					       ppTerm context ([], Top) p, 
					       string ")"]
     | Restrict                -> let p = case srt of Arrow (_, Subtype (_, p, _), _) -> p | _ -> mkTrueA a in
				  prettysFill [pp.fromString "restrict", 
					       string "(",
					       ppTerm context ([], Top) p,
					       string ")"]
     %% Only used internally at present
     | Select (Qualified(_,s)) -> pp.fromString ("select(" ^ s ^ ")")


 def [a] singletonPattern (pat : APattern a) = 
   case pat of
     | AliasPat      _ -> false
     | QuotientPat   _ -> false
     | RestrictedPat _ -> false
     | _               -> true
 
 op [a] stripQual (tm: ATerm a): ATerm a =
   case tm of
     | Fun(Op(Qualified(_, "Cons"), _), s, a) -> Fun(Embed(mkUnQualifiedId "::", true), s, a)
     | Fun(Op(Qualified(_,opName),fx),s,a) | ~alwaysPrintQualifiers? -> Fun(Op(mkUnQualifiedId(opName),fx),s,a)
     | Fun(Embed(Qualified(_, "Cons"), true), s, a) -> Fun(Embed(mkUnQualifiedId "::", true), s, a)
     | _ -> tm

 % FIXME / TODO: I think the paths into patterns here (e.g., [0, i])
 % are wrong
 def printLambda (context, path, marker, match, enclose?, case?) = 
   let pp : ATermPrinter = context.pp in
   let 
     def prRule marker (i, (pat, cond, trm)) par = 
       case cond of
	 | Fun (Bool true, _, _) -> 
	   blockFill (0,
		      [(0, prettysNone [marker,
                                        let context = context << {printType = enclose?} in
					ppPattern context ([0, i] ++ path, enclose?, case?) pat,
					pp.Arrow]),
		       (3, ppTerm context ([2, i] ++ path, par) trm)])
	 | _ -> 
	   blockFill (0,
		      [(0, prettysNone [marker,
					ppPattern context ([0, i] ++ path, enclose?, case?) pat,
					string " ",
					pp.Where,
					string " ",
					ppTerm context ([1, i] ++ path, Top) cond,
					pp.Arrow]),
		       (3, ppTerm context ([3, i] ++ path, par) trm)])
   in
     prettysAll (case match of
		   | [] -> []
		   | rule :: rules -> 
		     [prRule marker (0, rule) (if rules = [] then Top else Nonfix)] ++
		     (ListUtilities.mapWithIndex (fn (i, rule) -> prRule pp.Bar (i + 1, rule) Nonfix) 
		                                 rules))
 
 op [a] ppMonadContents (context: PrContext) (path: Path) (term: ATerm a) (i: Nat): Prettys =
   case term of
     | Apply(Fun (Op(Qualified(_, "monadBind"), _), _, _),
             Record([(_, t1), (_, Lambda([(pat, Fun (Bool true, _, _), t2)], _))], _), _) ->
       let r_prettys = ppMonadContents context path t2 (i+1) in
       (case pat of
        | WildPat _ -> ppTerm context (i :: path, Top) t1
        | _ -> blockFill (0, [(0, ppPattern context ([0, i] ++ path, false, false) pat),
                              (1, string " <- "),
                              (2, ppTerm context ([1, i] ++ path, Top) t1)]))
       
        :: r_prettys
     | _ -> [ppTerm context (i :: path, Top) term]

 def ppTermScheme context parent (tvs, term) = 
   let pp1 = ppForallTyVars context.pp tvs in
   let pp2 = ppTerm context parent term in
   prettysNone [pp1, pp2]     

 def ppTerm context (path, parentTerm) term =
   let pretty = ppTerm1 context (path, parentTerm) term in
   if markSubterm? context then
     let num = State.! context.markNumber in
     let table = State.! context.markTable in
     (context.markTable State.:= NatMap.insert (table, num, path);
      context.markNumber State.:= num + 1;
      PrettyPrint.markPretty (num, pretty))
   else 
     pretty

 op printLocalDefTypes?: Bool = true
 op useMonadSyntax?: Bool = true

 def [a] ppTerm1 context (path, parentTerm) (term: ATerm a) : Pretty =
   let pp : ATermPrinter = context.pp in
   let % Function application is printed taking special cases into account
     def prApply (t1, t2) = 
       case (t1, t2) of
	 | (Lambda (rules as (_ :: _), _), _) ->
	   % Print lambda abstraction as
	   % case pattern matching
           enclose(~(embed? Top parentTerm), pp,
                   blockAll (0, 
                             [(1, prettysNone [pp.Case, ppTerm context ([1] ++ path, Top) t2]), 
                              (1, prettysNone 
                                    [printLambda (context, [0] ++ path, pp.Bar, rules, false, true)])]))
	   % Print tuple projection using
	   % dot notation.
	 | (Fun (Project p, srt1, _), Var ((id, srt2), _)) ->
	   if printType? context then
	     prettysNone [pp.fromString id, 
			  string ":", 
			  ppType context ([0, 1] ++ path, Top) srt2, 
			  string ".", 
			  string p, 
			  string ":", 
			  ppType context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [pp.fromString id, string ".", pp.fromString p]
	 | (Fun (Project p, srt1, _), tm as Fun _) ->
	   if printType? context then
	     prettysNone [ppTerm context (path, parentTerm) tm,
			  string ":", 
			  ppType context ([0, 1] ++ path, Top) (termType tm),
			  string ".", 
			  string p, 
			  string ":", 
			  ppType context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [ppTerm context (path, parentTerm) tm, string ".", pp.fromString p]
	 | (Fun (Project p, srt1, _), tm) ->
	   if printType? context then
	     prettysNone [string "(",
			  ppTerm context (path, parentTerm) tm,
			  string ":", 
			  ppType context ([0, 1] ++ path, Top) (termType tm),
			  string ").",
			  string p, 
			  string ":", 
			  ppType context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [string "(",
			  ppTerm context (path, parentTerm) tm, 
			  string ").", 
			  pp.fromString p]
         | (Fun (Op(Qualified(_, "monadBind"), _), _, _),
            Record([(_, t1), (_, Lambda([(pat, Fun (Bool true, _, _), t2)], _))], _)) | useMonadSyntax? ->
           %% {pat <- t1; t2}
           prettysNone [pp.LCurly,
                        prettysAll (addSeparator (string ";") (ppMonadContents context path term 0)),
                        pp.RCurly]
	 | _ -> 
	   blockLinear (0, 
                        [(0, prettysNone([ppTerm context ([0] ++ path, Nonfix) t1]
                                           ++ (if embed? Var t2
                                                 || (case t2 of
                                                       | Fun(f, _, _) -> true 
                                                       | _ -> false)
                                                 || (case t1 of
                                                       | Fun(f, _, _) ->
                                                         (case f of
                                                            | Not -> false
                                                            | Op _ -> false
                                                            | Embed _ -> false
                                                            | _ -> true)
                                                       | _ -> true)
                                                 then [string " "] else []))), 
                         (2, blockNone (0, 
                                        (case t2 of
                                           | Record (row, _) ->
                                             if isShortTuple (1, row) then
                                               %% We want the application to be mouse-sensitive not
                                               %% just the argument list--otherwise there is no way to
                                               %% select the application which is what you normally want
                                               [(0, ppTerm1 context ([1] ++ path, Top) t2)]
                                             else 
                                               [(0, ppTerm context ([1] ++ path, Top) t2)]
                                           | Var _ -> 
                                             [(0, ppTerm context ([1] ++ path, Top) t2)]
                                           | Fun(f, _, _) ->
                                             (case f of
                                              | Op(Qualified(q,id), Infix _) ->
                                                [(0, enclose(true, pp,
                                                             if id = "*" then string " * "
                                                             else ppTerm context ([1] ++ path, Top) t2))]
                                              | _ -> [(0, ppTerm context ([1] ++ path, Top) t2)])
                                           | _ -> 
                                             [(0, pp.LP), 
                                              (0, ppTerm context ([1] ++ path, Top) t2), 
                                              (0, pp.RP)])))])
   in
   case isFiniteList term of
     | Some terms -> ppListPath path (fn (path, term) -> ppTerm context (path, Top) term)
                       (pp.LBrack, pp.Comma, pp.RBrack)  terms
     | None -> 
       (case term of
	  | Fun (top, srt, a) -> 
	    if printType? context then
	      blockFill (0, 
			 [(0, printOp (context, pp, top, srt, a)), 
			  (0, string ": "), 
			  (2, ppType context ([0] ++ path, Top) srt)])
	    else 
	      printOp (context, pp, top, srt, a)
	  | Var ((id, srt), _) -> 
	    if printType? context then
	      blockFill (0, 
			 [(0, pp.fromString id), 
			  (0, string ": "), 
			  (0, ppType context ([0] ++ path, Top) srt)])
	    else 
	      pp.fromString id
	  | Let (decls, body, _) -> 
	    let 
              def ppD (index, separatorLength, separator, pat, trm) = 
		case (pat, trm) of
		  | (VarPat _, Lambda ([(pat2, Fun (Bool true, _, _), body)], _)) ->
		    (0, blockLinear (0, 
				     [(0, prettysNone [separator, 
						       ppPattern context ([0, index]++ path, false, false) pat, 
						       string " ", 
						       ppPattern context ([0, 1, index]++ path, true, false) pat2, 
						       string " ", 
						       pp.Equals, 
						       string " "]), 
				      (separatorLength, 
				       prettysNone [ppTerm context
						           ([2, 1, index]++ path, Top)
							   body, 
						    string " "])])) 
		  | _ -> 
		    (0, blockLinear (0, 
				     [(0, prettysNone [separator, 
						       ppPattern context ([0, index]++ path, true, false) pat, 
						       string " ", 
						       pp.Equals, 
						       string " "]), 
				      (separatorLength, 
				       prettysNone [ppTerm context 
						           ([1, index]++ path, Top) 
						           trm, 
						    string " "])]))
	    in
	    let 
	      def ppDs (index, l, separator, decls) = 
		case decls of
		  | [] -> []
		  | (pat, trm) :: decls -> Cons (ppD (index, l, separator, pat, trm), 
						 ppDs (index + 1, 5, pp.LetDeclsAnd, decls))
	    in
	      enclose(case parentTerm of
			| Infix _ -> true   % Add parens if inside infix expression
			| _ -> false, pp,
		      blockAll (0, 
				[(0, blockLinear (0, 
						  [(0, blockLinear (0, ppDs (0, 4, pp.Let, decls))), 
						   (0, pp.In)])), 
				 (0, ppTerm context ([length decls] ++ path, parentTerm) body)]))
	  | LetRec (decls, body, _) -> 
            let
              def ppD (path, ((id, srt), trm)) =
                (case trm of
		   | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
		     blockLinear (0, 
				  [(0, prettysNone ([pp.Def, 
                                                     pp.fromString id, 
                                                     string " ",
                                                     let context = context << {printType = printLocalDefTypes?} in
                                                     ppPattern context ([1, 0] ++ path, true, false) pat]
                                                 ++ (case srt of
                                                       | Arrow(dom,rng, apos) | printLocalDefTypes? ->
                                                         [string ": ", 
                                                          ppType context ([1] ++ path, Top) rng]
                                                       | _ -> [])
                                                 ++ [string " ", 
                                                     pp.Equals, 
                                                     string " "])), 
				   (2, ppTerm context ([2, 0] ++ path, Top)
				    body)])
		   | _ -> 
		     blockLinear (0, 
				 [(0, prettysNone
				   [pp.Def, 
				    pp.fromString id, 
				    pp.Equals]), 
				  (4, ppTerm context (path, Top) trm)]))
            in
              enclose(case parentTerm of
			| Infix _ -> true % Add parens if inside an infix expr
			| _ -> false, pp,
		      blockAll (0, 
			[(0, blockNone (0, 
				      [(0, pp.Let), 
				       (0, AnnTermPrinter.ppListPath path ppD
					(pp.Empty, pp.Empty, pp.Empty) decls)])), 
			 (0, pp.In), 
			 (0, ppTerm context ([length decls]++ path, parentTerm) body)]))
	  | Record (row, _) ->
	    if isShortTuple (1, row) then
	      AnnTermPrinter.ppListPath path (fn (path, (_, t)) ->
					      ppTerm context
					      (path, Top) t)
	                                     (pp.LP, pp.Comma, pp.RP) row
	    else
	      let
	        def ppEntry (path, (id, t)) = 
		  blockFill (0, 
			     [(0, prettysNone [pp.fromString  id, 
					      string  " = "]), 
                              (2, ppTerm context (path, Top) t)])
	      in
		AnnTermPrinter.ppListPath path ppEntry (pp.LCurly, string ", ", pp.RCurly) row
	  | IfThenElse (t1, t2, t3, _) -> 
	    enclose(case parentTerm of
			| Infix _ -> true % Add parens if inside an infix expr
			| _ -> false, pp,
		    blockLinear (0, 
		       [(0, prettys [pp.If, ppTerm context ([0]++ path, Top) t1]), 
			(0, blockFill (0, 
				       [(0, pp.Then), 
					(3, ppTerm context ([1]++ path, Top) t2), 
					(0, string " ")])), 
			(0, blockFill (0, 
				       [(0, pp.Else), 
					(0, ppTerm context ([2]++ path, Top) t3)]))]))
	  | Lambda (match, _) -> 
	    enclose(~(embed? Top parentTerm), pp,
                    printLambda (context, path, pp.Lambda, match, true, false))
          | The ((id,srt),body,_) ->
	    enclose(~(embed? Top parentTerm), pp,
		    blockFill (0, [
			  (0, prettysNone 
			   [pp.The,
			    pp.LP,
			    pp.fromString id, 
			    string ": ", 
			    ppType context ([2] ++ path, Top) srt,
			    pp.RP, string " "
			   ]), 
			  (1, ppTerm context ([2] ++ path, Top) body)]))

	  | Bind (binder, bound, body, _) ->
	    let b = case binder of
		      | Forall -> pp.Fa
		      | Exists -> pp.Ex
		      | Exists1 -> pp.Ex1
	    in
	    let 
	      def ppBound (index, (id, srt)) =
		(prettys [pp.fromString id, 
			  string ": ", 
			  ppType context ([index]++ path, Top) srt])
	    in
	      enclose(case parentTerm of
			| Infix _ -> true % Add parens if inside an infix expr
			| _ -> false, pp,
		      blockFill (0, [
			    (0, prettysNone 
			     [b, pp.LP, 
			      prettysFill (addSeparator (string ", ") 
					  (ListUtilities.mapWithIndex ppBound bound)), 
			      pp.RP, 
			      string " "]), 
			    (1, ppTerm context ([length bound]++ path, parentTerm) body)]))
              
	  | Seq (ts, _) -> AnnTermPrinter.ppListPath path
	                                           (fn (path, trm) -> ppTerm context (path, Top) trm) 
						   (pp.LP, string ";", pp.RP)  ts
	  | Apply (trm1, trm2 as Record ([(_, t1), (_, t2)], _), _) ->
            let conj_or_disj? = case trm1 of
                                  | Fun(And,_,_) -> true
                                  | Fun(Or,_,_)  -> true
                                  | _ -> false
            in
            let
	      def prInfix (f1, f2, l, t1, oper, t2, r, nested?) =
                let arg_pp = 
                      [prettysNone [l, 
                                    ppTerm context ([0, 1]++ path, f1) t1, 
                                    string " "],
                       %% Don't want qualifiers on infix ops
                       prettysNone [ppTerm context ([0]++ path, Top) (stripQual oper), 
                                    string " ", 
                                    ppTerm context ([1, 1]++ path, f2) t2, 
                                    r]]
                in
                if nested? && conj_or_disj?
                   then prLines (-3) arg_pp
                 else prBreak 1 arg_pp
	    in
	      %
	      % Infix printing is to be completed.
	      %
              (case (parentTerm, termFixity (trm1)) of
                 | (_, Nonfix) -> prApply (trm1, trm2)
                 | (Nonfix, Infix (a, p)) ->
                    prInfix (Infix (Left, p), Infix (Right, p), pp.LP, t1, trm1, t2, pp.RP, false)
                 | (Top, Infix (a, p))  ->
                    prInfix (Infix (Left, p), Infix (Right, p), pp.Empty, t1, trm1, t2, pp.Empty, false) 
                 | (Infix (a1, p1), Infix (a2, p2)) ->
		   if p1 = p2 then
		     (if a1 = a2 then
			prInfix (Infix (Left, p2), Infix (Right, p2), pp.Empty, t1, trm1, t2, pp.Empty, true)
		      else
			prInfix (Infix (Left, p2), Infix (Right, p2), pp.LP, t1, trm1, t2, pp.RP, false))
		   else if p2 > p1 then
		     %% Inner has higher precedence
		     prInfix (Infix (Left, p2), Infix (Right, p2), pp.Empty, t1, trm1, t2, pp.Empty, false)
		   else 
		     prInfix (Infix (Left, p2), Infix (Right, p2), pp.LP, t1, trm1, t2, pp.RP, false))
	  | Apply (t1, t2, _) -> prApply (t1, t2)
	  | ApplyN ([t], _) -> ppTerm context (path, parentTerm) t
	  | ApplyN ([trm1, trm2 as Record ([(_, t1), (_, t2)], _)], _) ->
            let
              def prInfix (f1, f2, l, t1, oper, t2, r) =
		prettysLinear [l, 
			       ppTerm context ([0, 1]++ path, f1) t1, 
			       string " ", 
			       ppTerm context ([0]++ path, Top) oper, 
			       string " ", 
			       ppTerm context ([1, 1]++ path, f2) t2, 
			       r]
	    in
	      %
	      % Infix printing is to be completed.
	      %
	      (case (parentTerm, (termFixity trm1):Fixity) of
		 | (_, Nonfix) -> prApply (trm1, trm2)
		 | (Nonfix, Infix (a, p)) ->
	           prInfix (Nonfix, Nonfix, pp.LP, t1, trm1, t2, pp.RP)
		 | (Top, Infix (a, p))  ->
		   prInfix (Nonfix, Nonfix, pp.Empty, t1, trm1, t2, pp.Empty) 
		 | (Infix (a1, p1), Infix (a2, p2)) ->
		   prInfix (Nonfix, Nonfix, pp.LP, t1, trm1, t2, pp.RP))
	  | ApplyN ([t1, t2], _) -> prApply (t1, t2)
	  | ApplyN (t1 :: t2 :: ts, a) -> prApply (ApplyN ([t1, t2], a), ApplyN (ts, a))
	  | TypedTerm (t, s, _) -> 
	    (case s of
	      | MetaTyVar _ ->  
	        ppTerm context ([0] ++ path, Top) t
	      | _ ->
	        prettysFill [ppTerm context ([0]++ path, Top) t, 
			     prettysNone[string ":", string " ", 
                                         ppType context ([1]++ path, Top) s]])
          | Transform (tfm, _) -> ppTransformExpr context.pp tfm
	  | Pi (tvs, tm, _) ->
	    let pp1 = ppForallTyVars context.pp tvs in
	    let pp2 = ppTerm context (path, parentTerm) tm in
	    prettysNone [pp1, string " ", pp2]     

          | Any _ -> string "<anyterm>"
          | And (tms, _) -> let _ = debug("and") in prettysFill ([string "<AndTerms: "] 
					 ++
					 (foldl (fn (pps, tm) -> 
						 pps ++
						 [ppTerm context (path, Top) tm,
						  string " "])
					        []
						tms)
					 ++
					 [string ">"])
	  | _ -> System.fail "Uncovered case for term")
      

 def ppTypeScheme context parent (tyVars, srt) = 
   let pp2 = ppType context parent srt in
   let pp1 = ppForallTyVars context.pp tyVars in
   prettysNone [pp1, string " ", pp2]     

 def ppType context (path, parent) srt = 
   let pp : ATermPrinter = context.pp in
   case srt of

     | CoProduct (row, _) -> 
       let
         def ppEntry (path, (qid, srtOption)) = 
	   case srtOption of
	     | Some s -> 
	       prettysNone [pp.Bar, 
			    pp.ppOpId qid, 
			    string  " ", 
			    ppType context (path, CoProduct) s]
	     | None -> 
	       prettysNone [pp.Bar, 
			    pp.ppOpId  qid]
       in
       let (left, right) = 
           case parent of
	     | Product   -> (pp.LP, pp.RP)
	     | CoProduct -> (pp.LP, pp.RP)
	     | Subtype   -> (pp.LP, pp.RP)
	     | _ -> (pp.Empty, pp.Empty)
       in
	 AnnTermPrinter.ppListPath path ppEntry (left, pp.Empty, right) row

    | Product ([], _) -> string  "()"

    | Product (row, _) -> 
      if isShortTuple (1, row) then
	let (left, right) = 
	    case parent of
	      | Product -> (pp.LP, pp.RP)
	      | Subtype -> (pp.LP, pp.RP)
	      | _ -> (pp.Empty, pp.Empty)
	in
	  AnnTermPrinter.ppListPath path 
	                            (fn (path, (lbl, t)) -> ppType context (path, Product) t) 
				    (left, pp.Product, right) 
	                            row
      else
	let                  
	  def ppEntry (path, (id, s)) = 
	    blockFill (0, 
		       [(0, pp.fromString  id), 
			(0, string  ": "), 
			(0, ppType context (path, Top) s)])
	in
	  AnnTermPrinter.ppListPath path ppEntry (pp.LCurly, string ", ", pp.RCurly)  row
              
    | Arrow (dom, rng, _) -> 
      let (left, right) = 
          case parent of
	    | Product   -> (pp.LP, pp.RP)
	    | ArrowLeft -> (pp.LP, pp.RP)
	    | Subtype   -> (pp.LP, pp.RP)
	    | _ -> (pp.Empty, pp.Empty)
      in
	blockFill (0, 
		   [(0, prettysNone [left, 
				     ppType context ([0]++ path, ArrowLeft  : ParentType) dom, 
				     pp.Arrow]), 
		    (3, prettysNone [ppType context ([1]++ path, ArrowRight : ParentType) rng, 
				     right])])

    | Subtype (s, Lambda ([(pat, Fun (Bool true, _, _), t)], _), _) ->
      let context = context << {printType = context.topPrintType} in
      prettysNone [pp.LCurly,
                   blockFill (0, 
                              [(0, ppPattern context ([0, 0, 1] ++ path, true, false) pat), 
                               (0, string ": "), 
                               (0, ppType    context ([0]       ++ path, Subtype) s), 
                               (0, pp.Bar), 
                               (0, ppTerm    context ([2, 0, 1] ++ path, Top) t)]),
                   pp.RCurly]
    | Subtype (s, t, _) -> 
      let context = context << {printType = context.topPrintType} in
      blockFill (0, 
		 [(0, pp.LP), 
		  (0, ppType context ([0] ++ path, Subtype) s), 
		  (0, pp.Bar), 
		  (0, ppTerm context ([1] ++ path, Top) t), 
		  (0, pp.RP)])
    | Quotient (s, t, _) -> 
      let context = context << {printType = context.topPrintType} in
      blockFill (0, 
		 [(0, pp.LP), 
		  (0, ppType context ([0] ++ path, Top) s), 
		  (0, string  " / "), 
		  (0, ppTerm context ([1] ++ path, Top) t), 
		  (0, pp.RP)])

  % | Base (Qualified ("String", "String"))  -> string "String"
  % | Base (Qualified ("Nat",    "Nat"))     -> string "Nat"

    | Boolean _ -> string "Bool"

    | Base (idInfo, [], _) -> pp.ppTypeId idInfo

    | Base (idInfo, ts, _) -> 
      blockFill (0, 
		 [(0, pp.ppTypeId idInfo), 
		  (0, AnnTermPrinter.ppListPath path
		   (fn (path, srt) -> ppType context (path, Top : ParentType) srt)
		   (pp.LP, pp.Comma, pp.RP) ts)])

%    | PBase (idInfo, [], _) -> pp.ppPTypeId (idInfo)

%    | PBase (idInfo, ts, _) -> 
%            blockFill (0, 
%                [(0, pp.ppPTypeId idInfo), 
%                 (0, AnnTermPrinter.ppListPath path
%                      (fn (path, srt) -> ppType context (path, Top : ParentType) srt)
%                      (pp.LP, pp.Comma, pp.RP) ts)])

    | TyVar (id, _) -> string id

    | MetaTyVar (mtv, _) -> string (TyVarString mtv)

    | Pi (tvs, srt, _) ->
      let pp1 = ppForallTyVars context.pp tvs in
      let pp2 = ppType context (path, parent) srt in
      prettysNone [pp1, string " ", pp2]     

    | Any _ -> string ("<anytype>")

    | And (srts, _) -> prettysNone ([string "<AndTypes: "] 
				    ++
				    (foldl (fn (pps, srt) -> 
					    pps ++
					    [ppType context (path, Top : ParentType) srt,
					     string " "])
				           []
					   srts)
				    ++
				    [string ">"])

    | _ -> string ("ignoring mystery type: " ^ (anyToString srt))
      
 op showBoundMetaTyvarInfo?: Bool = false

 def [a] TyVarString (mtv: AMetaTyVar a) : String =
   let {link, uniqueId, name} = State.! mtv in
   case link of
    | None -> "mtv%"^(if showBoundMetaTyvarInfo? then name^"%" else "")^ show uniqueId
    | Some srt -> (if showBoundMetaTyvarInfo?
                     then "mtv%"^name^"%"^ show uniqueId ^": "
                     else "")
                 ^ printType srt

  %% More elaborate version
  %     let linkr =
  %       case link
  %         of None  -> ""
  %          | Some srt -> "["^printType srt^"]"
  %     in "mtv%"^Nat.show uniqueId^linkr

 def enclose (enclose?, pp, pretty) = 
   if enclose? then
     prettysNone [pp.LP, pretty, pp.RP]
   else
     pretty 

  def ppPattern context (path, enclose?, case?) pattern = 
   let pp : ATermPrinter = context.pp in
   case pattern of
     | WildPat   (_(* srt *), _) -> pp.Underscore
     | BoolPat   (b, _) -> string (show b)
     | NatPat    (n, _) -> string (show n)
     | StringPat (s, _) -> pp.fromString ("\""^escapeString s^"\"")         % "abc"
     | CharPat   (c, _) -> pp.fromString ("\#"^escapeString(show c))      % \ to appease emacs 

     | VarPat    ((id, srt), _) -> 
       if printType? context then
	 enclose (enclose?, pp,
                  blockFill (0, 
                             [(0, pp.fromString id), 
                              (0, string ": "), 
                              (2, ppType context ([0] ++ path, Top : ParentType) srt)]))
       else 
	 pp.fromString id
     | EmbedPat  (Qualified(_, "Nil"), None, ty, _) | listType?(ty) -> string "[]"
     | EmbedPat  (qid, None, _, _) -> pp.ppOpId qid
     | RecordPat (row, _) ->
       if isShortTuple (1, row) then
	 AnnTermPrinter.ppListPath path 
	                           (fn (path, (id, pat)) -> ppPattern context (path, embed? RecordPat pat, false) pat) 
				   (if enclose? || case? then (pp.LP, pp.Comma, pp.RP)
                                    else (pp.Empty, pp.Comma, pp.Empty)) 
				   row
       else
	 let 
           def ppEntry (path, (id, pat)) = 
	     blockFill (0, 
			[(0, prettysNone [pp.fromString id, string " ", pp.Equals, string " "]), 
			 (2, 
			  prettysFill [ppPattern context (path, false, false) pat])])
	 in
	   ppListPath path ppEntry (pp.LCurly, pp.Comma, pp.RCurly) row
     | EmbedPat (Qualified(_,"Cons"), 
		 Some (RecordPat ([("1", p1), ("2", p2)], _)), 
		 Base (_, [_], _), _) ->
       (case isFiniteListPat pattern of
          | Some pats -> ppListPath path (fn (path, term) -> ppPattern context (path, true, false) term)
                           (pp.LBrack, pp.Comma, pp.RBrack) pats
          | None ->
            enclose (enclose?, pp, 
                     prettysFill [ppPattern context ([0]++ path, true, false) p1, 
                                  string " :: ", 
                                  ppPattern context ([1]++ path, false, false) p2]))
 %  | EmbedPat ("Cons", 
 %             Some (RecordPat ([("1", p1), ("2", p2)], _)), 
 %              PBase (_(* Qualified ("List", "List") *), [_], _), _) -> 
 %   enclose (enclose?, 
 %           prettysFill [ppPattern context ([0]++ path, false) p1, 
 %                        string " :: ", 
 %                        ppPattern context ([1]++ path, false) p2])
     | EmbedPat (qid, Some pat, _(* srt *), _) -> 
       enclose (enclose?, pp,
		blockFill (0, (Cons ((0, pp.ppOpId qid), 
                                     if singletonPattern pat then
                                       [(0, string " "), 
                                        (2, ppPattern context ([0]++ path, true, false) pat)]
                                     else
                                       [(2, prettysNone[pp.LP, 
                                                        ppPattern context ([0]++ path, false, false) pat,
                                                        pp.RP])]))))
     | TypedPat (pat, srt, _) -> 
       enclose (enclose?, pp,
		blockFill (0, 
			   [(0, ppPattern context ([0]++ path, true, false) pat), 
			    (0, string  ": "), 
			    (0, ppType context ([1]++ path, Top : ParentType) srt)]))
     | AliasPat (pat1, pat2, _) -> 
       enclose (enclose?, pp,
		blockFill (0, 
			   [(0, let context = context << {printType = context.topPrintType} in
                                ppPattern context ([0]++ path, true, false) pat1), 
			    (0, string  " as "), 
			    (0, ppPattern context ([1]++ path, true, false) pat2)]))
     | QuotientPat (pat, qid, _, _) -> 
       enclose (enclose?, pp,
		blockFill (0, 
			   [(0, string ("quotient[" ^ show qid ^ "] ")),
			    (0, ppPattern context ([0]++ path, true, false) pat)]))
     | RestrictedPat(pat, Lambda([(p_pat, _, p_bod)], _), _) | equalPattern?(pat, p_pat) ->
       enclose (true, pp,
                blockFill(0, [(0, ppPattern context ([0]++ path, false, false) pat),
                              (2, prettysNone [pp.Bar,
                                               let context = context << {printType = context.topPrintType} in
                                               ppTerm context ([1]++ path, Top) p_bod])]))

     | RestrictedPat (pat, term, _) ->
%% Don't want restriction expression inside parentheses in normal case statement
%       (case pat of
%	  | RecordPat (row, _) ->
%	    %% This probably isn't quite right as far as formatting the "|" term
%	    let def ppListPathPlus path f (left, sep, right) ps = 
%	          prettysNone ([left,
%			       prettysLinear (addSeparator sep 
%					      (mapWithIndex (fn (i, x) ->
%							     f (Cons (i, path), x)) ps))]
%		               ++ [pp.Bar,ppTerm context ([1]++ path, Top) term]
%			       ++ [right])
%	    in
%	    if isShortTuple (1, row) then
%	      ppListPathPlus path 
%	        (fn (path, (id, pat)) -> ppPattern context (path, true) pat) 
%		(pp.LP, pp.Comma, pp.RP) 
%		row
%	    else
%	      let 
%		def ppEntry (path, (id, pat)) = 
%		  blockFill (0, 
%			     [(0, prettysNone [pp.fromString id, string " ", pp.Equals, string " "]), 
%			      (2, 
%			       prettysFill [ppPattern context (path, true) pat])])
%	      in
%		ppListPathPlus path ppEntry (pp.LCurly, pp.Comma, pp.RCurly) row
%	   | _ ->
	     enclose (enclose?, pp,
		      blockFill (0, 
				 [(0, ppPattern context ([0]++ path, false, false) pat), 
				  (1, blockNone (0, [(0, pp.Bar), 
                                                     (0,
                                                      let context = context << {printType = context.topPrintType} in
                                                      ppTerm context ([1]++ path, Top) term)]))])) %)

     | _ -> System.fail "Uncovered2 case for pattern"
      

 def printTyVars tvs =
   case tvs of
     | []     -> "[]"
     | v1::vs -> "[" ^ v1 ^ (foldl (fn (str, v) -> str ^","^ v) "" vs) ^ "]"

 def useXSymbols? = false
 def uiPrinter() = if useXSymbols? then XSymbolPrinter else asciiPrinter

 op printWidth: Nat = 105

 def AnnSpecPrinter.printTermPP term =
   ppTerm (initialize (asciiPrinter, false)) ([], Top) term

 def AnnSpecPrinter.printTerm term = 
   PrettyPrint.toString (format (printWidth, printTermPP term))

 op [a]  printTermIndent(indent: Nat, term: ATerm a): String = 
     let indent   = PrettyPrint.blanks indent in
     let context  = initialize(asciiPrinter,false) in 
     let argument = ([],Top) in
     let termPP   = ppTerm context argument term in
     let termPP   = PrettyPrint.prettysNone [PrettyPrint.string indent,termPP] in
     PrettyPrint.toString(PrettyPrint.format(100,termPP))

 def termToPretty term =
   ppTerm (initialize (asciiPrinter, false)) ([], Top) term

 def printTermToTerminal term =
   toTerminal (format (printWidth, ppTerm (initialize (uiPrinter(), false)) 
		                  ([], Top) 
				  term))
 
 def AnnSpecPrinter.printTypePP srt =
   ppType (initialize (asciiPrinter, false)) ([], Top : ParentType) srt

 def AnnSpecPrinter.printType srt = 
    PrettyPrint.toString (format (printWidth, printTypePP srt))

 op [a] printTypeWithTypes(srt: AType a): String =
   toString (format (printWidth, ppType (initialize (asciiPrinter, true))
                           ([], Top : ParentType) 
                           srt))

 def printTypeToTerminal srt = 
   toTerminal (format (printWidth, ppType (initialize (uiPrinter(), false))
		                  ([], Top : ParentType) 
				  srt))
 
 def printTypeScheme scheme = 
   PrettyPrint.toString (format (printWidth, ppTypeScheme (initialize (asciiPrinter, false))
				                  ([], Top)
						  scheme))

 def printTermScheme scheme = 
   PrettyPrint.toString (format (printWidth, ppTermScheme (initialize (asciiPrinter, false))
				                  ([], Top) 
						  scheme))

 def AnnSpecPrinter.printPattern pat = 
   PrettyPrint.toString (format (printWidth, ppPattern (initialize (asciiPrinter, false))
			                       ([], false, false) 
					       pat))

 op AnnSpecPrinter.printPatternWithTypes (pat: MSPattern): String = 
   PrettyPrint.toString (format (printWidth, ppPattern (initialize (asciiPrinter, true))
			                       ([], false, false) 
					       pat))

 def AnnSpecPrinter.printTermWithTypes term = 
   PrettyPrint.toString (format (printWidth, ppTerm (initialize (asciiPrinter, true))
			                    ([], Top)
					    term))

 def ppForallTyVars (pp : ATermPrinter) tyVars = 
   case tyVars of
     | [] -> string ""
     | _ -> AnnTermPrinter.ppList string 
                                  (pp.LBrack, pp.Comma, pp.RBrack)
                                  tyVars

 def ppTyVars (pp : ATermPrinter) tvs = 
   case tvs of
     | [] -> string ""
     | _ -> AnnTermPrinter.ppList string (pp.LP, pp.Comma, pp.RP) tvs

 def typeIndex     = 0
 def opIndex       = 1
 def defIndex      = 2
 def propertyIndex = 3

 def ppProperty context (index, (pt, name as Qualified (q, id), tyVars, term, _)) = 
   let pp : ATermPrinter = context.pp in
   let button1 = (if markSubterm? context then
		    PrettyPrint.buttonPretty (~(IntSet.member (context.indicesToDisable, index)), 
					      index, string " ", false) 
		  else 
		    string "")
   in
   let button2 = (if markSubterm? context then
                    PrettyPrint.buttonPretty (IntSet.member (context.sosIndicesToEnable, index), 
					      index, string " ", true) 
		  else 
		    string "")
   in
     (0, blockFill (0, [(0, button1), 
			(0, button2), 
			(0, case (pt:PropertyType) of
			      | Theorem    -> pp.Theorem 
			      | Axiom      -> pp.Axiom 
			      | Conjecture -> pp.Conjecture), 
			(0, pp.ppFormulaDesc (" "^ (if q = UnQualified then "" else q^".")^id)), 
			(0, string " "), 
			(0, pp.Is), 
                        (0, if empty? tyVars then string "" else string " "), 
			(0, ppForallTyVars pp tyVars), 
			(0, string " "), 
			(2, ppTerm context ([index, propertyIndex], Top) term)]))

 op  ppOpDecl: [a] PrContext -> Bool -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDecl context blankLine? info_res =
   ppOpDeclAux context (true, false, false, 0) blankLine? info_res

 op  ppOpDef: [a] PrContext -> Nat -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDef context refine_num info_res =
   ppOpDeclAux context (false, true, false, refine_num) true info_res

 op  ppOpDeclThenDef: [a] PrContext -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDeclThenDef context info_res =
   ppOpDeclAux context (true, true, false, 0) true info_res

 op  ppOpDeclWithDef: [a] PrContext -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDeclWithDef context info_res =
   ppOpDeclAux context (true, false, true, 0) true info_res

 op  ppOpDeclAux: [a] PrContext -> Bool * Bool * Bool * Nat -> Bool -> (AOpInfo a * IndexLines)
                     -> IndexLines
 %% If printDef? is false print "op ..." else print "def ..."
 def ppOpDeclAux context (printOp?, printDef?, printOpWithDef?, refine_num) blankLine? (info, (index, lines)) =
   let pp : ATermPrinter = context.pp in
   let 
     def ppOpName (qid as Qualified (q, id)) =
       if q = UnQualified then
	 pp.ppOp id
       else
	 pp.ppOpId qid

     def ppOpNames () =
       case info.names of
	 | [name] -> ppOpName name
	 | _      -> ppList ppOpName ("{", ", ", "}") info.names
   in
   let index1 = -(index + 1) in
   let defined? = definedOpInfo? info in
   let button1 = (if markSubterm? context && ~ defined? then
		    PrettyPrint.buttonPretty (~(IntSet.member (context.indicesToDisable, index1)), 
					      index1, string " ", false)
		  else 
		    string "")
   in
   let button2 = (if markSubterm? context && ~ defined? then
		    PrettyPrint.buttonPretty (IntSet.member (context.sosIndicesToEnable, index1), 
					      index1, string " ", true)
		  else 
		    string "")
   in
   let (tvs, ty, dfn) = unpackNthTerm(info.dfn, refine_num) in
   % let _ = if show(head info.names) = "i"
   % then writeLine("def "^show(head info.names)^": "^show refine_num^" "^printType ty^"\n"^printTerm dfn^"\n"
   %                      ^printTerm info.dfn) else () in
   let 
     def ppDeclWithArgs (tvs, srt, tm) =
       case (tm, srt) of
         | (Lambda ([(pat,cond,body)],_), Arrow (dom,rng, apos)) ->
           [(4, blockNone (0, [(0, string " ("), 
                               (0, ppPattern (context << {printType = true})
                                     ([index, opIndex], false, false)
                                     pat  (* (TypedPat (pat, dom, apos)) *) ),
                               (0, string ")")]))]
           ++
           ppDeclWithArgs (tvs, rng, body)
         | _ ->
           (case info.fixity of
              | Nonfix           -> []
              | Constructor0     -> []
              | Constructor1     -> []
              | Unspecified      -> []
              | Infix (Left, i)  -> [(4, string (" infixl "^Nat.show i))]
              | Infix (Right, i) -> [(4, string (" infixr "^Nat.show i))])
           ++
           [(4, blockNone (0, [(0, string ": "), 
                               (4, ppType context ([index, opIndex], Top) srt)]))]
           ++
           ppDefAux (context, [index, defIndex], None, tm)

     def ppDecl (tvs, srt, tm) =
       (0, blockFill
             (0, 
              [(0, blockFill
                    (0, [(0, pp.Op)] ++ 
                       (if tvs ~= []
                          then [(0, ppForallTyVars pp tvs), (0, string " ")]
                        else []) ++
                       [(0, ppOpNames ())]))]
                ++
                (if printOpWithDef? || embed? Lambda tm && anyTerm? tm then
                   case (tm, srt) of
                     | (Lambda _, Arrow _) ->
                       ppDeclWithArgs ([], srt, tm)
                     | _ ->
                       [(0, case info.fixity of
                              | Nonfix         -> string ""
                              | Constructor0   -> string ""
                              | Constructor1   -> string ""
                              | Unspecified    -> string ""
                              | Infix (Left, i)  -> string (" infixl "^Nat.show i)
                              | Infix (Right, i) -> string (" infixr "^Nat.show i))]
                       ++
                       ppDefAux (context, [index, defIndex], Some srt, tm)
                 else
                   [(0, case info.fixity of
                                    | Nonfix         -> string ""
                                    | Constructor0   -> string ""
                                    | Constructor1   -> string ""
                                    | Unspecified    -> string ""
                                    | Infix (Left, i)  -> string (" infixl "^Nat.show i)
                                    | Infix (Right, i) -> string (" infixr "^Nat.show i)),
                    (4, prConcat [string ": ",
                                  ppType context ([index, opIndex], Top) srt])])))

     %def ppDeclWithDef(context, path, term, ty) =

     def ppDefAux (context, path, opt_ty, term) = 
       case term of
 	 | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
           let (opt_dom, opt_rng) = case opt_ty of
                                      | Some(Arrow(dom, rng, _)) -> (Some dom, Some rng)
                                      | _ -> (None, None)
           in
           let pat = maybeIncludeType(pat, opt_dom) in
 	   let pat  = let context = context << {printType = true} in
                      ppPattern context ([0, 0] ++ path, true, false) pat
           in
 	   let body = ppDefAux (context, [2, 0] ++ path, opt_rng, body) in
 	   let prettys = [(4, blockNone (0, [(0, pat)]))] ++ body in
 	   if markSubterm? context then
 	     let num = State.! context.markNumber in
 	     let table = State.! context.markTable in
 	     (context.markTable State.:= NatMap.insert (table, num, path);
 	      context.markNumber State.:= num + 1;
 	      PrettyPrint.markLines (num, prettys))
 	   else 
 	     prettys
         | Any _ ->
           (case opt_ty of
              | None -> []
              | Some ty -> [(4, blockNone (0, [(0, string ": "),
                                               (4, ppType context
                                                     ([index, opIndex], Top) ty)]))])
	 | _ ->
           (case opt_ty of
              | None -> []
              | Some ty -> [(4, blockNone (0, [(0, string ": "),
                                               (4, ppType context
                                                     ([index, opIndex], Top) ty)]))])
           ++ 
           [(1, blockNone (1, [(0, string " "),
                               (0, pp.DefEquals), 
                               (0, string " "), 
                               (2, ppTerm context (path, Top) term)]))]
	     
     def ppDef (tvs, ty, tm) =
       % let (tvs, opt_srt, tm) = unpackTerm(tm0) in
       % let _ = writeLine("ppDef:\n"^printTerm tm^":: "^printType ty) in
       let prettys = ppDefAux (context, [index, defIndex], Some ty, tm)
       in
       (0, blockLinear (0, 
		      [(0, blockFill (0, 
				      [(0, button1), 
				       (0, button2)]
                                      ++ (if refine_num > 0 then [(0, pp.Refine)] else [])
                                      ++ [(0, pp.Def)]
                                      ++ (if tvs ~= []
                                            then [(0, ppForallTyVars pp tvs),
                                                  (0, string " ")]
                                          else [])
                                      ++ [(0, ppOpName (primaryOpName info)), (0, string " ")]
				     ))]
                      ++ prettys))
   in
   % let (decls, defs) = opInfoDeclsAndDefs info in
   % let _ = writeLine("ppDef: "^show(head info.names)^" "^show refine_num^" of "^show(length defs)^"\n"^printTerm info.dfn) in
   let the_def = if true || printDef? || printOpWithDef?
                  then dfn
                  else Any(termAnn(dfn))
   in
   let ppDecls = if printOp? then [ppDecl (tvs, ty, the_def)] else [] in
   % let _ = writeLine("ppOpDeclAux: "^printAliases info.names^": "^show (length defs)^" - "^show refine_num) in
   let ppDefs  = if printDef? then [ppDef (tvs, ty, the_def)] else [] in
   (index + 1, ppDecls ++ ppDefs ++ lines)

 op [a] maybeIncludeType(pat: APattern a, opt_ty: Option(AType a)): APattern a =
   case pat of
     | RestrictedPat _ -> pat
     | _ ->
   case opt_ty of
     | Some(Subtype(_, pred, a)) ->
       RestrictedPat(pat, pred, a)
     | _ -> pat

 op  ppTypeDeclType: [a] PrContext -> (ATypeInfo a * IndexLines) -> IndexLines
 def ppTypeDeclType context info_res =
   ppTypeDecl context false true info_res

 op  ppTypeDeclDef: [a] PrContext -> (ATypeInfo a * IndexLines) -> IndexLines
 def ppTypeDeclDef context info_res =
   ppTypeDecl context true true info_res

 op  ppTypeDecl: [a] PrContext -> Bool -> Bool -> (ATypeInfo a * IndexLines) -> IndexLines
 %% If printDef? is false print "op ..." else print "def ..."
 def ppTypeDecl context printDef? newline? (info, (index, lines)) =
   let pp : ATermPrinter = context.pp in
   let 
     def ppTypeName (qid as Qualified (q, id)) =
       if q = UnQualified then
	 pp.ppType id
       else
	 pp.ppTypeId qid

     def ppTypeNames () =
       case info.names of
	 | [name] -> ppTypeName name
	 | _      -> ppList ppTypeName ("{", ", ", "}") info.names

     def ppLHS tvs =
       [(0, pp.Type), 
	(0, string " "), 
	(0, ppTypeNames()), 
	(0, ppTyVars pp tvs)]
       
     def ppDecl srt =
       let (tvs, srt) = unpackType srt in
       (0, blockFill (0, 
		      (ppLHS tvs))) 
       
     def ppDef srt =
       let (tvs, srt) = unpackType srt in
       (0, blockFill (0, 
		      (ppLHS tvs) 
		      ++
		      [(0, string " "), 
		       (0, pp.DefEquals)]
                      ++
		      (if embed? CoProduct srt then [] else  [(0, string " ")])
		      ++ [(2, ppType context ([index, typeIndex], Top) srt)]))
   in
   let (decls, defs) = typeInfoDeclsAndDefs info in
   let warnings = 
       (let m = length decls in
	let n = length defs  in
	if m <= 1 then
	  if n <= 1 then
	    []
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryTypeName info)) ^ " has " ^ (show n) ^ " definitions. *)"))]
	else
	  if n <= 1 then
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryTypeName info)) ^ " has " ^ (show m) ^ " declarations. *)"))]
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryTypeName info)) ^ " has " ^ (show m) ^ " declarations and " ^ (show n) ^ " definitions. *)"))])
   in
   let ppDecls = if printDef? then [] else map ppDecl decls in
   let ppDefs  = if printDef? then map ppDef defs else []  in
   (index + 1, (if newline? then [(0, string " ")] else []) ++ warnings ++ ppDecls ++ ppDefs ++ lines)

   % op isBuiltIn? : Import -> Bool
   % def isBuiltIn? (specCalcTerm, _ (* spc *)) = false
   % spec_ref = "String"  or spec_ref = "Nat"  or 
   % spec_ref = "Bool"    or spec_ref = "Char" or
   % spec_ref = "Integer" or spec_ref = "List" or 
   % spec_ref = "General"


 type ImportDirections = | NotSpec (List Spec)
                         | Verbose
                         | Recursive (List Spec)	% Make smarter to avoid repetitions?

 %% Top-level print module; lower-level print spec
 def ppSpec context spc = 
   let pp  = context.pp in
   blockAll (0, 
	     [(0, blockFill (0, 
			     [(0, pp.Spec), 
			      (0, string " ")]))]
	     ++
	     (ppSpecElements context spc (NotSpec [getBaseSpec()]) spc.elements)
	     ++
	     [(0, pp.EndSpec), 
	      (0, string "")])

 %% shw: Don't see how this is different from above
 def ppSpecR context spc = ppSpec context spc

 def ppSpecHidingImportedStuff context base_spec spc =
   %% Also suppress printing import of base specs
   let pp  = context.pp in
   blockAll (0, 
	     [(0, blockFill (0, 
			     [(0, pp.Spec), 
			      (0, string " ")]))]
	     ++
	     (ppSpecElements context spc (NotSpec [getBaseSpec()]) spc.elements)
	     ++
	     [(0, pp.EndSpec), 
	      (0, string "")])

 def ppSpecAll context spc =
   let pp  = context.pp in
   blockAll (0, 
	     [(0, blockFill (0, 
			     [(0, pp.Spec), 
			      (0, string " ")]))]
	     ++
	     (ppSpecElements context spc Verbose spc.elements)
	     ++
	     [(0, pp.EndSpec), 
	      (0, string "")])

 def ppSpecFlat context spc =
   let pp  = context.pp in
   blockAll (0, 
	     [(0, blockFill (0, 
			     [(0, pp.Spec), 
			      (0, string " ")]))]
	     ++
	     (ppSpecElements context spc (Recursive [getBaseSpec()]) spc.elements)
	     ++
	     [(0, pp.EndSpec), 
	      (0, string "")])


 op  ppSpecElements: [a] PrContext -> ASpec a -> ImportDirections -> ASpecElements a -> Lines
 def ppSpecElements context spc import_directions elements =
   (ppASpecElementsAux context spc import_directions elements (0,[])).2
 
 op  ppASpecElementsAux: [a] PrContext -> ASpec a -> ImportDirections -> ASpecElements a -> IndexLines
                           -> IndexLines
 op  ppSpecElementsAux: [a]      PrContext -> ASpec a -> ImportDirections -> SpecElements -> IndexLines
                           -> IndexLines
 def ppASpecElementsAux context spc import_directions elements result =
   let
     def ppSpecElement(el,afterOp?,result as (index,ppResult)) =
       case el of
	 | Import (im_sp_tm,im_sp,im_elements,_) ->
	   (case import_directions of
	     | NotSpec ign_specs ->
	       if im_sp in? ign_specs then result
	       else (index,
		     Cons((0, blockFill (0,
					 [(0, context.pp.Import), 
					  (2, ppImportTerm context import_directions im_sp_tm)])),
			  ppResult))
	     | Verbose ->
	       (index,
		Cons((0, blockFill (0, 
				    [(0, context.pp.Import),
				     (2, ppImportTerm context import_directions im_sp_tm),
				     (2, string " |-> "), 
				     (2, ppSpecAll context im_sp)])),
		     ppResult))
	     | Recursive ign_specs ->
               if im_sp in? ign_specs then result
	       else 
	       %% for now, showx is broken, but simply changing spc to im_sp is not the fix...
	       %% use sp, not im_sp, to get correct context for show
               let (index, ppResult) = ppSpecElementsAux context spc import_directions im_elements result in
               (index, [(0, blockFill (0,
                               [(0, context.pp.Import), 
                                (2, ppImportTerm context import_directions im_sp_tm)]))]
                  ++ ppResult))
	       
	 | Op (qid,def?,_) ->
           % let _ = writeLine("printing op "^show qid^" "^show def?) in
	   (case findTheOp(spc,qid) of
	      | Some opinfo ->
                if def? then
                  ppOpDeclWithDef context (opinfo,result) % TODO: discriminate decl-with-def from decl-then-def
                else
                  ppOpDecl context (~afterOp?) (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[1]: " ^ printQualifiedId qid ^ "\n") in
		(4, (0, string("op "^show qid)) :: ppResult))
	 | OpDef (qid,refine_num,_,_) ->
           % let _ = writeLine("printing def "^show qid^" "^show refine_num) in
	   (case findTheOp(spc,qid) of
	      | Some opinfo -> ppOpDef context refine_num (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[2]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | Type (qid,_) ->
	   (case findTheType(spc,qid) of
	      | Some typeinfo -> ppTypeDeclType context (typeinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type[1]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | TypeDef (qid,_) ->
	   (case findTheType(spc,qid) of
	      | Some typeinfo -> ppTypeDeclDef context (typeinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type[2]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | Property prop ->
	   (index+1,
	    (0, string " ") :: Cons(ppProperty context (index, prop),ppResult))
	 | Comment (str,_) ->
	   (index+1,
	    if exists? (fn char -> char = #\n) str then
	      [(0, string " (* "),
	       (2, string str),
	       (0, string " *) ")]
	      ++
	      ppResult
	    else
	      Cons ((0, string (" %% " ^ str)),
		    ppResult))
	 | Pragma (prefix, body, postfix, pos) ->
	   if printPragmas?
             then (index+1,
                   (0, string " ") :: Cons ((0, string (prefix ^ body ^ postfix)),
                                            ppResult))
             else result

     def aux(elements,afterOp?,result) =
         case elements of
	   | [] -> result
	   | (Op (qid1,def?,a)) :: (r1_els as (OpDef (qid2,0,_,_)) :: r2_els) ->
	     (case findTheOp(spc,qid1) of
	      | Some opinfo ->
		if qid1 = qid2 then
                  ppOpDeclThenDef context (opinfo,aux(r2_els, false, result))
		else if def? then
                  ppOpDeclWithDef context (opinfo,aux(r1_els, false, result)) % TODO: discriminate decl-with-def from decl-then-def
                else
                  ppOpDecl context afterOp? (opinfo,aux(r1_els, true, result))
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[3]: " ^ printQualifiedId qid1 ^ "\n") in
		result)
	   | el :: r_els -> ppSpecElement(el,afterOp?,aux(r_els,(embed? Op) el,result))
   in
     aux(elements,true,result)
       
 op  ppImportTerm : PrContext -> ImportDirections -> SCTerm -> Pretty

 %% ppImportTerm wants to dispatch on the structure of the SCTerm, but that isn't defined here,
 %% so ppImportTerm is defined over in /Languages/SpecCalculus/Semantics/Evaluate/Print.sw,
 %% where SCTerm has been defined.
 %% 
 %%  def AnnSpecPrinter.ppImportTerm context import_directions im_sp_tm =
 %%    case im_sp_tm of
 %%      | (Quote (Spec spc, _, _), _) ->
 %%         AnnSpecPrinter.ppImportedSpec context spc import_directions 
 %%      | _ ->
 %%        string (indentString "  " (showTerm im_sp_tm))
 %% 
 %% Note that ppImportTerm may call right back to ppImportedSpec, defined here:

 op  ppImportedSpec : [a] PrContext -> ASpec a -> ImportDirections -> Pretty
 def ppImportedSpec context spc import_directions =
   let pp  = context.pp in
   blockLinear (0,
		[(0, pp.Spec)] ++
		(ppSpecElements context spc import_directions spc.elements) ++
		[(0, pp.EndSpec)])

 %% Identical tedt copy to body of ppASpecElementsAux, but different types
 def ppSpecElementsAux context spc import_directions elements result =
   let
     def ppSpecElement(el,afterOp?,result as (index,ppResult)) =
       case el of
	 | Import (im_sp_tm,im_sp,im_elements,_) ->
	   (case import_directions of
	     | NotSpec ign_specs ->
	       if im_sp in? ign_specs then result
	       else (index,
		     Cons((0, prettysFill [context.pp.Import, 
					   %% TODO: indenting this way isn't quite right,
					   %% since it will indent inside string literals
					   %% But pretty printers make it inordinately 
					   %% difficult to do simple things like indentation.
					   string (indentString "  " (showSCTerm im_sp_tm))]),
			  ppResult))
	     | Verbose ->
	       (index,
		Cons((2, blockFill (0, 
				    [(0, string "import "), 
				     (0, string (showSCTerm im_sp_tm)), 
				     (0, string " |-> "), 
				     (0, ppSpecAll context im_sp)])),
		     ppResult))
	     | Recursive  ign_specs ->
	       if im_sp in? ign_specs then result
	       else
	       %% for now, showx is broken, but simply changing spc to im_sp is not the fix...
	       %% use sp, not im_sp, to get correct context for show
	       aux(im_elements, false, result))
	       
	 | Op (qid,def?,_) ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo ->
                if def? then
                  ppOpDeclThenDef context (opinfo,result) % TODO: discriminate decl-with-def from decl-then-def
                else
                  ppOpDecl context (~afterOp?) (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[4]: " ^ printQualifiedId qid ^ "\n") in
		(4, (0, string("op "^show qid)) :: ppResult))
	 | OpDef (qid, refine_num, _, _) ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo -> ppOpDef context refine_num (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[5]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | Type (qid,_) ->
	   (case findTheType(spc,qid) of
	      | Some typeinfo -> ppTypeDeclType context (typeinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type[3]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | TypeDef (qid,_) ->
	   (case findTheType(spc,qid) of
	      | Some typeinfo -> ppTypeDeclDef context (typeinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type[4]: " ^ printQualifiedId qid ^ "\n") in
		result)
	 | Property prop ->
	   (index+1,
	    Cons(ppProperty context (index, prop),ppResult))
	 | Comment (str,_) ->
	   (index+1,
	    if exists? (fn char -> char = #\n) str then
	      [(0, string " (* "),
	       (2, string str),
	       (0, string " *) ")]
	      ++
	      ppResult
	    else
	      Cons ((0, string (" %% " ^ str)),
		    ppResult))
	 | Pragma (prefix, body, postfix, pos) \_rightarrow
           if printPragmas?
             then (index+1,
                   Cons ((0, string (prefix ^ body ^ postfix)),
                         ppResult))
             else result

     def aux(elements,afterOp?,result) =
         case elements of
	   | [] -> result
	   | (Op (qid1,def?,a)) :: (OpDef (qid2,0,hist,_)) :: r_els ->
	     (case findTheOp(spc,qid1) of
	      | Some opinfo ->
		if qid1 = qid2 then
                  ppOpDeclThenDef context (opinfo,aux(r_els, false, result))
		else if def? then
                  ppOpDeclWithDef context (opinfo,aux(r_els, false, result)) % TODO: discriminate decl-with-def from decl-then-def
                else
                  ppOpDecl context afterOp? (opinfo,aux(Cons(OpDef (qid2,0,hist,a),r_els), true, result))
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op[6]: " ^ printQualifiedId qid1 ^ "\n") in
		result)
	   | el :: r_els -> ppSpecElement(el,afterOp?,aux(r_els,(embed? Op) el,result))
   in
     aux(elements,true,result)

  op indentString : String -> String -> String
 def indentString prefix s =
   let newline_char = head (explode newline) in
   let prefix = explode prefix in
   let s = foldl (fn (s, char) ->
		  if char = newline_char then
		    prefix ++ (Cons (char, s))
		  else
		    Cons (char, s))
                 []  
		 (explode s)
   in
     implode (reverse s)

 def specToPrettyVerbose spc = 
   ppSpecAll (initialize (asciiPrinter, false)) spc

 def specToPrettyVerboseXSymbol spc = 
   ppSpecAll (initialize (XSymbolPrinter, false)) spc

 def specToPrettyFlat spc = 
   ppSpecFlat (initialize (asciiPrinter, false)) spc
   
 def specToPretty spc = 
   let base_spec = getBaseSpec () in
   ppSpecHidingImportedStuff (initialize (asciiPrinter, false)) emptySpec spc
   
 def specToPrettyXSymbol spc = 
   let base_spec = getBaseSpec () in
   ppSpecHidingImportedStuff (initialize (XSymbolPrinter, false)) emptySpec spc
   
 def specToPrettyR spc = 
   ppSpecR (initialize (asciiPrinter, false)) spc
   
 def printSpec spc =
   PrettyPrint.toString (format (printWidth, specToPretty spc))

 def printSpecXSymbol spc =
   PrettyPrint.toString (format (printWidth, specToPrettyXSymbol spc))
   
 def printSpecVerbose spc =
   PrettyPrint.toString (format (printWidth, specToPrettyVerbose spc))

 def printSpecVerboseXSymbol spc =
   PrettyPrint.toString (format (printWidth, specToPrettyVerboseXSymbol spc))

 def printSpecFlat spc =
   PrettyPrint.toString (format (printWidth, specToPrettyFlat spc))

 op printSpecExpanded: Spec -> Spec -> String

 def printSpecFlatToTerminal spc =
   (toTerminal (format (printWidth, specToPrettyFlat spc)); 
    writeLine "")
   
 def printSpecToTerminal spc =
   (toTerminal (format (printWidth, specToPretty spc)); 
    writeLine "")
   
 def printSpecToFile (fileName, spc) = 
   toFile (fileName, format (printWidth, specToPretty spc))

 def printFlatSpecToFile (fileName, spc) = 
   toFile (fileName, format (printWidth, specToPrettyFlat spc))
   
 def printMarkedSpecToFile (fileName, pathFileName, indicesToDisable, sosIndicesToEnable, spc) = 
   let context = initializeMark (asciiPrinter, indicesToDisable, sosIndicesToEnable) in
   let specToPretty = ppSpec context in
   (PrettyPrint.toPathFiles (fileName, pathFileName, format (printWidth, specToPretty spc));
    State.! context.markTable)

 def printMarkedSpecToString (indicesToDisable, sosIndicesToEnable, spc) = 
   let context = initializeMark (asciiPrinter, indicesToDisable, sosIndicesToEnable) in
   let specToPretty = ppSpec context in
   let spcAndMarking = PrettyPrint.toStringWithPathIndexing (format (printWidth, specToPretty spc)) in
   (spcAndMarking, State.! context.markTable)

 def printSpecWithTypesToTerminal spc =
   toTerminal (format (printWidth, ppSpec (initialize (asciiPrinter, true)) spc))
   
 def latexSpecToPretty spc = 
   let pSpec = ppSpec (initialize (latexPrinter, false)) spc in
   makeSpecListing pSpec
   
 def makeSpecListing pSpec = 
   blockAll (0, 
	    [(0, string "\\specListing{"), 
	     (0, pSpec), 
	     (0, string "}")]) 
   
 def latexSpec spc = 
   PrettyPrint.toLatexString (format (printWidth, latexSpecToPretty spc))
   
 def latexSpecToFile (fileName, spc) = 
   PrettyPrint.toLatexFile (fileName, format (printWidth, latexSpecToPretty spc))
   
 def htmlSpecToPretty spc = 
   let pSpec = ppSpec (initialize (htmlPrinter (), false)) spc in
   prettysAll
   [string "<html><body BGCOLOR = \"#EEFFFA\"><pre>", 
    pSpec, 
    string "</pre></body></html>"]      

 def htmlSpecToFile (fileName, spc) = 
   PrettyPrint.toFile (fileName, format (printWidth, htmlSpecToPretty spc))
   
 def boolToNat b = if b then 1 else 0
 def positive? n = if n > 0 then 1 else 0
   
 def pdfMenu spc = 
   let types = 
       foldriAQualifierMap 
        (fn (q, id, _, types) -> 
	 Cons (prettysNone [string ("  \\pdfoutline goto name {"^"???"^":Type:"
				   ^ (if q = UnQualified then "" else q^".")^id^"} {"), 
			   string (if q = UnQualified then "" else q^"."), 
			   string id, 
			   string "}"], 
	      types))
	[] 
	spc.types        
   in
   let ops = 
       foldriAQualifierMap 
        (fn (q, id, _, ops) -> 
	 Cons (prettysNone [string ("  \\pdfoutline goto name {"^"???"^":Op:"
				   ^ (if q = UnQualified then "" else q^".")^id^"} {"), 
			   string (if q = UnQualified then "" else q^"."), 
			   string id, 
			   string "}"], 
	      ops))
	[] 
	spc.ops
   in
   let (counter, properties) = 
       foldl (fn (result as (counter, list), el) ->
	      case el of
		| Property(pt, qid, tvs, _, _) ->
	          (counter + 1, 
		   Cons (string ("  \\pdfoutline goto num "^ Nat.show counter^
				 "  {"^ printQualifiedId qid ^ "}"), 
			 list))
		| _ -> result)
             (1, []) 
	     spc.elements
   in
   let properties = reverse properties    in
   let typeCount  = length types      in
   let opCount    = length ops        in
   let pCount     = length properties in

   let menuCount = positive? typeCount + 
                   positive? opCount +
		   positive? pCount        
   in
     prettysAll ([string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
			 Nat.show menuCount^"  {"^"???"^"}")]
		++
		(if typeCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^
			    "} count -"^Nat.show typeCount^
			    " {Types}")]
		 else 
		   [])
		++
		types
		++
		(if opCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
			    Nat.show opCount^
			    " {Ops}")]
		 else 
		   [])
		++
		ops
		++
		(if pCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^"} count-"^
			    Nat.show pCount^" {Properties}")]
		 else
		   [])
		++
		properties)          

 def [a] pdfSpecsToPretty specs0 = 
   let counter = (Ref 0) : Ref Nat in
   let specs = 
        map (fn (sp : ASpec a) -> 
	     ppSpec (initialize (pdfPrinter (counter, "???"), false)) sp) 
	    specs0 
   in
   let menues = map pdfMenu specs0                  in
   let sw2000 = case getEnv "SPECWARE2000" of
		  | None            -> "??SPECWARE2000??" 
		  | Some dir_string -> dir_string
   in
   prettysAll ([string "\\documentclass{article}", 
		string ("\\input{" ^ sw2000 ^ "/doc/pdf-sources/megamacros}"), 
		% string "\\input{/specware/doc/macros/macros}", 
		string "\\begin{document}", 
		string "\\pdfthread num 1"]
	       ++
	       (map (fn s -> 
		     string (PrettyPrint.toLatexString (format (printWidth, makeSpecListing s)))) 
		    specs)
	       ++
	       [string "\\pdfendthread"]
	       ++
	       menues
	       ++
	       [string "\\pdfcatalog{ /PageMode /UseOutlines }", 
		string "\\end{document}"])        
                        
 def [a] pdfSpecsToFile (fileName, spcs : List (ASpec a)) = 
   PrettyPrint.toFile (fileName, format (printWidth, pdfSpecsToPretty spcs))

 % Separate output in three portions:
 % 1. pretty print the prelude erasing older versions
 % 2. pretty print append each spec with LaTeX line breaks.
 % 3. pretty print append the postlude.

 def pdfPreludeToFile fileName =
   let sw2000 = case getEnv "SPECWARE2000" of
		  | None            -> "??SPECWARE2000??" 
		  | Some dir_string -> dir_string
   in
   PrettyPrint.toFile 
     (fileName, 
      format (printWidth, 
	      prettysAll
	      ([string "\\documentclass{article}", 
		string ("\\input{" ^ sw2000 ^ "/doc/pdf-sources/megamacros}"), 
		string "\\begin{document}", 
		string "\\pdfthread num 1"])))

 def [a] pdfOneSpecToFile (counter, fileName, spc : ASpec a) = 
   let spc1 = ppSpec (initialize (pdfPrinter (counter, "???"), false)) spc         in
   let menu = pdfMenu spc                                                         in
   (PrettyPrint.appendFile(fileName, 
			   format (100, string "\\newpage"));
    PrettyPrint.appendLatexFile (fileName, PrettyPrint.format (printWidth, makeSpecListing spc1));
    menu)

 def pdfPostLudeToFile (fileName, menues) = 
   PrettyPrint.appendFile (fileName, 
     PrettyPrint.format (100, 
       prettysAll
       ([string "\\pdfendthread"]
         ++ menues
         ++ [string "\\pdfcatalog{ /PageMode /UseOutlines }", 
             string "\\end{document}"])))

 op [a] TransformExpr.show (tre: ATransformExpr a): String = 
   PrettyPrint.toString (format (printWidth, ppTransformExpr asciiPrinter tre))

 op [a] ppTransformExprs (pp: ATermPrinter) (tres: List(ATransformExpr a)): Pretty =
  ppList (ppTransformExpr pp) ("{", ", ", "}") tres

 op [a] ppTransformExpr (pp: ATermPrinter) (tre: ATransformExpr a): Pretty =
   case tre of
    | Name(id, _) -> pp.ppOp id
    | Number(i, _) -> pp.fromString (show i)
    | Str(str, _) -> pp.fromString ("\""^str^"\"")
    | Qual(q, id, _) -> pp.ppOpId(Qualified(q, id))
    | SCTerm(sct, _) -> string (showSCTerm sct)
    | QuotedTerm(tm, _) -> prettysNone[string "`", string(printTerm tm), string "`"]
    | Item(nm, tre1, _) -> prettysNone[pp.ppOp nm, string " ", ppTransformExpr pp tre1]
    | Repeat(cnt, r_tre, _) -> prettysNone[string "repeat", ppTransformExpr pp r_tre]
    | Tuple(tres, _) -> ppList (ppTransformExpr pp) ("(", ", ", ")") tres
    % | Record(prs, _) -> ppList (ppTransformExpr pp) ("{", ", ", "}") tres
    | Options(tres, _) -> ppList (ppTransformExpr pp) ("[", ", ", "]") tres
    % | At(qids, tres, _) -> 
    | Command(tre1, tres, _) -> prettysNone[string tre1, string " ",
                                            ppList (ppTransformExpr pp) ("", " ", "") tres]
    | _ -> pp.fromString (anyToString tre)

endspec
