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

AnnSpecPrinter qualifying spec 
 import ../AbstractSyntax/Printer
 import AnnSpec
 % import /Library/IO/Primitive/IO                    % for getEnv
 import /Library/Legacy/DataStructures/IntSetSplay  % for indicesToDisable
 import /Library/Legacy/DataStructures/NatMapSplay  % for markTable's

 op SpecCalc.getBaseSpec : () -> Spec % defined in /Languages/SpecCalculus/Semantics/Environment

 %% ========================================================================

 type Path = List Nat

 type ParentSort = | Top | ArrowLeft | ArrowRight | Product | CoProduct | Quotient | Subsort 

 type ParentTerm = | Top | Nonfix | Infix Associativity * Nat

 type PrContext = {
		 pp                 : ATermPrinter,
		 printSort          : Boolean,
		 markSubterm        : Boolean,
		 markNumber         : Ref Nat,
		 markTable          : Ref (NatMap.Map (List Nat)),
		 indicesToDisable   : IntegerSet.Set,
		 sosIndicesToEnable : IntegerSet.Set
                }
 
 type IndexLines = Integer * Lines

 %% ========================================================================

 op printTyVars                  : TyVars            -> String 
 op printSort                    : [a] ASort       a -> String 
 op printPattern                 : [a] APattern    a -> String
 op printSortScheme              : [a] ASortScheme a -> String 
 op printTermScheme              : [a] ATermScheme a -> String 
 op printTermWithSorts           : [a] ATerm       a -> String
 op printSpec                    : [a] ASpec       a -> String
 op latexSpec                    : [a] ASpec       a -> String

 op printSpecToFile              : [a] String * ASpec a -> ()
 op printFlatSpecToFile          : [a] String * ASpec a -> ()
 op latexSpecToFile              : [a] String * ASpec a -> ()
 op printSpecFlatToTerminal      : [a]          ASpec a -> ()
 op printSpecToTerminal          : [a]          ASpec a -> ()
 op printSpecWithSortsToTerminal : [a]          ASpec a -> ()

 op isShortTuple                 : [a] Nat * List (Id * a) -> Boolean
 op ppTerm                       : [a] PrContext -> Path * ParentTerm -> ATerm    a -> Pretty
 op ppSort                       : [a] PrContext -> Path * ParentSort -> ASort    a -> Pretty
 op ppPattern                    : [a] PrContext -> Path * Boolean    -> APattern a -> Pretty
 op termToPretty                 : [a] ATerm a -> Pretty
 op printTermToTerminal          : [a] ATerm a -> ()
%op printSort                    : [a] ASort a -> String
 op printSortToTerminal          : [a] ASort a -> ()
%op printSortScheme              : [a] ASortScheme a -> String
%op printPattern                 : [a] APattern a -> String
%op printTermWithSorts           : [a] ATerm a -> String
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
 op printMarkedSpecToFile        : [a] String * String * IntegerSet.Set * IntegerSet.Set * ASpec a ->          NatMap.Map (List Nat)
 op printMarkedSpecToString      : [a]                   IntegerSet.Set * IntegerSet.Set * ASpec a -> String * NatMap.Map (List Nat)
%op printSpecWithSortsToTerminal : [a] ASpec a -> ()
 op latexSpecToPretty            : [a] ASpec a -> Pretty
%op latexSpec                    : [a] ASpec a -> String
%op latexSpecToFile              : [a] String * ASpec a -> ()
 op htmlSpecToPretty             : [a] ASpec a -> Pretty
 op htmlSpecToFile               : [a] String * ASpec a -> ()

 %% ========================================================================

 def toString = PrettyPrint.toString

 def isShortTuple (i, row) = 
   case row of
     | []           -> true
     | (lbl, r) :: row -> lbl = Nat.toString i & isShortTuple (i + 1, row)
      

 def [a] isFiniteList (term : ATerm a) : Option (List (ATerm a)) =  
   case term of
     | Fun (Embed ("Nil", false), Base (Qualified("List", "List"), _, _), _) -> Some []
     | Apply (Fun (Embed("Cons", true), 
		   Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				   _),
			  Base (Qualified("List", "List"), _, _),
			  _),
		   _),
	      Record ([(_, t1), (_, t2)], _),
	      _)
       -> 
       (case isFiniteList t2 of
	  | Some terms -> Some (cons (t1, terms))
	  | _ ->  None)
     | ApplyN ([Fun (Embed ("Cons", true), 
		     Arrow (Product ([("1", _), ("2", Base (Qualified("List", "List"), _, _))], 
				     _),
			    Base (Qualified("List", "List"), _, _),
			    _),
		     _),
		Record ([(_, t1), (_, t2)], _),
		_],
	       _) 
       -> 
       (case isFiniteList t2 of
	  | Some terms -> Some (cons (t1, terms))
	  | _  ->  None)
     | _ -> None

 def initialize (pp, printSort?) : PrContext = 
   {pp                 = pp,
    printSort          = printSort?,
    markSubterm        = false,
    markNumber         = Ref 0,
    markTable          = Ref NatMap.empty,
    indicesToDisable   = IntegerSet.empty,
    sosIndicesToEnable = IntegerSet.empty}
 
 def initializeMark (pp, indicesToDisable, sosIndicesToEnable) : PrContext = 
   {pp                 = pp,
    printSort          = false,
    markSubterm        = true, 
    markNumber         = (Ref 0),
    markTable          = Ref NatMap.empty,
    indicesToDisable   = indicesToDisable,
    sosIndicesToEnable = sosIndicesToEnable}
 
 def printSort?   (c:PrContext) = c.printSort
 def markSubterm? (c:PrContext) = c.markSubterm
 
 def [a] termFixity (term : ATerm a) : Fixity = 
   case term of
     | Fun (termOp, srt, _) -> 
       (case termOp of
	  | Op (_, fixity) -> (case fixity of
				 | Unspecified -> Nonfix
				 | _ -> fixity)
	  | And            -> Infix (Right, 15) 
	  | Or             -> Infix (Right, 14) 
	  | Implies        -> Infix (Right, 13) 
	  | Iff            -> Infix (Right, 12) 
	  | Equals         -> Infix (Left, 20) % was 10 ??
	  | NotEquals      -> Infix (Left, 20)
	  | RecordMerge    -> Infix (Left, 25)
	  | _              -> Nonfix)
     | _ -> Nonfix
 

%def mkAEquals (srt,pos) = Fun (Equals, srt, pos)

 def [a] printOp (context, 
		  pp     : ATermPrinter, 
		  termOp : AFun  a, 
		  srt    : ASort a, 
		  a      : a) 
   : Pretty = 
   case termOp of
     | Op          (idInfo, _) -> pp.ppOpId (idInfo)
     | Bool        b           -> pp.fromString (Boolean.toString b)
     | Nat         n           -> pp.fromString (Nat.toString n)
     | String      s           -> pp.fromString ("\""^s^"\"")              % "abc"
     | Char        c           -> pp.fromString ("#" ^ (Char.toString c))  % #A
     | Embed       (s, _)      -> pp.fromString (s)  %"embed("^s^")"
     | Project     s           -> pp.fromString ("project "^s^" ")
     | RecordMerge             -> pp.fromString "<<"
     | Embedded    s           -> pp.fromString ("embed?("^s^")")
     | Quotient    qid         -> pp.fromString ("quotient[" ^ toString qid ^ "] ")
     | Choose      qid         -> pp.fromString ("choose["   ^ toString qid ^ "] ")
     | PQuotient   qid         -> pp.fromString ("quotient[" ^ toString qid ^ "] ")
     | PChoose     qid         -> pp.fromString ("choose["   ^ toString qid ^ "] ")
     | Not                     -> pp.Not
     | And                     -> pp.And
     | Or                      -> pp.Or
     | Implies                 -> pp.Implies
     | Iff                     -> pp.Iff
     | Equals                  -> pp.Equals
     | NotEquals               -> pp.NotEquals
     | OneName     (x, _)      -> pp.fromString x
     | TwoNames    (x, y, _)   -> pp.fromString (if x = UnQualified then y else x^"."^ y)
     
     | Relax                   -> let p = case srt of Arrow (Subsort (_, p, _), _, _) -> p | _ -> mkTrueA a in
                                  prettysFill [pp.fromString "relax", 
					       string "(",
					       ppTerm context ([], Top) p, 
					       string ")"]
     | Restrict                -> let p = case srt of Arrow (_, Subsort (_, p, _), _) -> p | _ -> mkTrueA a in
				  prettysFill [pp.fromString "restrict", 
					       string "(",
					       ppTerm context ([], Top) p,
					       string ")"]
     %% Only used internally at present
     | Select      s           -> pp.fromString ("select(" ^ s ^ ")")


 def [a] singletonPattern (pat : APattern a) = 
   case pat of
     | AliasPat      _ -> false
     | QuotientPat   _ -> false
     | RestrictedPat _ -> false
     | _               -> true


 def printLambda (context, path, marker, match) = 
   let pp : ATermPrinter = context.pp in
   let 
     def prRule marker (i, (pat, cond, trm)) = 
       case cond of
	 | Fun (Bool true, _, _) -> 
	   blockFill (0,
		      [(0, prettysNone [marker,
					ppPattern context ([0, i] ++ path, true) pat,
					pp.Arrow]),
		       (3, ppTerm context ([2, i] ++ path, Top) trm)])
	 | _ -> 
	   blockFill (0,
		      [(0, prettysNone [marker,
					ppPattern context ([0, i] ++ path, true) pat,
					string " ",
					pp.Where,
					string " ",
					ppTerm context ([1, i] ++ path, Top) cond,
					pp.Arrow]),
		       (3, ppTerm context ([3, i] ++ path, Top) trm)])
   in
     prettysAll (case match of
		   | [] -> []
		   | rule :: rules -> 
		     [prRule marker (0, rule)] ++
		     (ListUtilities.mapWithIndex (fn (i, rule) -> prRule pp.Bar (i + 1, rule)) 
		                                 rules))
 
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

 def [a] ppTerm1 context (path, parentTerm) (term: ATerm a) : Pretty =
   let pp : ATermPrinter = context.pp in
   let % Function application is printed taking special cases into account
     def prApply (t1, t2) = 
       case (t1, t2) of
	 | (Lambda (rules as (_ :: _), _), _) ->
	   % Print lambda abstraction as
	   % case pattern matching
           blockAll (0, 
		     [(0, prettysNone [pp.LP, pp.Case, ppTerm context ([1] ++ path, Top) t2]), 
		      (3, prettysNone 
		       [printLambda (context, [0] ++ path, pp.Of, rules), 
			pp.RP])])
	   % Print tuple projection using
	   % dot notation.
	 | (Fun (Project p, srt1, _), Var ((id, srt2), _)) ->
	   if printSort? context then
	     prettysNone [pp.fromString id, 
			  string ":", 
			  ppSort context ([0, 1] ++ path, Top) srt2, 
			  string ".", 
			  string p, 
			  string ":", 
			  ppSort context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [pp.fromString id, string ".", pp.fromString p]
	 | (Fun (Project p, srt1, _), tm as Fun _) ->
	   if printSort? context then
	     prettysNone [ppTerm context (path, parentTerm) tm,
			  string ":", 
			  ppSort context ([0, 1] ++ path, Top) (termSort tm),
			  string ".", 
			  string p, 
			  string ":", 
			  ppSort context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [ppTerm context (path, parentTerm) tm, string ".", pp.fromString p]
	 | (Fun (Project p, srt1, _), tm) ->
	   if printSort? context then
	     prettysNone [string "(",
			  ppTerm context (path, parentTerm) tm,
			  string ":", 
			  ppSort context ([0, 1] ++ path, Top) (termSort tm),
			  string ").",
			  string p, 
			  string ":", 
			  ppSort context ([0, 0] ++ path, Top) srt1]
	   else
	     prettysNone [string "(",
			  ppTerm context (path, parentTerm) tm, 
			  string ").", 
			  pp.fromString p]
	 | _ -> 
	   blockFill (0, 
		      [(0, ppTerm context ([0] ++ path, Nonfix) t1), 
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
					   [(0, string " "), 
					    (0, ppTerm context ([1] ++ path, Top) t2)
					    (*, (0, string " ")*)
					    ]
					 | _ -> 
					   [(0, pp.LP), 
					    (0, ppTerm context ([1] ++ path, Top) t2), 
					    (0, pp.RP)])))])
   in
   case isFiniteList term of
     | Some terms -> 
       AnnTermPrinter.ppListPath path
                                 (fn (path, term) -> ppTerm context (path, Top) term)
				 (pp.LBrack, pp.Comma, pp.RBrack)  terms
     | None -> 
       (case term of
	  | Fun (top, srt, a) -> 
	    if printSort? context then
	      blockFill (0, 
			 [(0, printOp (context, pp, top, srt, a)), 
			  (0, string " : "), 
			  (0, ppSort context ([0] ++ path, Top) srt)])
	    else 
	      printOp (context, pp, top, srt, a)
	  | Var ((id, srt), _) -> 
	    if printSort? context then
	      blockFill (0, 
			 [(0, pp.fromString id), 
			  (0, string " : "), 
			  (0, ppSort context ([0] ++ path, Top) srt)])
	    else 
	      pp.fromString id
	  | Let (decls, body, _) -> 
	    let 
              def ppD (index, separatorLength, separator, pat, trm) = 
		case (pat, trm) of
		  | (VarPat _, Lambda ([(pat2, Fun (Bool true, _, _), body)], _)) ->
		    (0, blockLinear (0, 
				     [(0, prettysNone [separator, 
						       ppPattern context ([0, index]++ path, false) pat, 
						       string " ", 
						       ppPattern context ([0, 1, index]++ path, false) pat2, 
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
						       ppPattern context ([0, index]++ path, true) pat, 
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
		  | (pat, trm) :: decls -> cons (ppD (index, l, separator, pat, trm), 
						 ppDs (index + 1, 5, pp.LetDeclsAnd, decls))
	    in
	      enclose(case parentTerm of
			| Infix _ -> false   % Add parens if inside infix expression
			| _ -> true,
		      blockAll (0, 
				[(0, blockLinear (0, 
						  [(0, blockLinear (0, ppDs (0, 4, pp.Let, decls))), 
						   (0, pp.In)])), 
				 (0, ppTerm context ([length decls] ++ path, parentTerm) body)]))
	  | LetRec (decls, body, _) -> 
            let
              def ppD (path, ((id, _), trm)) =
                (case trm of
		   | Lambda ([(pat, Fun (Bool true, _, _), body)], _) -> 
		     blockLinear (0, 
				  [(0, prettysNone [pp.Def, 
						    pp.fromString id, 
						    string " ", 
						    ppPattern context ([1, 0] ++ path, false) pat, 
						    string " ", 
						    pp.Equals, 
						    string " "]), 
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
			| Infix _ -> false % Add parens if inside an infix expr
			| _ -> true,
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
			| Infix _ -> false % Add parens if inside an infix expr
			| _ -> true,
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
	    prettysNone [pp.LP, 
			 printLambda (context, path, pp.Lambda, match), 
			 pp.RP]
          | The ((id,srt),body,_) ->
	    enclose(case parentTerm of
		      | Top -> true
		      | _ -> false,
		    blockFill (0, [
			  (0, prettysNone 
			   [pp.The,
			    pp.LP,
			    pp.fromString id, 
			    string " : ", 
			    ppSort context ([2] ++ path, Top) srt,
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
			  string " : ", 
			  ppSort context ([index]++ path, Top) srt])
	    in
	      enclose(case parentTerm of
			| Infix _ -> false % Add parens if inside an infix expr
			| _ -> true,
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
            let
	      def prInfix (f1, f2, l, t1, oper, t2, r) =
		prettysFill [prettysNone [l, 
					  ppTerm context ([0, 1]++ path, f1) t1, 
					  string " "], 
			     prettysNone [ppTerm context ([0]++ path, Top) oper, 
					  string " ", 
					  ppTerm context ([1, 1]++ path, f2) t2, 
					  r]]
	    in
	      %
	      % Infix printing is to be completed.
	      %
              (case (parentTerm, termFixity (trm1)) of
                 | (_, Nonfix) -> prApply (trm1, trm2)
                 | (Nonfix, Infix (a, p)) ->
                    prInfix (Infix (Left, p), Infix (Right, p), pp.LP, t1, trm1, t2, pp.RP)
                 | (Top, Infix (a, p))  ->
                    prInfix (Infix (Left, p), Infix (Right, p), pp.Empty, t1, trm1, t2, pp.Empty) 
                 | (Infix (a1, p1), Infix (a2, p2)) ->
		   if p1 = p2 then
		     (if a1 = a2 then
			prInfix (Infix (Left, p2), Infix (Right, p2), pp.Empty, t1, trm1, t2, pp.Empty)
		      else
			prInfix (Infix (Left, p2), Infix (Right, p2), pp.LP, t1, trm1, t2, pp.RP))
		   else if p2 > p1 then
		     %% Inner has higher precedence
		     prInfix (Infix (Left, p2), Infix (Right, p2), pp.Empty, t1, trm1, t2, pp.Empty)
		   else 
		     prInfix (Infix (Left, p2), Infix (Right, p2), pp.LP, t1, trm1, t2, pp.RP))
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
	  | SortedTerm (t, s, _) -> 
	    (case s of
	      | MetaTyVar _ ->  
	        ppTerm context ([0] ++ path, Top) t
	      | _ ->
	        prettysNone [ppTerm context ([0]++ path, Top) t, 
			     string ":", string " ", 
			     ppSort context ([1]++ path, Top) s])
	  | Pi (tvs, tm, _) ->
	    let pp1 = ppForallTyVars context.pp tvs in
	    let pp2 = ppTerm context (path, parentTerm) tm in
	    prettysNone [pp1, string " ", pp2]     

          | Any _ -> string "<anyterm>"
          | And (tms, _) -> prettysNone ([string "<AndTerms: "] 
					 ++
					 (foldl (fn (tm, pps) -> 
						 pps ++
						 [ppTerm context (path, Top) tm,
						  string " "])
					        []
						tms)
					 ++
					 [string ">"])
	  | _ -> System.fail "Uncovered case for term")
      

 def ppSortScheme context parent (tyVars, srt) = 
   let pp2 = ppSort context parent srt in
   let pp1 = ppForallTyVars context.pp tyVars in
   prettysNone [pp1, string " ", pp2]     

 def ppSort context (path, parent) srt = 
   let pp : ATermPrinter = context.pp in
   case srt of

     | CoProduct (row, _) -> 
       let
         def ppEntry (path, (id, srtOption)) = 
	   case srtOption of
	     | Some s -> 
	       prettysNone [pp.Bar, 
			    pp.fromString  id, 
			    string  " ", 
			    ppSort context (path, CoProduct) s]
	     | None -> 
	       prettysNone [pp.Bar, 
			    pp.fromString  id]
       in
       let (left, right) = 
           case parent of
	     | Product -> (pp.LP, pp.RP)
	     | CoProduct -> (pp.LP, pp.RP)
	     | Subsort -> (pp.LP, pp.RP)
	     | _ -> (pp.Empty, pp.Empty)
       in
	 AnnTermPrinter.ppListPath path ppEntry (left, pp.Empty, right) row

    | Product ([], _) -> string  "()"

    | Product (row, _) -> 
      if isShortTuple (1, row) then
	let (left, right) = 
	    case parent of
	      | Product -> (pp.LP, pp.RP)
	      | Subsort -> (pp.LP, pp.RP)
	      | _ -> (pp.Empty, pp.Empty)
	in
	  AnnTermPrinter.ppListPath path 
	                            (fn (path, (lbl, t)) -> ppSort context (path, Product) t) 
				    (left, pp.Product, right) 
	                            row
      else
	let                  
	  def ppEntry (path, (id, s)) = 
	    blockFill (0, 
		       [(0, pp.fromString  id), 
			(0, string  " : "), 
			(0, ppSort context (path, Top) s)])
	in
	  AnnTermPrinter.ppListPath path ppEntry (pp.LCurly, string ", ", pp.RCurly)  row
              
    | Arrow (dom, rng, _) -> 
      let (left, right) = 
          case parent of
	    | Product   -> (pp.LP, pp.RP)
	    | ArrowLeft -> (pp.LP, pp.RP)
	    | Subsort -> (pp.LP, pp.RP)
	    | _ -> (pp.Empty, pp.Empty)
      in
	blockFill (0, 
		   [(0, prettysNone [left, 
				     ppSort context ([0]++ path, ArrowLeft  : ParentSort) dom, 
				     pp.Arrow]), 
		    (3, prettysNone [ppSort context ([1]++ path, ArrowRight : ParentSort) rng, 
				     right])])

    | Subsort (s, Lambda ([(pat, Fun (Bool true, _, _), t)], _), _) -> 
      blockFill (0, 
		 [(0, pp.LCurly), 
		  (0, ppPattern context ([0, 0, 1] ++ path, true) pat), 
		  (0, string " : "), 
		  (0, ppSort    context ([0]       ++ path, Subsort) s), 
		  (0, pp.Bar), 
		  (0, ppTerm    context ([2, 0, 1] ++ path, Top) t), 
		  (0, pp.RCurly)])
    | Subsort (s, t, _) -> 
      blockFill (0, 
		 [(0, pp.LP), 
		  (0, ppSort context ([0] ++ path, Subsort) s), 
		  (0, pp.Bar), 
		  (0, ppTerm context ([1] ++ path, Top) t), 
		  (0, pp.RP)])
    | Quotient (s, t, _) -> 
      blockFill (0, 
		 [(0, pp.LP), 
		  (0, ppSort context ([0] ++ path, Top) s), 
		  (0, string  " / "), 
		  (0, ppTerm context ([1] ++ path, Top) t), 
		  (0, pp.RP)])

  % | Base (Qualified ("String", "String"))  -> string "String"
  % | Base (Qualified ("Nat",    "Nat"))     -> string "Nat"

    | Boolean _ -> string "Boolean"

    | Base (idInfo, [], _) -> pp.ppSortId idInfo

    | Base (idInfo, ts, _) -> 
      blockFill (0, 
		 [(0, pp.ppSortId idInfo), 
		  (0, AnnTermPrinter.ppListPath path
		   (fn (path, srt) -> ppSort context (path, Top : ParentSort) srt)
		   (pp.LP, pp.Comma, pp.RP) ts)])

%    | PBase (idInfo, [], _) -> pp.ppPSortId (idInfo)

%    | PBase (idInfo, ts, _) -> 
%            blockFill (0, 
%                [(0, pp.ppPSortId idInfo), 
%                 (0, AnnTermPrinter.ppListPath path
%                      (fn (path, srt) -> ppSort context (path, Top : ParentSort) srt)
%                      (pp.LP, pp.Comma, pp.RP) ts)])

    | TyVar (id, _) -> string id

    | MetaTyVar (mtv, _) -> string (TyVarString mtv)

    | Pi (tvs, srt, _) ->
      let pp1 = ppForallTyVars context.pp tvs in
      let pp2 = ppSort context (path, parent) srt in
      prettysNone [pp1, string " ", pp2]     

    | Any _ -> string ("<anysort>")

    | And (srts, _) -> prettysNone ([string "<AndSorts: "] 
				    ++
				    (foldl (fn (srt, pps) -> 
					    pps ++
					    [ppSort context (path, Top : ParentSort) srt,
					     string " "])
				           []
					   srts)
				    ++
				    [string ">"])

    | _ -> string ("ignoring mystery sort: " ^ (anyToString srt))
      

 def [a] TyVarString (mtv: AMetaTyVar a) : String =
   let {link, uniqueId, name} = State.! mtv in
   case link of
    | None -> "mtv%"^name^"%"^ (Nat.toString uniqueId)
    | Some srt -> printSort srt

  %% More elaborate version
  %     let linkr =
  %       case link
  %         of None  -> ""
  %          | Some srt -> "["^printSort srt^"]"
  %     in "mtv%"^Nat.toString uniqueId^linkr

 def enclose (enclosed, pretty) = 
   if enclosed then
     pretty 
   else
     prettysNone [string "(", pretty, string ")"]
        
 def ppPattern context (path, enclosed) pattern = 
   let pp : ATermPrinter = context.pp in
   case pattern of
     | WildPat   (_(* srt *), _) -> pp.Underscore
     | BoolPat   (b, _) -> string (Boolean.toString b)
     | NatPat    (n, _) -> string (Nat.toString     n)
     | StringPat (s, _) -> pp.fromString ("\""^s^"\"")               % "abc"
     | CharPat   (c, _) -> pp.fromString ("#" ^ (Char.toString c))   % #A
     | VarPat    ((id, srt), _) -> 
       if printSort? context then
	 blockFill (0, 
		    [(0, pp.fromString id), 
		     (0, string " : "), 
		     (0, ppSort context ([0] ++ path, Top : ParentSort) srt)])
       else 
	 pp.fromString id
     | EmbedPat  ("Nil", None, Base (Qualified ("List",      "List"), [_], _), _) -> string "[]"
     | EmbedPat  ("Nil", None, Base (Qualified (UnQualified, "List"), [_], _), _) -> string "[]" % ???
     | EmbedPat  (id, None, _(* srt *), _) -> pp.fromString id
     | RecordPat (row, _) ->
       if isShortTuple (1, row) then
	 AnnTermPrinter.ppListPath path 
	                           (fn (path, (id, pat)) -> ppPattern context (path, true) pat) 
				   (pp.LP, pp.Comma, pp.RP) 
				   row
       else
	 let 
           def ppEntry (path, (id, pat)) = 
	     blockFill (0, 
			[(0, prettysNone [pp.fromString id, string " ", pp.Equals, string " "]), 
			 (2, 
			  prettysFill [ppPattern context (path, true) pat])])
	 in
	   AnnTermPrinter.ppListPath path ppEntry (pp.LCurly, pp.Comma, pp.RCurly) row
     | EmbedPat ("Cons", 
		 Some (RecordPat ([("1", p1), ("2", p2)], _)), 
		 Base (_(* Qualified ("List", "List") *), [_], _), _) -> 
       enclose (enclosed, 
		prettysFill [ppPattern context ([0]++ path, false) p1, 
			     string " :: ", 
			     ppPattern context ([1]++ path, false) p2])
 %  | EmbedPat ("Cons", 
 %             Some (RecordPat ([("1", p1), ("2", p2)], _)), 
 %              PBase (_(* Qualified ("List", "List") *), [_], _), _) -> 
 %   enclose (enclosed, 
 %           prettysFill [ppPattern context ([0]++ path, false) p1, 
 %                        string " :: ", 
 %                        ppPattern context ([1]++ path, false) p2])
     | EmbedPat (id, Some pat, _(* srt *), _) -> 
       enclose (enclosed, 
		prettysFill (cons (pp.fromString id, 
				   if singletonPattern pat then
				     [string " ", 
				      ppPattern context ([0]++ path, false) pat]
				   else
				     [pp.LP, 
				      ppPattern context ([0]++ path, true) pat, 
				      pp.RP])))
     | SortedPat (pat, srt, _) -> 
       enclose (enclosed, 
		blockFill (0, 
			   [(0, ppPattern context ([0]++ path, false) pat), 
			    (0, string  " : "), 
			    (0, ppSort context ([1]++ path, Top : ParentSort) srt)]))
     | AliasPat (pat1, pat2, _) -> 
       enclose (enclosed, 
		blockFill (0, 
			   [(0, ppPattern context ([0]++ path, false) pat1), 
			    (0, string  " as "), 
			    (0, ppPattern context ([1]++ path, false) pat2)]))
     | QuotientPat (pat, qid, _) -> 
       enclose (enclosed, 
		blockFill (0, 
			   [(0, string ("quotient[" ^ toString qid ^ "]")),
			    (0, ppPattern context ([0]++ path, false) pat)]))

     | RestrictedPat (pat, term, _) ->
%% Don't want restriction expression inside parentheses in normal case statement
%       (case pat of
%	  | RecordPat (row, _) ->
%	    %% This probably isn't quite right as far as formatting the "|" term
%	    let def ppListPathPlus path f (left, sep, right) ps = 
%	          prettysNone ([left,
%			       prettysLinear (addSeparator sep 
%					      (mapWithIndex (fn (i, x) ->
%							     f (cons (i, path), x)) ps))]
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
	     enclose (enclosed, 
		      blockFill (0, 
				 [(0, ppPattern context ([0]++ path, true) pat), 
				  (0, pp.Bar), 
				  (0, ppTerm context ([1]++ path, Top) term)])) %)

     | _ -> System.fail "Uncovered case for pattern"
      

 def printTyVars tvs =
   case tvs of
     | []     -> "[]"
     | v1::vs -> "[" ^ v1 ^ (foldl (fn (v, str) -> str ^","^ v) "" vs) ^ "]"

 def useXSymbols? = true
 def uiPrinter() = if useXSymbols? then XSymbolPrinter else asciiPrinter

 def AnnSpecPrinter.printTerm term = 
   PrettyPrint.toString (format (80, ppTerm (initialize (asciiPrinter, false))
				            ([], Top) 
					    term))

 def termToPretty term =
   ppTerm (initialize (asciiPrinter, false)) ([], Top) term

 def printTermToTerminal term =
   toTerminal (format (80, ppTerm (initialize (uiPrinter(), false)) 
		                  ([], Top) 
				  term))
 
 def printSort srt = 
    PrettyPrint.toString (format (80, ppSort (initialize (asciiPrinter, false))
				             ([], Top : ParentSort) 
					     srt))

 def printSortToTerminal srt = 
   toTerminal (format (80, ppSort (initialize (uiPrinter(), false))
		                  ([], Top : ParentSort) 
				  srt))
 
 def printSortScheme scheme = 
   PrettyPrint.toString (format (80, ppSortScheme (initialize (asciiPrinter, false))
				                  ([], Top)
						  scheme))

 def printTermScheme scheme = 
   PrettyPrint.toString (format (80, ppTermScheme (initialize (asciiPrinter, false))
				                  ([], Top) 
						  scheme))

 def printPattern pat = 
   PrettyPrint.toString (format (80, ppPattern (initialize (asciiPrinter, false))
			                       ([], true) 
					       pat))

 def printTermWithSorts term = 
   PrettyPrint.toString (format (80, ppTerm (initialize (asciiPrinter, true))
			                    ([], Top)
					    term))

 def ppForallTyVars (pp : ATermPrinter) tyVars = 
   case tyVars of
     | [] -> string ""
     | _ -> AnnTermPrinter.ppList string 
                                  (prettysNone [string " ", pp.LBrack], 
				   pp.Comma, pp.RBrack)
                                  tyVars

 def ppTyVars (pp : ATermPrinter) tvs = 
   case tvs of
     | [] -> string ""
     | _ -> AnnTermPrinter.ppList string (pp.LP, pp.Comma, pp.RP) tvs

 def sortIndex     = 0
 def opIndex       = 1
 def defIndex      = 2
 def propertyIndex = 3

 def ppProperty context (index, (pt, name as Qualified (q, id), tyVars, term)) = 
   let pp : ATermPrinter = context.pp in
   let button1 = (if markSubterm? context then
		    PrettyPrint.buttonPretty (~(IntegerSet.member (context.indicesToDisable, index)), 
					      index, string " ", false) 
		  else 
		    string "")
   in
   let button2 = (if markSubterm? context then
                    PrettyPrint.buttonPretty (IntegerSet.member (context.sosIndicesToEnable, index), 
					      index, string " ", true) 
		  else 
		    string "")
   in
     (1, blockFill (0, [(0, button1), 
			(0, button2), 
			(0, case (pt:PropertyType) of
			      | Theorem    -> pp.Theorem 
			      | Axiom      -> pp.Axiom 
			      | Conjecture -> pp.Conjecture), 
			(0, pp.ppFormulaDesc (" "^ (if q = UnQualified then "" else q^".")^id)), 
			(0, string " "), 
			(0, pp.Is), 
			% (0, if null tyVars then string "" else string " sort"), 
			(0, ppForallTyVars pp tyVars), 
			(0, string " "), 
			(3, ppTerm context ([index, propertyIndex], Top) term)]))

 op  ppOpDeclOp: [a] PrContext -> Boolean -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDeclOp context blankLine? info_res =
   ppOpDecl context true false blankLine? info_res

 op  ppOpDeclDef: [a] PrContext -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDeclDef context info_res =
   ppOpDecl context false true true info_res

 op  ppOpDeclOpDef: [a] PrContext -> (AOpInfo a * IndexLines) -> IndexLines
 def ppOpDeclOpDef context info_res =
   ppOpDecl context true true true info_res


 op  ppOpDecl: [a] PrContext -> Boolean -> Boolean -> Boolean -> (AOpInfo a * IndexLines) -> IndexLines
 %% If printDef? is false print "op ..." else print "def ..."
 def ppOpDecl context printOp? printDef? blankLine? (info, (index, lines)) =
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
   let button1 = (if markSubterm? context & ~ defined? then
		    PrettyPrint.buttonPretty (~(IntegerSet.member (context.indicesToDisable, index1)), 
					      index1, string " ", false)
		  else 
		    string "")
   in
   let button2 = (if markSubterm? context & ~ defined? then
		    PrettyPrint.buttonPretty (IntegerSet.member (context.sosIndicesToEnable, index1), 
					      index1, string " ", true)
		  else 
		    string "")
   in
   let 
     def ppDecl tm =
       let (tvs, srt, _) = unpackTerm tm in
       (1, blockFill (0, [(0, pp.Op), 
			  (0, string " "), 
			  (0, ppOpNames ()), 
			  (0, case info.fixity of
				| Nonfix         -> string ""
				| Unspecified    -> string ""
				| Infix (Left, i)  -> string (" infixl "^Nat.toString i)
				| Infix (Right, i) -> string (" infixr "^Nat.toString i)), 
			  (0, string " :"), 
			  (0, blockNone (0, [(0, ppForallTyVars pp tvs), 
					     (0, string " "), 
					     (3, ppSort context ([index, opIndex], Top) srt)]))
			  ]))
       
     def ppDefAux (path, term) = 
       case term of
	 | Lambda ([(pat, Fun (Bool true, _, _), body)], _) ->
	   let pat  = ppPattern context ([0, 0] ++ path, false) pat in 
	   let body = ppDefAux ([2, 0] ++ path, body) in
	   let prettys = [(0, pat), (0, string " ")] ++ body in
	   if markSubterm? context then
	     let num = State.! context.markNumber in
	     let table = State.! context.markTable in
	     (context.markTable State.:= NatMap.insert (table, num, path);
	      context.markNumber State.:= num + 1;
	      PrettyPrint.markLines (num, prettys))
	   else 
	     prettys
	 | _ -> 
	     [(0, pp.DefEquals), 
	      (0, string " "), 
	      (2, ppTerm context (path, Top) term)]
	     
     def ppDef tm =
       let (tvs, opt_srt, tm) = unpackTerm tm in
       let prettys = ppDefAux ([index, defIndex], tm) in
       (1, blockFill (0, 
		      [(0, blockFill (0, 
				      [(0, button1), 
				       (0, button2), 
				       (0, pp.Def), 
				       (if printSort? context then
					  (0, ppForallTyVars pp tvs) 
					else 
					  (0, string "")), 
					  (0, ppOpName (primaryOpName info)),
					  (0, string " ")]
				     ))]
		      ++ prettys))
   in
   let (decls, defs) = opInfoDeclsAndDefs info in
   let warnings = 
       (let m = length decls in
	let n = length defs  in
	if m <= 1 then
	  if n <= 1 then
	    %% Precede with new line only if both op and def 
	    (if blankLine? then [(0, string " ")] else [])
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryOpName info)) ^ " has " ^ (toString n) ^ " definitions. *)"))]
	else
	  if n <= 1 then
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryOpName info)) ^ " has " ^ (toString m) ^ " declarations. *)"))]
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primaryOpName info)) ^ " has " ^ (toString m) ^ " declarations and " ^ (toString n) ^ " definitions. *)"))])
   in
   let decls = 
       %% make sure an "op ..." form is printed, to establish the type of the op
       case (decls, defs) of
	 | ([], dfn :: _) -> [dfn]
	 | _ -> decls
   in
   let ppDecls = if printOp? then map ppDecl decls else [] in
   let ppDefs  = if printDef? then map ppDef  defs else [] in
   (index + 1, warnings ++ ppDecls ++ ppDefs ++ lines)

 op  ppSortDeclSort: [a] PrContext -> (ASortInfo a * IndexLines) -> IndexLines
 def ppSortDeclSort context info_res =
   ppSortDecl context false info_res

 op  ppSortDeclDef: [a] PrContext -> (ASortInfo a * IndexLines) -> IndexLines
 def ppSortDeclDef context info_res =
   ppSortDecl context true info_res

 op  ppSortDecl: [a] PrContext -> Boolean -> (ASortInfo a * IndexLines) -> IndexLines
 %% If printDef? is false print "op ..." else print "def ..."
 def ppSortDecl context printDef? (info, (index, lines)) =
   let pp : ATermPrinter = context.pp in
   let 
     def ppSortName (qid as Qualified (q, id)) =
       if q = UnQualified then
	 pp.ppSort id
       else
	 pp.ppSortId qid

     def ppSortNames () =
       case info.names of
	 | [name] -> ppSortName name
	 | _      -> ppList ppSortName ("{", ", ", "}") info.names

     def ppLHS tvs =
       [(0, pp.Type), 
	(0, string " "), 
	(0, ppSortNames()), 
	(0, ppTyVars pp tvs)]
       
     def ppDecl srt =
       let (tvs, srt) = unpackSort srt in
       (1, blockFill (0, 
		      (ppLHS tvs))) 
       
     def ppDef srt =
       let (tvs, srt) = unpackSort srt in
       (1, blockFill (0, 
		      (ppLHS tvs) 
		      ++
		      [(0, string " "), 
		       (0, pp.DefEquals), 
		       (0, string " "), 
		       (3, ppSort context ([index, sortIndex], Top) srt)]))
   in
   let (decls, defs) = sortInfoDeclsAndDefs info in
   let warnings = 
       (let m = length decls in
	let n = length defs  in
	if m <= 1 then
	  if n <= 1 then
	    []
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primarySortName info)) ^ " has " ^ (toString n) ^ " definitions. *)"))]
	else
	  if n <= 1 then
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primarySortName info)) ^ " has " ^ (toString m) ^ " declarations. *)"))]
	  else
	    [(0, string (" (* Warning: " ^ (printQualifiedId (primarySortName info)) ^ " has " ^ (toString m) ^ " declarations and " ^ (toString n) ^ " definitions. *)"))])
   in
   let ppDecls = if printDef? then [] else map ppDecl decls in
   let ppDefs  = if printDef? then map ppDef  defs else []  in
   (index + 1, warnings ++ ppDecls ++ ppDefs ++ lines)

   % op isBuiltIn? : Import -> Boolean
   % def isBuiltIn? (specCalcTerm, _ (* spc *)) = false
   % spec_ref = "String"  or spec_ref = "Nat"  or 
   % spec_ref = "Boolean" or spec_ref = "Char" or
   % spec_ref = "Integer" or spec_ref = "List" or 
   % spec_ref = "General"


 type ImportDirections = | NotSpec (List Spec)
                         | Verbose
                         | Recursive	% Make smarter to avoid repetitions?

 %% Top-level print module; lower-level print spec
 def ppSpec context spc = 
   let pp  = context.pp in
   blockAll (0, 
	     [(0, blockFill (0, 
			     [(0, pp.Spec), 
			      (0, string " ")]))]
	     ++
	     (ppSpecElements context spc (NotSpec Nil) spc.elements)
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
	     (ppSpecElements context spc (NotSpec [base_spec]) spc.elements)
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
	     (ppSpecElements context spc Recursive spc.elements)
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
	 | Import (im_sp_tm,im_sp,im_elements) ->
	   (case import_directions of
	     | NotSpec ign_specs ->
	       if member(im_sp,ign_specs) then result
	       else (index,
		     Cons((1, blockFill (0,
					 [(0, context.pp.Import), 
					  (2, ppImportTerm context import_directions im_sp_tm)])),
			  ppResult))
	     | Verbose ->
	       (index,
		Cons((2, blockFill (0, 
				    [(0, context.pp.Import),
				     (2, ppImportTerm context import_directions im_sp_tm),
				     (2, string " |-> "), 
				     (2, ppSpecAll context im_sp)])),
		     ppResult))
	     | Recursive ->
	       %% let _ = toScreen (anyToString im_sp_tm^"\n\n") in
	       ppSpecElementsAux context spc import_directions im_elements result)
	       
	 | Op qid ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo ->
	        ppOpDeclOp context (~afterOp?) (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | OpDef qid ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo -> ppOpDeclDef context (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | Sort qid ->
	   (case findTheSort(spc,qid) of
	      | Some sortinfo -> ppSortDeclSort context (sortinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | SortDef qid ->
	   (case findTheSort(spc,qid) of
	      | Some sortinfo -> ppSortDeclDef context (sortinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | Property prop ->
	   (index+1,
	    Cons(ppProperty context (index, prop),ppResult))
	 | Comment str ->
	   (index+1,
	    if exists (fn char -> char = #\n) str then
	      [(0, string " (* "),
	       (2, string str),
	       (0, string " *) ")]
	      ++
	      ppResult
	    else
	      Cons ((0, string (" %% " ^ str)),
		    ppResult))
	 | Pragma (prefix, body, postfix, pos)->
	   (index+1,
	    Cons ((1, string (prefix ^ body ^ postfix)),
		  ppResult))

     def aux(elements,afterOp?,result) =
         case elements of
	   | [] -> result
	   | (Op qid1) :: (OpDef qid2) :: r_els ->
	     (case findTheOp(spc,qid1) of
	      | Some opinfo ->
		if qid1 = qid2
		  then ppOpDeclOpDef context (opinfo,aux(r_els, false, result))
		else ppOpDeclOp context afterOp? (opinfo,aux(Cons(OpDef qid2,r_els), true, result))
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid1 ^ "\n") in
		(0, []))
	   | el :: r_els -> ppSpecElement(el,afterOp?,aux(r_els,(embed? Op) el,result))
   in
     aux(elements,true,result)
       
 op  ppImportTerm : PrContext -> ImportDirections -> SpecCalc.Term Position -> Pretty

 %% ppImportTerm wants to dispatch on the structure of the SpecCalc.Term, but that isn't defined here,
 %% so ppImportTerm is defined over in /Languages/SpecCalculus/Semantics/Evaluate/Print.sw,
 %% where SpecCalc.Term has been defined.
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
	 | Import (im_sp_tm,im_sp,im_elements) ->
	   (case import_directions of
	     | NotSpec ign_specs ->
	       if member(im_sp,ign_specs) then result
	       else (index,
		     Cons((1, prettysFill [context.pp.Import, 
					   %% TODO: indenting this way isn't quite right,
					   %% since it will indent inside string literals
					   %% But pretty printers make it inordinately 
					   %% difficult to do simple things like indentation.
					   string (indentString "  " (showTerm im_sp_tm))]),
			  ppResult))
	     | Verbose ->
	       (index,
		Cons((2, blockFill (0, 
				    [(0, string "import "), 
				     (0, string (showTerm im_sp_tm)), 
				     (0, string " |-> "), 
				     (0, ppSpecAll context im_sp)])),
		     ppResult))
	     | Recursive ->
	       %% let _ = toScreen (anyToString im_sp_tm^"\n\n") in
	       ppSpecElementsAux context spc import_directions im_elements result)
	       
	 | Op qid ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo ->
	        ppOpDeclOp context (~afterOp?) (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | OpDef qid ->
	   (case findTheOp(spc,qid) of
	      | Some opinfo -> ppOpDeclDef context (opinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | Sort qid ->
	   (case findTheSort(spc,qid) of
	      | Some sortinfo -> ppSortDeclSort context (sortinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | SortDef qid ->
	   (case findTheSort(spc,qid) of
	      | Some sortinfo -> ppSortDeclDef context (sortinfo,result)
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing type: " ^ printQualifiedId qid ^ "\n") in
		(0, []))
	 | Property prop ->
	   (index+1,
	    Cons(ppProperty context (index, prop),ppResult))
	 | Comment str ->
	   (index+1,
	    if exists (fn char -> char = #\n) str then
	      [(0, string " (* "),
	       (2, string str),
	       (0, string " *) ")]
	      ++
	      ppResult
	    else
	      Cons ((0, string (" %% " ^ str)),
		    ppResult))
	 | Pragma (prefix, body, postfix, pos) \_rightarrow
	   (index+1,
	    Cons ((1, string (prefix ^ body ^ postfix)),
		  ppResult))

     def aux(elements,afterOp?,result) =
         case elements of
	   | [] -> result
	   | (Op qid1) :: (OpDef qid2) :: r_els ->
	     (case findTheOp(spc,qid1) of
	      | Some opinfo ->
		if qid1 = qid2
		  then ppOpDeclOpDef context (opinfo,aux(r_els, false, result))
		else ppOpDeclOp context afterOp? (opinfo,aux(Cons(OpDef qid2,r_els), true, result))
	      | _ -> 
	        let _  = toScreen("\nInternal error: Missing op: " ^ printQualifiedId qid1 ^ "\n") in
		(0, []))
	   | el :: r_els -> ppSpecElement(el,afterOp?,aux(r_els,(embed? Op) el,result))
   in
     aux(elements,true,result)

  op indentString : String -> String -> String
 def indentString prefix s =
   let newline_char = hd (explode newline) in
   let prefix = explode prefix in
   let s = foldl (fn (char, s) ->
		  if char = newline_char then
		    prefix ++ (cons (char, s))
		  else
		    cons (char, s))
                 []  
		 (explode s)
   in
     implode (rev s)

 def specToPrettyVerbose spc = 
   ppSpecAll (initialize (asciiPrinter, false)) spc

 def specToPrettyVerboseXSymbol spc = 
   ppSpecAll (initialize (XSymbolPrinter, false)) spc

 def specToPrettyFlat spc = 
   ppSpecFlat (initialize (asciiPrinter, false)) spc
   
 def specToPretty spc = 
   let base_spec = SpecCalc.getBaseSpec () in
   ppSpecHidingImportedStuff (initialize (asciiPrinter, false)) base_spec spc
   
 def specToPrettyXSymbol spc = 
   let base_spec = SpecCalc.getBaseSpec () in
   ppSpecHidingImportedStuff (initialize (XSymbolPrinter, false)) base_spec spc
   
 def specToPrettyR spc = 
   ppSpecR (initialize (asciiPrinter, false)) spc
   
 def printSpec spc =
   PrettyPrint.toString (format (80, specToPretty spc))

 def printSpecXSymbol spc =
   PrettyPrint.toString (format (80, specToPrettyXSymbol spc))
   
 def printSpecVerbose spc =
   PrettyPrint.toString (format (80, specToPrettyVerbose spc))

 def printSpecVerboseXSymbol spc =
   PrettyPrint.toString (format (80, specToPrettyVerboseXSymbol spc))

 def printSpecFlat spc =
   PrettyPrint.toString (format (80, specToPrettyFlat spc))

 def printSpecFlatToTerminal spc =
   (toTerminal (format (80, specToPrettyFlat spc)); 
    String.writeLine "")
   
 def printSpecToTerminal spc =
   (toTerminal (format (80, specToPretty spc)); 
    String.writeLine "")
   
 def printSpecToFile (fileName, spc) = 
   toFile (fileName, format (90, specToPretty spc))

 def printFlatSpecToFile (fileName, spc) = 
   toFile (fileName, format (90, specToPrettyFlat spc))
   
 def printMarkedSpecToFile (fileName, pathFileName, indicesToDisable, sosIndicesToEnable, spc) = 
   let context = initializeMark (asciiPrinter, indicesToDisable, sosIndicesToEnable) in
   let specToPretty = ppSpec context in
   (PrettyPrint.toPathFiles (fileName, pathFileName, format (90, specToPretty spc));
    State.! context.markTable)

 def printMarkedSpecToString (indicesToDisable, sosIndicesToEnable, spc) = 
   let context = initializeMark (asciiPrinter, indicesToDisable, sosIndicesToEnable) in
   let specToPretty = ppSpec context in
   let spcAndMarking = PrettyPrint.toStringWithPathIndexing (format (90, specToPretty spc)) in
   (spcAndMarking, State.! context.markTable)

 def printSpecWithSortsToTerminal spc =
   toTerminal (format (80, ppSpec (initialize (asciiPrinter, true)) spc))
   
 def latexSpecToPretty spc = 
   let pSpec = ppSpec (initialize (latexPrinter, false)) spc in
   makeSpecListing pSpec
   
 def makeSpecListing pSpec = 
   blockAll (0, 
	    [(0, string "\\specListing{"), 
	     (0, pSpec), 
	     (0, string "}")]) 
   
 def latexSpec spc = 
   PrettyPrint.toLatexString (format (90, latexSpecToPretty spc))
   
 def latexSpecToFile (fileName, spc) = 
   PrettyPrint.toLatexFile (fileName, format (90, latexSpecToPretty spc))
   
 def htmlSpecToPretty spc = 
   let pSpec = ppSpec (initialize (htmlPrinter (), false)) spc in
   prettysAll
   [string "<html><body BGCOLOR = \"#EEFFFA\"><pre>", 
    pSpec, 
    string "</pre></body></html>"]      

 def htmlSpecToFile (fileName, spc) = 
   PrettyPrint.toFile (fileName, format (90, htmlSpecToPretty spc))
   
 def boolToNat b = if b then 1 else 0
 def positive? n = if n > 0 then 1 else 0
   
 def pdfMenu spc = 
   let sorts = 
       foldriAQualifierMap 
        (fn (q, id, _, sorts) -> 
	 cons (prettysNone [string ("  \\pdfoutline goto name {"^"???"^":Type:"
				   ^ (if q = UnQualified then "" else q^".")^id^"} {"), 
			   string (if q = UnQualified then "" else q^"."), 
			   string id, 
			   string "}"], 
	      sorts))
	[] 
	spc.sorts        
   in
   let ops = 
       foldriAQualifierMap 
        (fn (q, id, _, ops) -> 
	 cons (prettysNone [string ("  \\pdfoutline goto name {"^"???"^":Op:"
				   ^ (if q = UnQualified then "" else q^".")^id^"} {"), 
			   string (if q = UnQualified then "" else q^"."), 
			   string id, 
			   string "}"], 
	      ops))
	[] 
	spc.ops
   in
   let (counter, properties) = 
       foldl (fn (el, result as (counter, list)) ->
	      case el of
		| Property(pt, qid, tvs, _) ->
	          (counter + 1, 
		   cons (string ("  \\pdfoutline goto num "^ Nat.toString counter^
				 "  {"^ printQualifiedId qid ^ "}"), 
			 list))
		| _ -> result)
             (1, []) 
	     spc.elements
   in
   let properties = rev properties    in
   let sortCount  = length sorts      in
   let opCount    = length ops        in
   let pCount     = length properties in

   let menuCount = positive? sortCount + 
                   positive? opCount +
		   positive? pCount        
   in
     prettysAll ([string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
			 Nat.toString menuCount^"  {"^"???"^"}")]
		++
		(if sortCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^
			    "} count -"^Nat.toString sortCount^
			    " {Sorts}")]
		 else 
		   [])
		++
		sorts
		++
		(if opCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^"} count -"^
			    Nat.toString opCount^
			    " {Ops}")]
		 else 
		   [])
		++
		ops
		++
		(if pCount > 0 then
		   [string ("\\pdfoutline goto name {Spec:"^"???"^"} count-"^
			    Nat.toString pCount^" {Properties}")]
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
		     string (PrettyPrint.toLatexString (format (90, makeSpecListing s)))) 
		    specs)
	       ++
	       [string "\\pdfendthread"]
	       ++
	       menues
	       ++
	       [string "\\pdfcatalog{ /PageMode /UseOutlines }", 
		string "\\end{document}"])        
                        
 def [a] pdfSpecsToFile (fileName, spcs : List (ASpec a)) = 
   PrettyPrint.toFile (fileName, format (90, pdfSpecsToPretty spcs))

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
      format (90, 
	      prettysAll
	      ([string "\\documentclass{article}", 
		string ("\\input{" ^ sw2000 ^ "/doc/pdf-sources/megamacros}"), 
		string "\\begin{document}", 
		string "\\pdfthread num 1"])))

 def [a] pdfOneSpecToFile (counter, fileName, spc : ASpec a) = 
   let spc1 = ppSpec (initialize (pdfPrinter (counter, "???"), false)) spc         in
   let menu = pdfMenu spc                                                         in
   (PrettyPrint.appendFile(fileName, 
			   format (90, string "\\newpage"));
    PrettyPrint.appendLatexFile (fileName, PrettyPrint.format (90, makeSpecListing spc1));
    menu)

 def pdfPostLudeToFile (fileName, menues) = 
   PrettyPrint.appendFile (fileName, 
     PrettyPrint.format (90, 
       prettysAll
       ([string "\\pdfendthread"]
         ++ menues
         ++ [string "\\pdfcatalog{ /PageMode /UseOutlines }", 
             string "\\end{document}"])))
endspec
