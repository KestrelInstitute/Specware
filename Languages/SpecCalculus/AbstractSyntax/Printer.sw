\section{SpecCalc pretty printer}

This is a pretty printer for the spec calculus. This is almost but
not quite throw away code. In my opinion, it should be separate from
the MetaSlang pretty printer. The problem is that the MetaSlang pretty
printer functions are parameterized on a context to handle HTML, PDF etc.
and all the Also the two pretty printers use different pretty printing
libraries. This one should be changed to use the original
pretty printer library. Alternatively, the original library should be
discarded.

We use \verb+show+ functions to render terms as strings. We
use \verb+pp+ functions to render terms as "Pretty".

Note that the shell command "show" and the spec calculus "print" command 
are implemented via SpecCalc.evaluatePrint, which is defined in 
/Languages/SpecCalculus/Semantics/Evaluate/Print.sw,
and which uses an alternative strategy of printing the value
that results from evaluating a term, as opposed the term itself
as done here.

\begin{spec}
SpecCalc qualifying spec 

 import Types
 import ../../MetaSlang/Specs/SimplePrinter % based on /Library/PrettyPrinter/WadlerLindig
 import /Languages/MetaSlang/Specs/Printer
 import /Languages/SpecCalculus/Semantics/Value

  %% ppValue is defined in /Languages/SpecCalculus/Semantics/Value, 
  %% but we can't import that without circularity...

 %% never called...
  op showSpecTerm : [a] SpecTerm a -> String
 def showSpecTerm spec_term = ppFormat (ppSpecTerm spec_term)

 %% SpecCalc.showTerm is called from /Languages/MetaSlang/Specs/Printer.sw and 
 %%  SimplePrinter.sw to print import terms.
 %% They use /Languages/MetaSlang/Specs/SpecCalc.sw as a hack to refer to this,
 %%  which they otherwise would not have access to.
  op showTerm : [a] SpecCalc.Term a -> String
 def showTerm term = ppFormat (ppTerm term)

  op showUID : UnitId -> String
 def showUID unitId = ppFormat (ppUID unitId)

%   op ppUID : UnitId -> Doc
%   def ppUID {path, hashSuffix}  = 
%     let def ppElem elem =
%       ppConcat [
%           ppString "\"",
%           ppString elem,
%           ppString "\""
%         ]
%     in
%       ppConcat [
%           ppString "[",
%           ppSep (ppString " ") (map ppElem path),
%           (case hashSuffix of
%             | None -> ppNil
%             | Some suffix -> ppString (" # " ^ suffix)),
%           ppString "]"
%         ]

  op ppUID : UnitId -> Doc
 def ppUID unitId =
   let ppLocal = ppUIDlocal unitId in
   case unitId of
     | {path=h::_,hashSuffix=_} ->
       if deviceString? h
	 then ppLocal
	 else ppAppend (ppString "/") ppLocal
     | _ -> ppLocal			% Shouldn't happen

  op ppUIDlocal : UnitId -> Doc
 def ppUIDlocal {path, hashSuffix} =
   let prefix = ppSep (ppString "/") (map ppString path) in
   case hashSuffix of
     | None -> prefix
     | Some suffix -> ppAppend prefix (ppString ("#" ^ suffix))

  op ppRelativeUID : RelativeUID -> Doc
 def ppRelativeUID relUID =
   case relUID of
     | SpecPath_Relative unitId -> ppAppend (ppString "/") (ppUIDlocal unitId)
     | UnitId_Relative   unitId -> ppUIDlocal unitId

  op showRelativeUID : RelativeUID -> String
 def showRelativeUID unitId = ppFormat (ppRelativeUID unitId)

 %% never called
  op ppSpecTerm : [a] SpecTerm a -> Doc
 def ppSpecTerm (sterm, _(* position *)) =
   case sterm of
     | Term  term -> ppTerm term
     | Decls decls -> ppDecls decls

 %% From Specware, called only for printing import SC terms !!
 %% From Forges, called for printing inline and specialize SC terms
  op ppTerm : [a] SpecCalc.Term a -> Doc
 def ppTerm (term, _(* position *)) =
   case term of
     | Print t ->
       ppConcat [ppString "print ",
		 ppTerm t]

     | UnitId unitId -> 
       ppRelativeUID unitId

     | Spec specElems -> 
       ppConcat [ppString "spec",
		 ppNewline,
		 ppString "  ",
		 ppNest 2 (ppSpecElems specElems),
		 ppNewline,
		 ppString "endspec"]

      | Qualify (term, qualifier) ->
        ppConcat [ppString qualifier,
		  ppString " qualifying ",
		  ppTerm term]

      | Translate (term, renaming) ->
	ppConcat [ppString "translate (",
		  ppTerm term,
		  ppString ") by ",
		  ppRenaming renaming]

      | Let (decls, term) ->
        ppConcat [ppString "let",
		  ppNewline,
		  ppString "  ",
		  ppNest 2 (ppDecls decls),
		  ppNewline,
		  ppString "in",
		  ppNewline,
		  ppNest 2 (ppTerm term)]

      | Where (decls, term) ->
	ppConcat [ppTerm term,
		  ppNewline,
		  ppString "  ",
		  ppString "where {",
		  ppNewline,
		  ppString "    ",
		  ppNest 4 (ppDecls decls),
		  ppNewline,
		  ppString "}"]

      | Diag elems ->
        ppConcat [ppString "diag {",    % with apologies to stephen
		  ppNewline,
		  ppString "  ",
		  ppNest 2 (ppSep ppNewline (map ppDiagElem elems)),
		  ppNewline,
		  ppString "}"]

      | Colimit term ->
	ppConcat [ppString "colim ",
		  ppTerm term]

      | Subst (specTerm,morphTerm) ->
	ppConcat [ppTerm specTerm,
		  ppString " [",
		  ppTerm morphTerm,
		  ppString "]"]

      | SpecMorph (dom, cod, elems) ->
	let 
	  def ppSpecMorphRule (rule, _(* position *)) = 
	    case rule of          
	      | Sort (left_qid, right_qid) ->
	        ppConcat [ppString " type ",
			  ppQualifier left_qid,
			  ppString " +-> ",
			  ppQualifier right_qid]
	       
	      | Op ((left_qid, _), (right_qid, _)) ->
		ppConcat [ppString " op ",
			  ppQualifier left_qid,
			  ppString " +-> ",
			  ppQualifier right_qid]

	      | Ambiguous (left_qid, right_qid) ->
		ppConcat [ppQualifier left_qid,
			  ppString " +-> ",
			    ppQualifier right_qid]
	in
          ppConcat [ppString "morphism ",
		    ppTerm dom,
		    ppString " -> ",
		    ppTerm cod,
		    ppNewline,
		    ppString "  {",
		    ppIndent (ppSep ppNewline (map ppSpecMorphRule elems)),
		    ppNewline,
		    ppString "} : "]

      | Hide (nameExprs, term) ->
        let 
	  def ppNameExpr expr = 
	    case expr of          
	      | Sort qid ->
	        ppConcat [ppString "sort ",
			  ppQualifier qid]

	      | Op (qid, optSort) ->
		ppConcat [ppString "op ",
			  ppQualifier qid]

	      | Axiom qid ->
		ppConcat [ppString "axiom ",
			  ppQualifier qid]

	      | Theorem qid ->
		ppConcat [ppString "theorem ",
			  ppQualifier qid]

	      | Conjecture qid ->
		ppConcat [ppString "conjecture ",
			  ppQualifier qid]

	      | Ambiguous qid ->
		ppQualifier qid
	in
	  ppConcat [ppString "hide {",
		    ppSep (ppString ",") (map ppNameExpr nameExprs),
		    ppString "} in",
		    ppTerm term]
    % | Export (nameExpr, term) ->
    %   ppConcat [ppString "export {",
    %             ppSep (ppString ",") (map ppIdInfo nameExpr),
    %             ppString "} from",
    %             ppTerm term]

      | Generate (target, term, optFileNm) ->
        ppConcat [ppString ("generate " ^ target ^ " "),
		  ppTerm term,
		  (case optFileNm of
		     | Some filNm -> ppString (" in " ^ filNm)
		     | _ -> ppNil)]

      | Reduce (msTerm, scTerm) ->
	ppConcat [ppString "reduce ",
		  ppATerm msTerm,
		  ppString " in ",
		  ppTerm scTerm]

      | Prove (claimName, term, proverName, assertions, proverOptions, proverBaseOptions, answer_var) ->
	  ppConcat [
	    ppString ("prove " ^ printQualifiedId(claimName) ^ " in "),
	    ppTerm term,
	    (case assertions of
	       | All -> ppNil
	       | Explicit ([]) -> ppNil
	       | Explicit (assertions) -> ppConcat [
					    ppString " using ",
					    ppSep (ppString ", ") (map ppQualifier assertions)]),
            (case proverOptions of
	       | OptionString ([option]) -> 
	                                  if option = string("") then ppNil else
					  ppConcat [
					   ppString " options ",
					   ppString (uncell (option)) ]
	       | OptionName (prover_option_name) -> ppConcat [
						    ppString " options ",
						    ppString (printQualifiedId(prover_option_name)) ])
		    ]

      | Expand term ->
	ppConcat [ppString "expand ",
		  ppTerm term]

      | Obligations term ->
	ppConcat [ppString "obligations ",
		  ppTerm term]

      | Quote (value,_,_) -> 
	ppValue value

      | Other other_term -> 
	ppOtherTerm other_term

 def ppQualifier (Qualified (q, id))  =
   if q = UnQualified then 
     ppString id
   else 
     ppString (q ^ "." ^ id)

   op ppDiagElem : [a] DiagElem a -> Doc
 def ppDiagElem (elem, _ (* position *)) =
    case elem of
      | Node (nodeId, term) ->
          ppConcat [
            ppString nodeId,
            ppString " |-> ",
            ppTerm term
          ]
      | Edge (edgeId, dom, cod, term) ->
          ppConcat [
            ppString edgeId,
            ppString " : ",
            ppString dom,
            ppString " -> ",
            ppString cod,
            ppString " |-> ",
            ppTerm term
          ]

  op ppDecls : [a] List (Decl a) -> Doc
 def ppDecls decls =
   let 
     def ppDecl (name, term) =
       ppConcat [ppString name,
		 ppString " = ",
		 ppTerm term]
   in
     ppSep ppNewline (map ppDecl decls)

  op ppSpecElems : [a] List (SpecElem a) -> Doc
 def ppSpecElems elems = ppSep ppNewline (map ppSpecElem elems)

  op ppSpecElem : [a] SpecElem a -> Doc
 def ppSpecElem (elem, _) = 
   case elem of
     | Import  term                   -> ppConcat [ppString "import ",
						   ppSep (ppString ", ") (map ppTerm term)]
     | Sort    (aliases, dfn)         -> myppASortInfo (aliases, dfn)
     | Op      (aliases, fixity, dfn) -> myppAOpInfo   (aliases, fixity, dfn)
     | Claim   property               -> ppAProperty   property
     | Comment str                    -> if exists (fn char -> char = #\n) str then
                                           ppConcat [ppString " (* ",
						     ppString str,
						     ppString " *) "]
					 else
					   ppString (" %% " ^ str)

  op ppIdInfo : List QualifiedId -> Doc
 def ppIdInfo qids = ppSep (ppString ",") (map ppString (map printQualifiedId qids))
   
  op myppASortInfo : [a] List QualifiedId * ASort a -> Doc
 def myppASortInfo (aliases, dfn) =
   let prefix = ppConcat [ppString "sort ", ppIdInfo aliases] in
   case sortDefs dfn of
     | [] ->  prefix
     | [dfn] ->
       let (tvs, srt) = unpackSort dfn in
       ppConcat [prefix,
		 ppTyVars tvs,
		 ppAppend (ppString " = ") (ppASort srt)]
     | defs ->
       ppConcat [ppNewline,
		 ppString " (* Warning: Multiple definitions for following sort: *) ",
		 ppNewline,
		 ppSep ppNewline (map (fn dfn ->
				       let (tvs, srt) = unpackSort dfn in
				       ppConcat [prefix,
						 ppTyVars tvs,
						 ppAppend (ppString " = ") (ppASort srt)])
                                      defs)]

  op ppTyVars : TyVars -> Doc
 def ppTyVars tvs =
   case tvs of
     | [] -> ppNil
     | _  -> ppConcat [ppString " (",
		       ppSep (ppString ",") (map ppString tvs),
		       ppString ") "]

  op myppAOpInfo : [a] Aliases * Fixity * ATerm a -> Doc
  def myppAOpInfo (aliases, fixity, dfn) =
    let (decls, defs) = termDeclsAndDefs dfn in
    ppConcat [ppAOpDecl (aliases, fixity, decls),
	      ppAOpDefs (aliases, defs)]

  op ppAOpDecl : [a] Aliases * Fixity * List (ATerm a) -> Doc
 def ppAOpDecl (aliases, fixity, dfns) =
   case dfns of
     | [] -> ppNil
     | dfn::_ ->
   let (tvs, srt, _) = unpackTerm dfn in
   ppConcat [ppString "op ",
	     ppIdInfo aliases,
	     (case fixity of
		| Infix (associativity, precedence) -> 
		  ppConcat [ppString (case associativity of
					| Left  -> " infixl "
					| Right -> " infixr "),
			    ppString (toString precedence)]
		| _ -> ppNil),
	     ppString " : ",
	     (case tvs of
		| [] -> ppNil
		| _ -> 
                  ppConcat [ppString "[",
			    ppSep (ppString ",") (map ppString tvs),
			    ppString "] "]),
	     ppASort srt]

  op ppAOpDefs : [a] Aliases * List (ATerm a) -> Doc
 def ppAOpDefs (aliases, defs) =
   let 
     def pp_def dfn =
       let (tvs, srt, term) = unpackTerm dfn in
       ppConcat [ppString "def ", 
		 (case tvs of
		    | [] -> ppNil
		    | _ -> 
		      ppConcat [ppString "[",
				ppSep (ppString ",") (map ppString tvs),
				ppString "]"]),
		 ppIdInfo aliases,
		 ppString " = ",
		 ppATerm term]
   in
     case defs of
       | []    -> ppNil
       | [dfn] -> pp_def dfn
       | _ ->
         ppConcat [ppNewline,
		   ppString " (* Warning: Multiple definitions for following op: *) ",
		   ppNewline,
		   ppSep ppNewline (map pp_def defs)]


 %  op ppAProperty : [a] AProperty a -> Doc
 %   def ppAProperty (propType, name, tyVars, term) =
 %     ppConcat [
 %      ppPropertyType propType,
 %      ppString " ",
 %      ppString name,
 %      ppString " ",
 %      (case tyVars of
 %        | [] -> ppNil
 %        | _ -> 
 %           ppConcat [
 %             ppString "[",
 %             ppSep (ppString ",") (map ppString tyVars),
 %             ppString "] "
 %           ]),
 %      ppString " ",
 %      ppATerm term
 %    ]
 %
 %  op ppPropertyType : PropertyType -> Doc
 %  def ppPropertyType propType =
 %    case propType of
 %      | Axiom -> ppString "axiom"
 %      | Theorem -> ppString "theorem"
 %      | Conjecture -> ppString "conjecture"
 %      | any ->
 %           fail ("No match in ppPropertyType with: '"
 %              ^ (Lisp_toString any)
 %              ^ "'")

  op  ppRenaming : Renaming -> Doc
  def ppRenaming (rules, _) =
    let 
      def ppRenamingRule (rule, _(* position *)) = 
	case rule of          
	  | Sort (left_qid, right_qid, aliases) ->
	    ppConcat [ppString " type ",
		      ppQualifier left_qid,
		      ppString " +-> ",
		      ppString (printAliases aliases)] % ppQualifier right_qid
	    
	  | Op ((left_qid,_), (right_qid, _), aliases) ->
	    ppConcat [ppString " op ",
		      ppQualifier left_qid,
		      ppString " +-> ",
		      ppQualifier right_qid]

	  | Ambiguous (left_qid, right_qid, aliases) ->
	    ppConcat [ppQualifier left_qid,
		      ppString " +-> ",
		      ppQualifier right_qid]
	  | Other other_rule ->
	    ppOtherRenamingRule other_rule
    in
      ppConcat [ppString "{",
		ppSep (ppString ", ") (map ppRenamingRule rules),
		ppString "}"]

  op ppOtherTerm         : [a] OtherTerm   a -> Doc % Used for extensions to Specware
  op ppOtherRenamingRule : OtherRenamingRule -> Doc % Used for extensions to Specware

  %% --------------------------------------------------------------------------------

  op  showValue : Value -> String
  def showValue value = ppFormat (ppValue value)

  %% --------------------------------------------------------------------------------

  op  ppValue : Value -> Doc
  def ppValue value =
    case value of
      | Spec        spc           -> ppString     (printSpec spc)
      | Morph       spec_morphism -> ppMorphism   spec_morphism
      | SpecPrism   spec_prism    -> ppPrism      spec_prism     % tentative
      | SpecInterp  spec_interp   -> ppInterp     spec_interp    % tentative
      | Diag        spec_diagram  -> ppDiagram    spec_diagram
      | Colimit     spec_colimit  -> ppColimit    spec_colimit
      | Other       other_value   -> ppOtherValue other_value
      | InProcess                 -> ppString "InProcess"
      | UnEvaluated _             -> ppString "some unevaluated term"
      | _                         -> ppString "<unrecognized value>"


  op ppOtherValue : OtherValue -> Doc % Used for extensions to Specware

  (* tentative *)
  def ppPrism {dom=_, sms=_, pmode=_, tm=_} =
    ppString "<some prism>"

  (* tentative *)
  def ppInterp {dom=_, med=_, cod=_, d2m=_, c2m=_} =
    ppString "<some interp>"

  %% --------------------------------------------------------------------------------
endspec
\end{spec}
