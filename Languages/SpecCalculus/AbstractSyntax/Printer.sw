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

Note that the spec calculus "print" command is implemented via 
SpecCalc.evaluatePrint, which is defined in 
/Languages/SpecCalculus/Semantics/Evaluate/Print.sw,
and which uses an alternative strategy of printing the value
that results from evaluating a term, as opposed the term itself
as done here.

\begin{spec}
SpecCalc qualifying spec {
  import Types
  import ../../MetaSlang/Specs/SimplePrinter 
  import /Library/PrettyPrinter/WadlerLindig

  op showSpecFile : fa (a) SpecFile a -> String
  def showSpecFile specFile = ppFormat (ppSpecFile specFile)

  op showTerm : fa (a) SpecCalc.Term a -> String
  def showTerm term = ppFormat (ppTerm term)

  op showUID : UnitId -> String
  def showUID unitId = ppFormat (ppUID unitId)

%   op ppUID : UnitId -> Doc
%   def ppUID {path,hashSuffix}  = 
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
  def ppUID unitId = ppAppend (ppString "/") (ppUIDlocal unitId)

  op ppUIDlocal : UnitId -> Doc
  def ppUIDlocal {path,hashSuffix} =
    let prefix = ppSep (ppString "/") (map ppString path) in
    case hashSuffix of
      | None -> prefix
      | Some suffix -> ppAppend prefix (ppString ("#" ^ suffix))

  op ppRelativeUID : RelativeUID -> Doc
  def ppRelativeUID relUID =
    case relUID of
        | SpecPath_Relative unitId -> ppAppend (ppString "/") (ppUIDlocal unitId)
        | UnitId_Relative unitId -> ppUIDlocal unitId

  op showRelativeUID : RelativeUID -> String
  def showRelativeUID unitId = ppFormat (ppRelativeUID unitId)

  op ppSpecFile : fa (a) SpecFile a -> Doc
  def ppSpecFile (specFile as (term,_ (* position *))) =
    case term of
      | Term term -> ppTerm term
      | Decls decls -> ppDecls decls

  op ppTerm : fa (a) SpecCalc.Term a -> Doc
  def ppTerm (term, _(* position *)) =
    case term of
      | Print t ->
          ppConcat [
            ppString "print ",
            ppTerm t
          ]
      | UnitId unitId -> ppRelativeUID unitId
      | Spec specElems -> 
          ppConcat [
            ppString "spec",
            ppNewline,
            ppString "  ",
            ppNest 2 (ppSpecElems specElems),
            ppNewline,
            ppString "endspec"
          ]
      | Qualify (term, qualifier) ->
          ppConcat [
            ppString qualifier,
            ppString " qualifying ",
            ppTerm term
          ]
      | Translate (term, (translation,_)) ->
          let def ppTranslateRule (rule, _(* position *)) = 
               case rule of          
                 | Sort (left_qid, right_qid, aliases) ->
                     ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
                 | Op ((left_qid,_), (right_qid,_), aliases) ->
                   ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
                 | Ambiguous (left_qid, right_qid, aliases) ->
                   ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
          in
            ppConcat [
            ppString "translate (",
            ppTerm term,
            ppString ") by {",
            ppSep (ppString ", ") (map ppTranslateRule translation),
            ppString "}"
          ]
      | Let (decls, term) ->
          ppConcat [
            ppString "let",
            ppNewline,
            ppString "  ",
            ppNest 2 (ppDecls decls),
            ppNewline,
            ppString "in",
            ppNewline,
            ppNest 2 (ppTerm term)
          ]
      | Where (decls, term) ->
          ppConcat [
            ppTerm term,
            ppNewline,
            ppString "  ",
            ppString "where {",
            ppNewline,
            ppString "    ",
            ppNest 4 (ppDecls decls),
            ppNewline,
            ppString "}"
          ]
      | Diag elems ->
          ppConcat [
            ppString "diag {",    % with apologies to stephen
            ppNewline,
            ppString "  ",
            ppNest 2 (ppSep ppNewline (map ppDiagElem elems)),
            ppNewline,
            ppString "}"
          ]
      | Colimit term ->
          ppConcat [
            ppString "colim ",
            ppTerm term
          ]
      | Subst (specTerm,morphTerm) ->
          ppConcat [
            ppTerm specTerm,
            ppString " [",
            ppTerm morphTerm,
            ppString "]"
          ]
      | SpecMorph (dom,cod,elems) ->
          let def ppSpecMorphRule (rule, _(* position *)) = 
               case rule of          
                 | Sort (left_qid, right_qid) ->
                     ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
                 | Op ((left_qid,_), (right_qid,_)) ->
                   ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
                 | Ambiguous (left_qid, right_qid) ->
                   ppConcat [
                             ppQualifier left_qid,
                             ppString " +-> ",
                             ppQualifier right_qid
                            ] 
            in
          ppConcat [
            ppString "morphism ",
            ppTerm dom,
            ppString " -> ",
            ppTerm cod,
            ppNewline,
            ppString "  {",
            ppIndent (ppSep ppNewline (map ppSpecMorphRule elems)),
            ppNewline,
            ppString "} : "
          ]
      | Hide (nameExprs,term) ->
          let def ppNameExpr expr = 
               case expr of          
                 | Sort qid ->
                     ppConcat [
                       ppString "sort ",
                       ppQualifier qid
                     ]
                 | Op (qid,optSort) ->
                     ppConcat [
                       ppString "op ",
                       ppQualifier qid
                     ] 
                 | Axiom qid ->
                     ppConcat [
                       ppString "axiom ",
                       ppQualifier qid
                     ]
                 | Theorem qid ->
                     ppConcat [
                       ppString "theorem ",
                       ppQualifier qid
                     ]
                 | Conjecture qid ->
                     ppConcat [
                       ppString "conjecture ",
                       ppQualifier qid
                     ]
                 | Ambiguous qid ->
                     ppQualifier qid
          in
            ppConcat [
              ppString "hide {",
              ppSep (ppString ",") (map ppNameExpr nameExprs),
              ppString "} in",
              ppTerm term
            ]
(*
      | Export (nameExpr,term) ->
          ppConcat [
            ppString "export {",
            ppSep (ppString ",") (map ppIdInfo nameExpr),
            ppString "} from",
            ppTerm term
          ]
*)

      | Generate (target,term,optFileNm) ->
          ppConcat [
            ppString ("generate " ^ target ^ " "),
            ppTerm term,
            (case optFileNm of
                   | Some filNm -> ppString(" in " ^ filNm)
               | _ -> ppNil)
          ]

      | Reduce (msTerm,scTerm) ->
          ppConcat [
            ppString "reduce ",
            ppATerm msTerm,
            ppString " in ",
            ppTerm scTerm
          ]

      | Prove (claimName, term, proverName, assertions, proverOptions) ->
	  ppConcat [
	    ppString ("prove " ^ claimName ^ " in "),
	    ppTerm term,
	    (case assertions of
	       | All -> ppNil
	       | Explicit ([]) -> ppNil
	       | Explicit (assertions) -> ppConcat [
					    ppString " using ",
					    ppSep (ppString ", ") (map ppString assertions)]),
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
      | Obligations term ->
          ppConcat [
            ppString "obligations ",
            ppTerm term
          ]

      | Other other_term -> ppOtherTerm other_term

  def ppQualifier (Qualified (Qualifier,Id))  =
    if Qualifier = UnQualified then ppString Id
      else ppString (Qualifier ^ "." ^ Id)

  op ppDiagElem : fa (a) DiagElem a -> Doc
  def ppDiagElem (elem, _ (* position *)) =
    case elem of
      | Node (nodeId,term) ->
          ppConcat [
            ppString nodeId,
            ppString " |-> ",
            ppTerm term
          ]
      | Edge (edgeId,dom,cod,term) ->
          ppConcat [
            ppString edgeId,
            ppString " : ",
            ppString dom,
            ppString " -> ",
            ppString cod,
            ppString " |-> ",
            ppTerm term
          ]

  op ppDecls : fa (a) List (Decl a) -> Doc
  def ppDecls decls =
    let def ppDecl (name,term) =
      ppConcat [
        ppString name,
        ppString " = ",
        ppTerm term
      ]
    in
      ppSep ppNewline (map ppDecl decls)

  op ppSpecElems : fa (a) List (SpecElem a) -> Doc
  def ppSpecElems elems = ppSep ppNewline (map ppSpecElem elems)

  op ppSpecElem : fa(a) SpecElem a -> Doc
  def ppSpecElem (elem,_) = 
    case elem of
      | Import term ->
          ppConcat [
            ppString "import ",
            ppSep (ppString ", ") (map ppTerm term)
          ]
      | Sort (aliases, sortInfo) -> myppASortInfo (aliases, sortInfo)
      | Op   (aliases, opInfo)   -> myppAOpInfo   (aliases, opInfo)
      | Claim property           -> ppAProperty property

  op ppIdInfo : List QualifiedId -> Doc
  def ppIdInfo qids = ppSep (ppString ",") (map ppString (map printQualifiedId qids))
   
  op myppASortInfo : fa (a) List QualifiedId * (TyVars * List (ASortScheme a)) -> Doc
  def myppASortInfo (aliases, sortInfo) =
    let prefix = ppConcat [ppString "sort ", ppIdInfo aliases] in
    case sortInfo of
      | ([],[]) ->  prefix
      | (_,[(type_vars, srt)]) ->
        ppConcat [prefix,
                  ppTyVars type_vars,
                  ppAppend (ppString " = ") (ppASort srt)]
      | (tyVars,defs) -> 
        ppConcat [ppNewline,
                  ppString " (* Warning: Multiple definitions for following sort: *) ",
                  ppNewline,
                  ppSep ppNewline (map (fn (type_vars,srt) ->
                                        ppConcat [prefix,
                                                  ppTyVars type_vars,
                                                  ppAppend (ppString " = ") (ppASort srt)])
                                       defs)]

  op ppTyVars : TyVars -> Doc
  def ppTyVars type_vars =
    case type_vars of
      | [] -> ppNil
      | _  -> ppConcat [ppString " (",
                        ppSep (ppString ",") (map ppString type_vars),
                        ppString ") "]


  op myppAOpInfo : fa (a)  (List QualifiedId) * (Fixity * ASortScheme a * List (List String * ATerm a)) -> Doc
  def myppAOpInfo (aliases, (fixity, sort_scheme, defs)) =
    case defs of
     | [] -> ppAOpDecl (aliases, fixity, sort_scheme)
     | _  -> ppAOpDefs (aliases, defs)

  op ppAOpDecl : fa (a)  (List QualifiedId) * Fixity * ASortScheme a -> Doc
  def ppAOpDecl (aliases, fixity, (type_vars, srt)) =
    ppConcat [ppString "op ",
              ppIdInfo aliases,
              ppString " : ",
              (case type_vars of
                 | [] -> ppNil
                 | _ -> 
                   ppConcat [ppString "fa (",
                             ppSep (ppString ",") (map ppString type_vars),
                             ppString ") "
                            ]),
              ppASort srt]

  op ppAOpDefs : fa (a)  (List QualifiedId) * List (List String * ATerm a) -> Doc
  def ppAOpDefs (aliases, defs) =
    let prefix = ppConcat [ppString "def ", ppIdInfo aliases] in
    let def pp_def (type_vars, term) =
        ppConcat [prefix,
                  (case type_vars of
                     | [] -> ppNil
                     | _ -> 
                       ppConcat [ppString "fa (",
                                 ppSep (ppString ",") (map ppString type_vars),
                                 ppString ")"
                                ]),
                  ppString " = ",
                  ppATerm term]
    in
    case defs of
      | [scheme] -> pp_def scheme
      | _ ->
        ppConcat [ppNewline,
                  ppString " (* Warning: Multiple definitions for following sort: *) ",
                  ppNewline,
                  ppSep ppNewline (map pp_def defs)]


%   op ppAProperty : fa (a) AProperty a -> Doc
%   def ppAProperty (propType, name, tyVars, term) =
%     ppConcat [
%       ppPropertyType propType,
%       ppString " ",
%       ppString name,
%       ppString " ",
%       (case tyVars of
%         | [] -> ppNil
%         | _ -> 
%            ppConcat [
%              ppString "fa (",
%              ppSep (ppString ",") (map ppString tyVars),
%              ppString ") "
%            ]),
%       ppString " ",
%       ppATerm term
%     ]
% 
%   op ppPropertyType : PropertyType -> Doc
%   def ppPropertyType propType =
%     case propType of
%       | Axiom -> ppString "axiom"
%       | Theorem -> ppString "theorem"
%       | Conjecture -> ppString "conjecture"
%       | any ->
%            fail ("No match in ppPropertyType with: '"
%               ^ (Lisp_toString any)
%               ^ "'")

  op ppOtherTerm : fa (a) OtherTerm a -> Doc % Used for extensions to Specware

}
\end{spec}
