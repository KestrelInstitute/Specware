\section{Wadler Lindig based Printer for PSL Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import /Library/PrettyPrinter/WadlerLindig
  import ../../MetaSlang/AbstractSyntax/AnnTerm
  import ../../MetaSlang/AbstractSyntax/SimplePrinter
  import ../../MetaSlang/Specs/SimplePrinter
  import Types

  op ppCommands : fa(a) List (Command a) -> Pretty
  op showSpecFile : fa (a) SpecFile a -> String
  def showSpecFile specFile = ppFormat (ppSpecFile specFile)

  op showTerm : fa (a) SpecCalc.Term a -> String
  def showTerm term = ppFormat (ppTerm term)

  op showURI : URI -> String
  def showURI uri = ppFormat (ppURI uri)

  op ppURI : URI -> Doc
  def ppURI uri = ppAppend (ppString "/") (ppURIlocal uri)

  op ppURIlocal : URI -> Doc
  def ppURIlocal {path,hashSuffix} =
    let prefix = ppSep (ppString "/") (map ppString path) in
    case hashSuffix of
      | None -> prefix
      | Some suffix -> ppAppend prefix (ppString ("#" ^ suffix))

  op ppRelativeURI : RelativeURI -> Doc
  def ppRelativeURI relURI =
    case relURI of
        | SpecPath_Relative uri -> ppAppend (ppString "/") (ppURIlocal uri)
        | URI_Relative uri -> ppURIlocal uri

  op showRelativeURI : RelativeURI -> String
  def showRelativeURI uri = ppFormat (ppRelativeURI uri)

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
      | URI uri -> ppRelativeURI uri
      | PSL pSpecElems -> 
          ppConcat [
            ppString "psl {",
            ppNewline,
            ppString "  ",
            ppIndent (ppSep ppNewline (map ppPSpecElem pSpecElems)),
            ppNewline,
            ppString "}"
          ]
      | Spec specElems -> 
          ppConcat [
            ppString "spec {",
            ppNewline,
            ppString "  ",
            ppNest 2 (ppSpecElems specElems),
            ppNewline,
            ppString "}"
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
		 | Sort (left_qid, right_qid) ->
  		   ppConcat [
			     ppQualifier left_qid,
			     ppString " -> ",
			     ppQualifier right_qid
			    ] 
		 | Op ((left_qid,_), (right_qid,_)) ->
		   ppConcat [
			     ppQualifier left_qid,
			     ppString " -> ",
			     ppQualifier right_qid
			    ] 
		 | Ambiguous (left_qid, right_qid) ->
		   ppConcat [
			     ppQualifier left_qid,
			     ppString " -> ",
			     ppQualifier right_qid
			    ] 
	  in
	    ppConcat [
            ppString "{",
            ppSep (ppString ", ") (map ppTranslateRule translation),
            ppString "}",
            ppString " translating ",
            ppTerm term
          ]
      | Let (decls, term) ->
          ppConcat [
            ppString "let {",
            ppNewline,
            ppString "  ",
            ppNest 2 (ppDecls decls),
            ppNewline,
            ppString "} in",
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
(*
      | SpecMorph (dom,cod,elems) ->
          let def ppSpecMorphElem ((id,term),pos) =
            ppConcat [
              ppIdInfo id,
              ppString " |-> ",
              ppATerm term
            ] in
          ppConcat [
            ppString "morph {",
            ppNewline,
            ppString "  ",
            ppNest (Integer.fromNat 2) (ppSep ppNewline (map ppSpecMorphElem elems)),
            ppNewline,
            ppString "} : ",
            ppTerm dom,
            ppString " -> ",
            ppTerm cod
          ]
      | Hide (nameExpr,term) ->
          ppConcat [
            ppString "hide {",
            ppSep (ppString ",") (map ppIdInfo nameExpr),
            ppString "} in",
            ppTerm term
          ]
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

  def ppQualifier(Qualified(Qualifier,Id))  =
    if Qualifier = UnQualified then ppString Id
      else ppString(Qualifier^"."^Id)

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
            ppTerm term
          ]
      | Sort (names,(tyVars,optSort)) -> 
          ppConcat [
            ppString "sort ",
            ppASortInfo (names,tyVars,optSort)
          ]
      | Op (names,(fxty,srtScheme,optTerm)) ->
          ppConcat [
            ppString "op ",
            ppAOpInfo (names,fxty,srtScheme,optTerm)
          ]
      | Claim property -> ppAProperty property

  def ppCommands cmds = ppSep (ppAppend (ppString ";") ppNewline) (map ppCommand cmds)

  op ppCommand : fa(a) Command a -> Pretty
  def ppCommand (cmd,_) =
    case cmd of
      | If alts ->
          ppConcat [
            ppString "if {",
            ppNewline,
            ppString "  ",
            ppIndent (ppAlts alts),
            ppNewline,
            ppString "}"
          ]
      | Case (term,cases) ->
          ppConcat [
            ppString "case ",
            ppATerm term,
            ppString " of",
            ppNewline,
            ppString "  ",
            ppIndent (ppCases cases)
          ]
      | Do alts ->
          ppConcat [
            ppString "do",
            ppNewline,
            ppString "  ",
            ppIndent (ppAlts alts)
          ]
      | Assign (term1,term2) ->
          ppConcat [
            ppATerm term1,
            ppString " := ",
            ppATerm term2
          ]
      | Let (decls,cmd) ->
          ppConcat [
            ppString "let",
            ppNewline,
            ppString "  ",
            ppIndent (ppSep ppNewline (map ppPSpecElem decls)),
            ppNewline,
            ppString "in {",
            ppNewline,
            ppString "  ",
            ppIndent (ppCommand cmd),
            ppNewline,
            ppString "}"
          ]
(*
      | Call (id,terms) ->
          ppConcat [
            ppString "call ",
            ppString id,
            ppString "(",
            ppSep (ppString ",") (map ppATerm terms),
            ppString ")"
          ]
      | AssignCall (term,id,terms) ->
          ppConcat [
            ppATerm term,
            ppString " := ",
            ppString "call ",
            ppString id,
            ppString "(",
            ppSep (ppString ",") (map ppATerm terms),
            ppString ")"
          ]
*)
      | Seq commands -> ppCommands commands
      | Relation term ->
         ppConcat [
           ppString "<|",
           ppATerm term,
           ppString "|>"
         ]
      | Exec term -> ppATerm term
      | Return term ->
          ppConcat [
            ppString "return ",
            ppATerm term
          ]

  op ppCases : fa(a) List (Case a) -> Pretty
  def ppCases cases =
    let def ppCase ((pat,guard2,cmd),_) =
      ppConcat [
        ppAPattern pat,
        ppString " -> ",
        ppIndent (ppCommand cmd)
      ] in
    ppConcat [
      ppString "  ",
      ppSep (ppAppend ppNewline (ppString "| ")) (map ppCase cases)
    ]

  op ppAlts : fa(a) List (Alternative a) -> Pretty
  def ppAlts alts = 
    let def ppAlt ((guard2,cmd),_) =
      ppConcat [
        ppATerm guard2,
        ppString " -> ",
        ppIndent (ppCommand cmd)
      ] in
    ppConcat [
      ppString "  ",
      ppSep (ppAppend ppNewline (ppString "| ")) (map ppAlt alts)
    ]

  op ppPSpecElem : fa(a) PSpecElem a -> Pretty
  def ppPSpecElem (decl,_) = 
    case decl of
      | Sort (names,(tyVars,optSort)) -> 
          ppConcat [
            ppString "sort ",
            ppASortInfo (names,tyVars,optSort)
          ]
      | Def (names,(fxty,srtScheme,optTerm)) ->
          ppConcat [
            ppString "def ",
            ppAOpInfo (names,fxty,srtScheme,optTerm)
          ]
      | Op (names,(fxty,srtScheme,optTerm)) ->
          ppConcat [
            ppString "op ",
            ppAOpInfo (names,fxty,srtScheme,optTerm)
          ]
      | Claim property -> ppAProperty property
      | Var (names,(fxty,srtScheme,optTerm)) ->
          ppConcat [
            ppString "var ",
            ppAOpInfo (names,fxty,srtScheme,optTerm)
          ]
      | Proc (name,procInfo) ->
          ppConcat [
            ppString "proc ",
            ppString name,
            ppString " ",
            ppProcInfo procInfo
          ]

  op ppPSpecElems : fa(a) List (PSpecElem a) -> Pretty
  def ppPSpecElems decls = ppSep ppNewline (map ppPSpecElem decls)

  op ppProcInfo : fa (a) ProcInfo a -> Pretty
  def ppProcInfo procInfo =
    ppConcat [
      ppString "(",
      ppSep (ppString ",") (map ppAVar procInfo.args),
      ppString "):",
      ppASort procInfo.returnSort,
      ppString " {",
      ppNewline,
      ppString "  ",
      ppIndent (ppCommand procInfo.command),
      ppNewline,
      ppString "}"
    ]
}
