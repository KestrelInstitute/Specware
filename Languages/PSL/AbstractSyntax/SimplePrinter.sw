\section{Wadler Lindig based Printer for PSL Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import /Library/PrettyPrinter/WadlerLindig
  import ../../MetaSlang/AbstractSyntax/AnnTerm
  import ../../MetaSlang/AbstractSyntax/SimplePrinter
  import ../../MetaSlang/Specs/SimplePrinter
  import ../../SpecCalculus/AbstractSyntax/Printer
  import Types

  % op SpecCalc.ppOtherTerm : fa (a) SpecCalc.OtherTerm a -> Doc
  def SpecCalc.ppOtherTerm scTerm =
    case scTerm of
      | Inline (name,scTerm) ->
           ppConcat [
             ppString "inline ",
             ppString name,
             ppString " ",
             ppTerm scTerm
           ]
      | Specialize (msTerm,scTerm) ->
           ppConcat [
             ppString "specialize ",
             ppATerm msTerm,
             ppString " ",
             ppTerm scTerm
           ]
    | OscarDecls decls -> ppOscarSpecTerm decls

  op ppOscarSpecTerm : fa (a) List (OscarSpecElem a) -> Doc
  def ppOscarSpecTerm pSpecElems =
          ppConcat [
            ppString "psl {",
            ppNewline,
            ppString "  ",
            ppIndent (ppSep ppNewline (map ppOscarSpecElem pSpecElems)),
            ppNewline,
            ppString "}"
          ]

  op ppCommands : fa(a) List (Command a) -> Pretty
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
            ppIndent (ppSep ppNewline (map ppOscarSpecElem decls)),
            ppNewline,
            ppString "in {",
            ppNewline,
            ppString "  ",
            ppIndent (ppCommand cmd),
            ppNewline,
            ppString "}"
          ]
      | Seq commands -> ppCommands commands
      | Relation term ->
         ppConcat [
           ppString "<|",
           ppATerm term,
           ppString "|>"
         ]
      | Exec term -> ppATerm term
      | Return None -> ppString "return"
      | Return (Some term) ->
          ppConcat [
            ppString "return ",
            ppATerm term
          ]
      | Skip -> ppString "skip"
      | Break -> ppString "break"
      | Continue -> ppString "continue"

  op ppCases : fa(a) List (Case a) -> Pretty
  def ppCases cases =
    let def ppCase ((vars,pat,guard2,cmd),_) =
      ppConcat [
        ppString "var (",
        ppSep (ppString ",") (map ppAVar vars),
        ppString ") ",
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

  op ppOscarSpecElem : fa(a) OscarSpecElem a -> Pretty
  def ppOscarSpecElem (decl,_) = 
    case decl of
      | Sort (names,(tyVars,defs)) -> 
          ppConcat [
            ppString "sort ",
            ppASortInfo (names,tyVars,defs)
          ]
      | Def (names,(fxty,srtScheme,defs)) ->
          ppConcat [
            ppString "def ",
            ppAOpInfo (names,fxty,srtScheme,defs)
          ]
      | Op (names,(fxty,srtScheme,defs)) ->
          ppConcat [
            ppString "op ",
            ppAOpInfo (names,fxty,srtScheme,defs)
          ]
      | Claim claim -> pp claim
      | Var (names,(fxty,srtScheme,defs)) ->
          ppConcat [
            ppString "var ",
            ppAOpInfo (names,fxty,srtScheme,defs)
          ]
      | Proc (name,procInfo) ->
          ppConcat [
            ppString "proc ",
            ppString name,
            ppString " ",
            ppProcInfo procInfo
          ]

  op AbsSynClaim.pp : fa (a) Claim a -> Pretty
  def AbsSynClaim.pp (claimType, qid, tyVars,term) =
    ppConcat [
      pp claimType,
      ppString " ",
      ppQualifiedId qid,
      ppGroup (ppIndent (ppConcat [
        ppString " is",
        ppBreak,
        ppGroup (ppConcat [
          (case tyVars of
             | [] -> ppNil
             | _ -> 
                ppConcat [
                  ppString "fa (",
                  ppSep (ppString ",") (map ppString tyVars),
                  ppString ") "
                ]),
          ppString " ",
          ppATerm term
        ])
      ]))
    ]

  op AbsSynClaimType.pp : ClaimType -> Pretty
  def AbsSynClaimType.pp claimType =
    case claimType of
      | Axiom -> ppString "axiom"
      | Theorem -> ppString "theorem"
      | Conjecture -> ppString "conjecture"
      | Invariant -> ppString "invariant"
      | any ->
           fail ("No match in ppPropertyType with: '"
              ^ (anyToString any)
              ^ "'")

  op ppOscarSpecElems : fa(a) List (OscarSpecElem a) -> Pretty
  def ppOscarSpecElems decls = ppSep ppNewline (map ppOscarSpecElem decls)

  op ppProcInfo : fa (a) ProcInfo a -> Pretty
  def ppProcInfo procInfo =
    ppConcat [
      ppString "(",
      ppSep (ppString ",") (map ppAVar (formalArgs procInfo)),
      ppString "):",
      ppASort (returnSort procInfo),
      ppString " {",
      ppNewline,
      ppString "  ",
      ppIndent (ppCommand (command procInfo)),
      ppNewline,
      ppString "}"
    ]
}
