\section{Wadler Lindig based Printer for PSL Calculus}

\begin{spec}
SpecCalc qualifying spec {
  import /Library/PrettyPrinter/WadlerLindig
  import ../../MetaSlang/AbstractSyntax/AnnTerm
  import ../../MetaSlang/AbstractSyntax/SimplePrinter
  import ../../MetaSlang/Specs/SimplePrinter
  import Types

  op ppPSpecTerm : fa (a) List (PSpecElem a) -> Doc
  def ppPSpecTerm pSpecElems =
          ppConcat [
            ppString "psl {",
            ppNewline,
            ppString "  ",
            ppIndent (ppSep ppNewline (map ppPSpecElem pSpecElems)),
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
            ppIndent (ppSep ppNewline (map ppPSpecElem decls)),
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
      | Claim property -> ppAProperty property
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
