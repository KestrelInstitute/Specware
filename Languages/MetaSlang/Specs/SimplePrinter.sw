\section{Simple MetaSlang Pretty Printer}

A simple pretty printer for MetaSlang.

\begin{spec}
MetaSlang qualifying spec {
  import ../AbstractSyntax/SimplePrinter
  import AnnSpec

%  sort ASpec b = 
%   {
%    importInfo   : ImportInfo,       %  not used in equality test on specs
%    sorts        : ASortMap    b,
%    ops          : AOpMap      b,
%    properties   : AProperties b
%   }

  op ppASpec : fa (a) ASpec a -> Pretty
  def ppASpec (spc as {importInfo,sorts,ops,properties}) = 
    let ppImports =
      let {imports,importedSpec,localOps,localSorts} = importInfo in
      let ppNames =
        map (fn (spcRef,spc) -> ppString ("import " ^ spcRef)) imports in
      ppSep ppNewline ppNames in

    % this assume that a name used to index into the sort map also appears
    % in the list of names for that sort.
    let def doSort (qualifier,id,sortInfo) =
      ppConcat [
        ppString "sort ",
        ppASortInfo sortInfo
      ] in

    let def doOp (qualifier,id,opInfo) =
      ppConcat [
         ppString "op ",
         ppAOpInfo opInfo
      ] in
    ppConcat [
      ppString "spec {",
      ppNewline,
      ppImports,    
      ppNewline,
        ppNest 2 (ppConcat [
          ppSep ppNewline (map doSort (sortsAsList spc)),
          ppNewline,
          ppSep ppNewline (map doOp (opsAsList spc)),
          ppNewline,
          ppSep ppNewline (map ppAProperty properties)
        ]),
      ppString "}"
    ]

  op ppASortInfo : fa (a) ASortInfo a -> Pretty
  def ppASortInfo (sortInfo as (names,tyVars,optSort)) =
    let ppNames =
      case names of
        | [] -> fail "ppASortInfo: empty name list in sort info"
        | [name] -> ppQualifiedId name
        | _ -> 
            ppConcat [
              ppString "{",
              ppSep (ppString ",") (map ppQualifiedId names),
              ppString "}"
            ] in
    let ppTyVars =
      case tyVars of
        | [] -> ppNil
        | [tyVar] -> ppString (" " ^ tyVar)
        | _::_ ->
            ppConcat [
              ppString " (",
              ppSep (ppString ",") (map ppString tyVars),
              ppString ")"
            ] in
    let ppSrt =
      case optSort of
        | None -> ppNil
        | Some srt -> ppAppend (ppString " = ") (ppASort srt) in
    ppConcat [
      ppNames,
      ppTyVars,
      ppSrt
    ]

  op ppAOpInfo : fa (a) AOpInfo a -> Pretty
  def ppAOpInfo (opInfo as (names,fxty,srtScheme,optTerm)) =
    let ppNames =
      case names of
        | [] -> fail "ppAOpInfo: empty name list in sort info"
        | [name] -> ppQualifiedId name
        | _ -> 
            ppConcat [
              ppString "{",
              ppSep (ppString ",") (map ppQualifiedId names),
              ppString "}"
            ] in
    let ppSrtScheme =
      case srtScheme of
        | ([],srt) -> ppASort srt
        | (tyVars,srt) ->
             ppConcat [
               ppString "fa (",
               ppSep (ppString ",") (map ppString tyVars),
               ppString ") ",
               ppASort srt
             ] in
    let ppTrm =
      case optTerm of
        | None -> ppNil
        | Some trm ->
             ppConcat [
               ppNewline,
               ppString "def ",
               ppNames,
               ppString " = ",
               ppATerm trm
             ] in
    ppConcat [
      ppNames,
      ppString " : ",
      ppSrtScheme,
      ppTrm
    ]

  op ppAProperty : fa (a) AProperty a -> Pretty
  def ppAProperty (propType,name,tyVars,term) =
    ppConcat [
      ppPropertyType propType,
      ppString " ",
      ppString name,
      ppString " is ",
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
    ]

  op ppPropertyType : PropertyType -> Pretty
  def ppPropertyType propType =
    case propType of
      | Axiom -> ppString "axiom"
      | Theorem -> ppString "theorem"
      | Conjecture -> ppString "conjecture"
      | any ->
           fail ("No match in ppPropertyType with: '"
              ^ (System.toString any)
              ^ "'")
}
\end{spec}
