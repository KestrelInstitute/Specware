\section{Simple MetaSlang Pretty Printer}

A simple pretty printer for MetaSlang.

\begin{spec}
spec {
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
  def ppASpec {importInfo,sorts,ops,properties} = 
    let ppImports =
      let {imports,importedSpec,localOps,localSorts} = importInfo in
      let ppNames =
        map (fn (spcRef,spc) -> ppString ("import " ^ spcRef)) imports in
      ppSep ppNewline ppNames in

    % this assume that a name used to index into the sort map also appears
    % in the list of names for that sort.
    let def doSort (qualifier,id,sortInfo,pp) =
      ppConcat [
        pp,
        ppString "sort ",
        ppASortInfo sortInfo
      ] in

    let def doOp (qualifier,id,opInfo,pp) =
      ppConcat [
         pp,
         ppString "op ",
         ppAOpInfo opInfo
      ] in
    ppConcat [
      ppString "spec {",
      ppNewline,
      ppImports,    
        ppNest 2 (ppConcat [
          foldriAQualifierMap doSort ppNil sorts,
          ppNewline,
          foldriAQualifierMap doOp ppNil ops,
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
               ppNames,
               ppString " = ",
               ppATerm trm
             ] in
    ppConcat [
      ppNames,
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
