\section{Simple MetaSlang Pretty Printer}

A simple pretty printer for MetaSlang.

\begin{spec}
SpecCalc qualifying spec {
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
    let ppImports = ppNil in
      % let {imports,localOps,localSorts} = importInfo in
      % let ppNames =
        % map (fn (specCalcTerm,spc) -> ppString ("import " ^ (showTerm specCalcTerm))) imports in
      % ppSep ppNewline ppNames in

    % this assume that a name used to index into the sort map also appears
    % in the list of names for that sort.
    let def doSortInfo sortInfo =
      ppConcat [
        ppString "type ",
        ppASortInfo sortInfo
      ] in
    let def doOpInfo opInfo =
      ppConcat [
         ppString "op ",
         ppAOpInfo opInfo
      ] in
    ppConcat [
      ppString "spec {",
      ppIndent (ppSep ppNewline (
          [ppImports]
          ++ (map doSortInfo (sortInfosAsList spc))
          ++ (map doOpInfo (opInfosAsList spc))
          ++ (map ppAProperty properties))),
      ppString "}"
    ]

  op ppASpecLocal : fa (a) ASpec a -> Pretty
  def ppASpecLocal (spc as {importInfo,sorts,ops,properties}) = 
    let {imports,localOps,localSorts,localProperties=_} = importInfo in
    let ppImports =
      let ppNames =
        map (fn (specCalcTerm,spc) -> ppString ("import " ^ (showTerm specCalcTerm))) spc.importInfo.imports in
      ppSep ppNewline ppNames in

    % this assume that a name used to index into the sort map also appears
    % in the list of names for that sort.
    let def doSortInfo sortInfo =
      ppConcat [
        ppString "type ",
        ppASortInfo sortInfo
      ] in
    let def doOpInfo opInfo =
      ppConcat [
         ppString "op ",
         ppAOpInfo opInfo
      ] in
    ppConcat [
      ppString "spec {",
      ppIndent (ppConcat [
        ppNewline,
        ppSep ppNewline [
          ppImports,    
          ppSep ppNewline (map doSortInfo (filter (fn info -> member (primarySortName info, localSorts))
					          (sortInfosAsList spc))),
          ppSep ppNewline (map doOpInfo   (filter (fn info -> member (primaryOpName   info, localOps))
					           (opInfosAsList spc))),
          ppSep ppNewline (map ppAProperty (localProperties spc))
        ]
      ]),
      ppString "}"
    ]

  
  op ppASortInfo : fa (a) ASortInfo a -> Pretty
  def ppASortInfo info =
    let ppNames =
      case info.names of
        | [] -> fail "ppASortInfo: empty name list in sort info"
        | [name] -> ppQualifiedId name
        | _ -> 
            ppConcat [
              ppString "{",
              ppSep (ppString ",") (map ppQualifiedId info.names),
              ppString "}"
            ] in
    let def doTyVars ty_vars =
          case ty_vars of
	    | [] -> ppNil
	    | [ty_var] -> ppString (" " ^ ty_var)
	    | _::_ ->
              ppConcat [ppString " (",
			ppSep (ppString ",") (map ppString ty_vars),
			ppString ")"]
	def doSortDef (type_vars, srt) =
	  ppConcat [ppNames, 
		    doTyVars type_vars, 
		    ppString " = ", 
		    ppASort srt] 
    in
    case info.dfn of
      | []        -> ppConcat [ppNames, 
			       doTyVars info.tvs]
      | [srt_def] -> doSortDef srt_def
      | _         -> ppConcat [ppNewline, 
			       ppString " (* Warning: Multiple Sort Definitions for following sort *) ",
			       ppNewline, 
			       ppSep ppNewline (map doSortDef info.dfn)]


  op ppAOpInfo : fa (a) AOpInfo a -> Pretty
  def ppAOpInfo info = 
    let ppNames =
      case info.names of
        | [] -> fail "ppAOpInfo: empty name list in sort info"
        | [name] -> ppQualifiedId name
        | _      -> ppConcat [ppString "{",
			      ppSep (ppString ",") (map ppQualifiedId info.names),
			      ppString "}"]
    in
    let ppSrtScheme =
      case info.typ of
        | ([],srt) -> ppASort srt
        | (tyVars,srt) ->
          ppConcat [ppString "[",
		    ppSep (ppString ",") (map ppString tyVars),
		    ppString "] ",
		    ppASort srt]
    in
    let def doOpDef (type_vars, term) =
          ppGroup (ppConcat [ppString "def ",
			     case type_vars of
			       | [] -> ppNil
			       | _  -> ppConcat [ppString "[",
						 ppSep (ppString ",") (map ppString type_vars),
						 ppString "] "],
			     ppNames,
			     ppGroup (ppIndent (ppConcat [ppString " =",
							  ppBreak,
							  ppGroup (ppATerm term)]))
			    ])
    in
    let ppDefs =
      case info.dfn of
        | []   -> ppNil
        | [op_def] -> ppCons ppNewline (doOpDef op_def)
        | _        -> ppConcat [ppNewline, 
                                ppString " (* Warning: Multiple Definitions for following op *) ",
                                ppNewline, 
                                ppSep ppNewline (map doOpDef info.dfn)]
    in
    ppConcat [ppNames,
              ppString " : ",
              ppSrtScheme,
              ppDefs]

  op ppAProperty : fa (a) AProperty a -> Pretty
  def ppAProperty (propType, name, tyVars, term) =
    ppConcat [
      ppPropertyType propType,
      ppString " ",
      ppQualifiedId name,
      ppGroup (ppIndent (ppConcat [
        ppString " is",
        ppBreak,
        ppGroup (ppConcat [
          (case tyVars of
             | [] -> ppNil
             | _ -> 
                ppConcat [
                  ppString "[",
                  ppSep (ppString ",") (map ppString tyVars),
                  ppString "] "
                ]),
          ppString " ",
          ppATerm term
        ])
      ]))
    ]

  op ppPropertyType : PropertyType -> Pretty
  def ppPropertyType propType =
    case propType of
      | Axiom      -> ppString "axiom"
      | Theorem    -> ppString "theorem"
      | Conjecture -> ppString "conjecture"
      | any ->
           fail ("No match in ppPropertyType with: '"
              ^ (anyToString any)
              ^ "'")
}
\end{spec}
