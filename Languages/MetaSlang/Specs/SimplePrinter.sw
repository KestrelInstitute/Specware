\section{Simple MetaSlang Pretty Printer}

A simple pretty printer for MetaSlang.

\begin{spec}
SpecCalc qualifying spec 
{
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
   let 
     def doSortInfo sortInfo = ppConcat [ppString "type ", ppASortInfo sortInfo]
     def doOpInfo   opInfo   = ppConcat [ppString "op ",   ppAOpInfo   opInfo]
   in
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
           map (fn (specCalcTerm,spc) -> ppString ("import " ^ (showTerm specCalcTerm))) 
	       spc.importInfo.imports 
       in
	 ppSep ppNewline ppNames 
   in
   % this assume that a name used to index into the sort map also appears
   % in the list of names for that sort.
   let 
     def doSortInfo sortInfo = ppConcat [ppString "type ", ppASortInfo sortInfo]
     def doOpInfo   opInfo   = ppConcat [ppString "op ",   ppAOpInfo   opInfo]
   in
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
	   ppConcat [ppString "{",
		     ppSep (ppString ",") (map ppQualifiedId info.names),
		     ppString "}"]
   in
   let 
      def ppTvs tvs =
	case tvs of
	  | [] -> ppNil
	  | [tv] -> ppString (" " ^ tv)
	  | _::_ ->
	    ppConcat [ppString " (",
		      ppSep (ppString ",") (map ppString tvs),
		      ppString ")"]
      def ppDef srt =
	let (tvs, srt) = unpackSort srt in
	ppConcat ([ppNames, ppTvs tvs]
		  ++
		  (case srt of
		     | Any _   -> []
		     | _       -> [ppString " = ", ppASort srt]))
   in
     case info.dfn of
       | And (srts, _) -> ppConcat [ppNewline, 
				    ppString " (* Warning: Multiple Sort Definitions for following sort *) ",
				    ppNewline, 
				    ppSep ppNewline (map ppDef srts)]
       | srt -> ppDef srt

  op ppAOpInfo : [a] AOpInfo a -> Pretty
 def ppAOpInfo info = 
   let ppNames =
       case info.names of
	 | [] -> fail "ppAOpInfo: empty name list in sort info"
	 | [name] -> ppQualifiedId name
	 | _      -> ppConcat [ppString "{",
			       ppSep (ppString ",") (map ppQualifiedId info.names),
			       ppString "}"]
   in
   let 
     def ppType srt =
       let (tvs, srt) = unpackSort srt in
       case (tvs, srt) of
	 | ([],srt) -> ppASort srt
	 | (tvs,srt) ->
	   ppConcat [ppString "[",
		     ppSep (ppString ",") (map ppString tvs),
		     ppString "] ",
		     ppASort srt]

     def ppDecl tm =
       let srt = termSort tm in
       ppGroup (ppConcat [ppString "op ", 
			  ppNames, 
			  ppString " : ", 
			  ppType srt])

     def ppDef tm =
       let (tvs, _, tm) = unpackTerm tm in
       ppGroup (ppConcat [ppString "def ",
			  case tvs of
			    | [] -> ppNil
			    | _  -> ppConcat [ppString "[",
					      ppSep (ppString ",") (map ppString tvs),
					      ppString "] "],
			  ppNames,
			  ppGroup (ppIndent (ppConcat [ppString " =",
						       ppBreak,
						       ppGroup (ppATerm tm)]))
			 ])
   in
   let (decls, defs) = opInfoDeclsAndDefs info in
   let ppDecls = map ppDecl decls in
   let ppDefs  = map ppDef  defs  in
   ppConcat (ppDecls ++ ppDefs)

  op ppAProperty : fa (a) AProperty a -> Pretty
 def ppAProperty (propType, name, tvs, term) =
   ppConcat [
     ppPropertyType propType,
     ppString " ",
     ppQualifiedId name,
     ppGroup (ppIndent (ppConcat [
       ppString " is",
       ppBreak,
       ppGroup (ppConcat [
         (case tvs of
	    | [] -> ppNil
	    | _ -> 
	      ppConcat [ppString "[",
			ppSep (ppString ",") (map ppString tvs),
			ppString "] "]),
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
