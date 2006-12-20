(* Simple MetaSlang Pretty Printer *)

SpecCalc qualifying spec 

 import ../AbstractSyntax/SimplePrinter
 import AnnSpec

 %  sort ASpec b = 
 %   {
 %    importInfo   : ImportInfo,       %  not used in equality test on specs
 %    sorts        : ASortMap    b,
 %    ops          : AOpMap      b,
 %    properties   : AProperties b
 %   }

 %% called via ppObj attribute in specCat
 %% (see /Languages/MetaSlang/Specs/Categories/AsRecord.sw)
  op ppASpec : Spec -> Pretty
 def ppASpec (spc as {sorts,ops,elements,qualifier}) = 
   let 
     def lookupSort(Qualified(q,id)) =
       case findAQualifierMap(sorts,q,id) of
	 | Some v -> v
     def lookupOp(Qualified(q,id)) =
       case findAQualifierMap(ops,q,id) of
	 | Some v -> v
     def ppAOp qId = ppAOpInfo (lookupOp qId)
     def ppASort qId = ppASortInfo (lookupSort qId)
     def ppComment str = 
       if exists (fn chr -> chr = #\n) str then
	 ppConcat [ppString "(*", ppString str, ppString "*)"]
       else
	 ppString (";; " ^ str)	
     def ppElements elts =
       foldr (fn (el,result) ->
	      case el of
		| Property prop          -> Cons (ppAProperty prop, result)
		| Op       (qId,def?)    -> Cons (ppAOp qId,        result) % Currently does def as well  % TODO: discriminate decl-with-def from decl then def
		| OpDef    qId           -> result                          % Cons(ppAOpDef   qId,result)
		| Sort     qId           -> Cons (ppASort qId,      result)
		| SortDef  qId           -> result                          % Cons(ppASortDef qId,result)
		| Comment  str           -> Cons (ppComment str,    result)
		| Import   (_,_,impElts) -> (ppElements impElts) ++ result)
	 [] elts
  in
     
     ppConcat [ppString "spec ",
	       ppIndent (ppSep ppNewline (ppElements elements)),
	       ppBreak,
	       ppString "endspec"
	      ]

 %% not called by Specware per se (see PSL)
  op ppASpecLocal : Spec -> Pretty
 def ppASpecLocal (spc as {sorts,ops,elements,qualifier}) = 
   let 
     def lookupSort(Qualified(q,id)) =
       case findAQualifierMap(sorts,q,id) of
	 | Some v -> v
     def lookupOp(Qualified(q,id)) =
       case findAQualifierMap(ops,q,id) of
	 | Some v -> v
     def ppAOp qId = ppAOpInfo (lookupOp qId)
     def ppASort qId = ppASortInfo (lookupSort qId)
     def ppComment str = 
       if exists (fn chr -> chr = #\n) str then
	 ppConcat [ppString "(*", ppString str, ppString "*)"]
       else
	 ppString (";; " ^ str)	
     def ppElements elts =
       foldr (fn (el,result) ->
	      case el of
		| Property prop               -> Cons (ppAProperty prop, result)
		| Op       (qId,def?)         -> Cons (ppAOp       qId,  result) % Currently does def as well
		| OpDef    qId                -> result                          % Cons(ppAOpDef qId,result)
		| Sort     qId                -> Cons (ppASort     qId,  result)
		| SortDef  qId                -> result                          % Cons(ppASortDef qId,result)
		| Comment  str                -> Cons (ppComment   str,  result)
		| Import   (specCalcTerm,_,_) -> Cons (ppString("import " ^ (showTerm specCalcTerm)), result))
	 [] elts
  in
     
     ppConcat [ppString "spec ",
	       ppIndent (ppSep ppNewline (ppElements elements)),
	       ppString "endspec"
	      ]


 %% Other than from this file, called only from /Languages/SpecCalculus/Semantics/Evaluate/Spec/CompressSpec (and see PSL)
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
      def ppDecl srt =
	let (tvs, srt) = unpackSort srt in
	ppConcat [ppString " type ", ppNames, ppTvs tvs]

      def ppDef srt =
	let (tvs, srt) = unpackSort srt in
	ppConcat [ppString " type ", ppNames, ppTvs tvs, ppString " = ", ppASort srt]
   in
   let (decls, defs) = sortInfoDeclsAndDefs info in
   let ppDecls =
       case decls of
	 | []    -> []
	 | [srt] -> [ppDecl srt]
	 | _     -> [ppNewline, 
		     ppString " (* Warning: Multiple declarations for following type *) ",
		     ppNewline, 
		     ppSep ppNewline (map ppDecl decls)]
   in
   let ppDefs =
       case defs of
	 | []    -> []
	 | [srt] -> [ppDef srt]
	 | _     -> [ppNewline, 
		     ppString " (* Warning: Multiple definitions for following type *) ",
		     ppNewline, 
		     ppSep ppNewline (map ppDef defs)]
   in
     ppConcat (ppDecls ++ ppDefs)

 %% Other than from this file, called only from /Languages/SpecCalculus/Semantics/Evaluate/Spec/CompressSpec (and see PSL)
  op ppAOpInfo : [a] AOpInfo a -> Pretty
 def ppAOpInfo info = ppAOpInfoAux (" op  ", info)

  op ppAOpInfoAux : [a] String * AOpInfo a -> Pretty
 def ppAOpInfoAux (decl_keyword, info) = 
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
       ppGroup (ppConcat [ppString decl_keyword, % " op ", " var ", etc.
			  ppNames, 
			  ppString " : ", 
			  ppType srt])

     def ppDef tm =
       let (tvs, _, tm) = unpackTerm tm in
       ppGroup (ppConcat [ppString " def ",
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
   let decls = 
       %% make sure at least one "op ..." form is printed, to establish the type of the op
       case (decls, defs) of
	 | ([], dfn :: _) -> [dfn]
	 | _ -> decls
   in
   let ppWarnings = 
       case (decls,defs) of
	 | (_ :: _ :: _, _ :: _ :: _) -> [ppNewline, 
					  ppString " (* Warning: Multiple declarations and definitions for following op *) ",
					  ppNewline]
	 | (_ :: _ :: _, _)           -> [ppNewline, 
					  ppString " (* Warning: Multiple declarations for following op *) ",
					  ppNewline]
	 | (_,           _ :: _ :: _) -> [ppNewline, 
					  ppString " (* Warning: Multiple definitions for following op *) ",
					  ppNewline]
	 | _ -> []
   in
   let ppDecls =
       case decls of
	 | []   -> []
	 | [tm] -> [ppDecl tm]
	 | _    -> [ppSep ppNewline (map ppDecl decls)]
   in
   let ppDefs =
       case defs of
	 | []   -> []
	 | [tm] -> [ppDef tm]
	 | _    -> [ppSep ppNewline (map ppDef defs)]
   in
     ppConcat (ppWarnings ++ ppDecls ++ [ppNewline] ++ ppDefs)

 %% other than from here, called from /Languages/SpecCalculus/AbstractSyntax/Printer.sw
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
     | mystery ->
       fail ("No match in ppPropertyType with mysterious property: '" ^ (anyToString mystery) ^ "'")
endspec
