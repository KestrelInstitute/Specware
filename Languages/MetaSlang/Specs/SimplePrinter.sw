(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(* Simple MetaSlang Pretty Printer *)

SpecCalc qualifying spec 

 import ../AbstractSyntax/SimplePrinter
 import AnnSpec

 %  type ASpec b = 
 %   {
 %    importInfo   : ImportInfo,       %  not used in equality test on specs
 %    types        : ATypeMap    b,
 %    ops          : AOpMap      b,
 %    properties   : AProperties b
 %   }

 %% called via ppObj attribute in specCat
 %% (see /Languages/MetaSlang/Specs/Categories/AsRecord.sw)
  op ppASpec : Spec -> WLPretty
 def ppASpec spc =
   let 
     def lookupType(Qualified(q,id)) =
       case findAQualifierMap(spc.types,q,id) of
	 | Some v -> v
     def lookupOp(Qualified(q,id)) =
       case findAQualifierMap(spc.ops,q,id) of
	 | Some v -> v
     def ppAOp qId = ppAOpInfo (lookupOp qId)
     def ppAType qId = ppATypeInfo (lookupType qId)
     def ppComment str = 
       if exists? (fn chr -> chr = #\n) str then
	 ppConcat [ppString "(*", ppString str, ppString "*)"]
       else
	 ppString (";; " ^ str)	
     def ppElements elts =
       foldr (fn (el,result) ->
	      case el of
		| Property prop            -> Cons (ppAProperty prop, result)
		| Op       (qId,def?,_)    -> Cons (ppAOp qId,        result) % Currently does def as well  % TODO: discriminate decl-with-def from decl then def
		| OpDef    (qId,_,_,_)       -> result                          % Cons(ppAOpDef   qId,result)
		| Type     (qId,_)         -> Cons (ppAType qId,      result)
		| TypeDef  (qId,_)         -> result                          % Cons(ppATypeDef qId,result)
		| Comment  (str,_)         -> Cons (ppComment str,    result)
		| Import   (_,_,impElts,_) -> (ppElements impElts) ++ result)
	 [] elts
  in
     
     ppConcat [ppString "spec ",
	       ppIndent (ppSep ppNewline (ppElements spc.elements)),
	       ppBreak,
	       ppString "endspec"
	      ]

 %% not called by Specware per se (see PSL)
  op ppASpecLocal : Spec -> WLPretty
 def ppASpecLocal spc =
   let 
     def lookupType(Qualified(q,id)) =
       case findAQualifierMap(spc.types,q,id) of
	 | Some v -> v
     def lookupOp(Qualified(q,id)) =
       case findAQualifierMap(spc.ops,q,id) of
	 | Some v -> v
     def ppAOp qId = ppAOpInfo (lookupOp qId)
     def ppAType qId = ppATypeInfo (lookupType qId)
     def ppComment str = 
       if exists? (fn chr -> chr = #\n) str then
	 ppConcat [ppString "(*", ppString str, ppString "*)"]
       else
	 ppString (";; " ^ str)	
     def ppElements elts =
       foldr (fn (el,result) ->
	      case el of
		| Property prop                 -> Cons (ppAProperty prop, result)
		| Op       (qId,def?,_)         -> Cons (ppAOp       qId,  result) % Currently does def as well
		| OpDef    (qId,_,_,_)            -> result                          % Cons(ppAOpDef qId,result)
		| Type     (qId,_)              -> Cons (ppAType     qId,  result)
		| TypeDef  (qId,_)              -> result                          % Cons(ppATypeDef qId,result)
		| Comment  (str,_)              -> Cons (ppComment   str,  result)
		| Import   (specCalcTerm,_,_,_) -> Cons (ppString("import " ^ (showSCTerm specCalcTerm)), result))
	 [] elts
  in
     
     ppConcat [ppString "spec ",
	       ppIndent (ppSep ppNewline (ppElements spc.elements)),
	       ppString "endspec"
	      ]


 %% Other than from this file, called only from /Languages/SpecCalculus/Semantics/Evaluate/Spec/CompressSpec (and see PSL)
  op ppATypeInfo : [a] ATypeInfo a -> WLPretty
 def ppATypeInfo info =
   let ppNames =
       case info.names of
	 | [] -> fail "ppATypeInfo: empty name list in type info"
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
	let (tvs, srt) = unpackType srt in
	ppConcat [ppString " type ", ppNames, ppTvs tvs]

      def ppDef srt =
	let (tvs, srt) = unpackType srt in
	ppConcat [ppString " type ", ppNames, ppTvs tvs, ppString " = ", ppAType srt]
   in
   let (decls, defs) = typeInfoDeclsAndDefs info in
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
  op ppAOpInfo : [a] AOpInfo a -> WLPretty
 def ppAOpInfo info = ppAOpInfoAux (" op ", info)

  op ppAOpInfoAux : [a] String * AOpInfo a -> WLPretty
 def ppAOpInfoAux (decl_keyword, info) = 
   let ppNames =
       case info.names of
	 | [] -> fail "ppAOpInfo: empty name list in type info"
	 | [name] -> ppQualifiedId name
	 | _      -> ppConcat [ppString "{",
			       ppSep (ppString ",") (map ppQualifiedId info.names),
			       ppString "}"]
   in
   let 
     def ppType srt =
       let (tvs, srt) = unpackType srt in
       case (tvs, srt) of
	 | ([],srt) -> ppAType srt
	 | (tvs,srt) ->
	   ppConcat [ppString "[",
		     ppSep (ppString ",") (map ppString tvs),
		     ppString "] ",
		     ppAType srt]

     def ppDecl tm =
       let srt = termType tm in
       ppGroup (ppConcat [ppString decl_keyword, % " op ", " var ", etc.
			  ppNames, 
			  ppString " : ", 
			  ppType srt])

     def ppDef tm =
       let (tvs, _, tm) = unpackFirstTerm tm in
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
  op ppAProperty : [a] AProperty a -> WLPretty
 def ppAProperty (propType, name, tvs, term, _) =
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

  op ppPropertyType : PropertyType -> WLPretty
 def ppPropertyType propType =
   case propType of
     | Axiom      -> ppString "axiom"
     | Theorem    -> ppString "theorem"
     | Conjecture -> ppString "conjecture"
     | mystery ->
       fail ("No match in ppPropertyType with mysterious property: '" ^ (anyToString mystery) ^ "'")
endspec
