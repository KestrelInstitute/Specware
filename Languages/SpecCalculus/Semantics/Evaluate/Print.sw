SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities

 % from Environment.sw :
 % sort ValueInfo = Value * TimeStamp * URI_Dependency
 % sort GlobalContext = PolyMap.Map (URI, ValueInfo)
 % sort LocalContext  = PolyMap.Map (RelativeURI, ValueInfo)
 % sort State = GlobalContext * LocalContext * Option URI * ValidatedURIs

 sort ReverseContext = PolyMap.Map (Value, URI)

 def SpecCalc.evaluatePrint term = {
   (value, time_stamp, dep_URIs) <- SpecCalc.evaluateTermInfo term;
   base_URI                      <- pathToRelativeURI "/Library/Base";
   (Spec base_spec, _, _)        <- SpecCalc.evaluateURI (Internal "base") base_URI;
   global_context                <- getGlobalContext;   
   reverse_context <- return (foldr (fn (uri, dep_uri_to_value_map) -> 
				     update dep_uri_to_value_map ((eval global_context uri).1) uri)
			           emptyMap
				   dep_URIs);
   (case value of
      | Spec    spc -> SpecCalc.print (printSpec     base_spec reverse_context spc)
      | Morph   sm  -> SpecCalc.print (printMorphism base_spec reverse_context sm)
      | Diag    dg  -> SpecCalc.print (printDiagram  base_spec reverse_context dg)
      | Colimit col -> SpecCalc.print (printColimit  base_spec reverse_context col)
      | InProcess   -> SpecCalc.print "No value!");
   return (value, time_stamp, dep_URIs)
   }

 op printSpec     : Spec -> ReverseContext -> Spec              -> String
 op printMorphism : Spec -> ReverseContext -> Morphism          -> String
 op printDiagram  : Spec -> ReverseContext -> SpecDiagram       -> String
 op printColimit  : Spec -> ReverseContext -> SpecInitialCocone -> String

 def printSpec base_spec reverse_context spc =
   %% this uses /Languages/MetaSlang/Specs/Printer
   %% which uses /Library/PrettyPrinter/BjornerEspinosa
   AnnSpecPrinter.printSpec (subtractSpec spc base_spec)

 def printMorphism base_spec reverse_context sm =
   %% this uses /Languages/MetaSlang/Specs/Categories/AsRecord
   %% which uses /Library/PrettyPrinter/WadlerLindig
   %%
   %% Some possible formats this might generate:
   %%
   %%  A -> B {}
   %%
   %%  A -> B { ... }
   %%  
   %%  A -> B 
   %%   { ... }      
   %%  
   %%  A -> B 
   %%   {... 
   %%    ...
   %%    ...}
   %%  
   let dom_spec = dom sm in
   let cod_spec = cod sm in
   ppFormat 
     (ppGroup 
       (ppConcat 
	 [% TODO: uriToString may produce filenames that are reasonable to the OS but not readable by Specware, e.g. ~/foo.sw
	  %       Not clear yet what the right solution is.  [Maybe specware should parse ~/foo.sw !]
	  ppGroup (ppConcat [ppString "morphism ",
			     ppString (case evalPartial reverse_context (Spec dom_spec) of
					 | Some uri -> uriToString uri  
					 | None     -> printSpec base_spec reverse_context dom_spec),
			     ppBreak,
			     ppString "->",
			     ppBreak,
			     ppString (case evalPartial reverse_context (Spec cod_spec) of
					 | Some uri -> uriToString uri  
					 | None     -> printSpec base_spec reverse_context cod_spec)]),
	  ppMorphismMap sm]))
	 

  %% inspired by ppMorphMap from /Languages/MetaSlang/Specs/Categories/AsRecord.sw,
  %%  but substantially different
  op ppMorphismMap : Morphism -> Doc
  def ppMorphismMap {dom, cod, sortMap, opMap} =
    let 
      def abbrevMap map =
	foldMap (fn newMap -> fn d -> fn c ->
		 if d = c then
		   newMap
		 else
		   update newMap d c) 
	        emptyMap 
		map 
      def ppAbbrevMap keyword map =
	foldMap (fn lst -> fn dom -> fn cod ->
		 Cons (ppConcat [ppString keyword,				    
				 ppQualifiedId dom,
				 ppString " +-> ",
				 ppQualifiedId cod], 
		       lst))
                [] 
		(abbrevMap map)
    in
      case (ppAbbrevMap "sort " sortMap) ++ (ppAbbrevMap "op " opMap) of
	| [] -> ppString " {} "
	| abbrev_map -> ppGroup (ppConcat [ppBreak,
					   ppString "{",
					   ppIndent (ppSep (ppCons (ppString ",") ppBreak) abbrev_map),
					   ppString "}",
					   ppBreak])


 def printDiagram base_spec reverse_context dg =
   %% this uses /Library/Structures/Data/Categories/Diagrams/Polymorphic
   %% which uses /Library/PrettyPrinter/WadlerLindig
   ppFormat (ppDiagram
	     (mapDiagram dg 
	      (fn obj -> subtractSpec obj base_spec) 
	      (fn arr -> arr)))

 def printColimit base reverse_context col =
   %% this uses /Languages/MetaSlang/Specs/Categories/AsRecord
   %% which uses /Library/PrettyPrinter/WadlerLindig
   ppFormat  (ppColimit col)

}
