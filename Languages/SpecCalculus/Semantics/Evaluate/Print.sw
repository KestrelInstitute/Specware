SpecCalc qualifying spec {
  import Signature 
  import URI/Utilities

 % This implements the "print" command, which evaluates its argument and 
 %  returns that value, with the side effect of printing the value.  
 % This strategy makes it cognizant of the results of type-checking, 
 %  overload resolution, colimit/translate computations, etc., which
 %  presumably is valuable information for a confused user, or a user
 %  exploring a new and unfamiliar system.
 %
 % Exactly how deeply recursively it should print is an open question.
 % Perhaps it should accept parameters to control that.
 %
 % An alternative strategy would be to simply call ppTerm on the argument,
 %  then evaluate that term and return its value.  That would simply echo
 %  back essentially the same term that was parsed, which makes it much
 %  simpler but also probably less useful.
 % ppTerm, the printer for a SpecCalculus Term, is in 
 %  /Languages/SpecCalculus/AbstractSyntax/Printer.sw

 % from Environment.sw :
 % sort ValueInfo = Value * TimeStamp * URI_Dependency
 % sort GlobalContext = PolyMap.Map (URI, ValueInfo)
 % sort LocalContext  = PolyMap.Map (RelativeURI, ValueInfo)
 % sort State = GlobalContext * LocalContext * Option URI * ValidatedURIs

 sort ReverseContext = PolyMap.Map (Value, RelativeURI)

 def SpecCalc.evaluatePrint term = {
   (value, time_stamp, dep_URIs) <- SpecCalc.evaluateTermInfo term;
   base_URI                      <- pathToRelativeURI "/Library/Base";
   (Spec base_spec, _, _)        <- SpecCalc.evaluateURI (Internal "base") base_URI;
   global_context                <- getGlobalContext;   
   current_URI                   <- getCurrentURI;
   reverse_context <- return (foldr (fn (uri, value_to_uri_map) -> 
				     update value_to_uri_map
                                            ((eval global_context uri).1) 
				            (relativizeURI current_URI uri))
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

 %% ======================================================================
 %% Spec
 %% ======================================================================

 def printSpec base_spec reverse_context spc =
   %% this uses /Languages/MetaSlang/Specs/Printer
   %% which uses /Library/PrettyPrinter/BjornerEspinosa
   AnnSpecPrinter.printSpec (subtractSpec spc base_spec)

 %% ======================================================================
 %% Morphism
 %% ======================================================================

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
	  ppString "morphism",
	  ppNest 4
 	   (ppConcat 
	     [ppBreak,
	      ppGroup
	        (ppConcat 
		  [ppString (case evalPartial reverse_context (Spec dom_spec) of
			       | Some rel_uri -> relativeURI_ToString rel_uri  
			       | None         -> printSpec base_spec reverse_context dom_spec),
		   ppBreak,
		   ppString "->",
		   ppBreak,
		   ppString (case evalPartial reverse_context (Spec cod_spec) of
			       | Some rel_uri -> relativeURI_ToString rel_uri  
			       | None         -> printSpec base_spec reverse_context cod_spec)]),
	      ppBreak,
	      ppMorphismMap sm,
	      ppBreak])]))
	 

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
		 Cons (ppGroup (ppConcat [ppString keyword,				    
					  ppQualifiedId dom,
					  ppBreak,
					  ppString "+->",
					  ppBreak,
					  ppQualifiedId cod]), 
		       lst))
                [] 
		(abbrevMap map)
    in
      case (ppAbbrevMap "sort " sortMap) ++ (ppAbbrevMap "op " opMap) of
	| [] -> ppString "{}"
	| abbrev_map -> ppGroup (ppConcat [ppString "{",
					   ppNest 1 (ppSep (ppCons (ppString ",") ppBreak) abbrev_map),
					   ppString "}"])


 %% ======================================================================
 %% Diagram
 %% ======================================================================

 def printDiagram base_spec reverse_context dg =
   %% this uses /Library/Structures/Data/Categories/Diagrams/Polymorphic
   %% which uses /Library/PrettyPrinter/WadlerLindig
   ppFormat (ppDiagram
	     (mapDiagram dg 
	      (fn obj -> subtractSpec obj base_spec) 
	      (fn arr -> arr)))

 %% ======================================================================
 %% Colimit
 %% ======================================================================

 def printColimit base reverse_context col =
   %% this uses /Languages/MetaSlang/Specs/Categories/AsRecord
   %% which uses /Library/PrettyPrinter/WadlerLindig
   ppFormat  (ppColimit col)

}
