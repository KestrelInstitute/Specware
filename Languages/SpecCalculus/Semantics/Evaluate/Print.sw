(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecCalc qualifying spec {
  import Signature 
  import UnitId/Utilities
 %import /Languages/MetaSlang/Specs/SubtractSpec

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
 % type ValueInfo = Value * TimeStamp * UnitId_Dependency
 % type GlobalContext = PolyMap.Map (UnitId, ValueInfo)
 % type LocalContext  = PolyMap.Map (RelativeUID, ValueInfo)
 % type State = GlobalContext * LocalContext * Option UnitId * ValidatedUIDs

 % These may be used in various places throughout this file:
 %  uidToString          produces (unparseable) UnitId's that are relative to the root of the OS, using ~ for home,    e.g. "~/foo"
 %  relativeUID_ToString produces (parseable?)  UnitId's that are relativized to the currentUID, using ".." to ascend, e.g. "foo" or "../../foo"
       
 type ReverseContext = PolyMap.Map (Value, RelativeUID)

 def printSpecExpanded? = false

 % from show, showx:
 def SpecCalc.evaluatePrint (term,useXSymbol?) = {
   (value, time_stamp, depUnitIds) <- SpecCalc.evaluateTermInfo term;
   (optBaseUnitId,base_spec)     <- getBase;
   global_context                <- getGlobalContext;   
   currentUnitId                 <- getCurrentUnitId;
   reverse_context <- return (foldr (fn (unitId, value_to_uid_map) -> 
				     update value_to_uid_map
                                            ((eval global_context unitId).1) 
				            (relativizeUID currentUnitId unitId))
			            emptyMap
				    depUnitIds);
   SpecCalc.print "\n";
   (case value of
      | Spec    spc ->
        SpecCalc.print (if printSpecExpanded?
			  then printSpecExpanded base_spec spc
			  else
			    if useXSymbol?
			      then printSpecXSymbol base_spec reverse_context spc
			      else printSpec base_spec reverse_context spc)
      | Morph      sm    -> SpecCalc.print (printMorphism base_spec reverse_context sm)
      | Diag       dg    -> SpecCalc.print (printDiagram  base_spec reverse_context dg)
      | Colimit    col   -> SpecCalc.print (printColimit  base_spec reverse_context col)
      | Proof _          -> SpecCalc.print ""
      | SpecPrism  sp    -> SpecCalc.print (printPrism  base_spec reverse_context sp)  % tentative
      | SpecInterp si    -> SpecCalc.print (printInterp base_spec reverse_context si)  % tentative
      | Other      other -> evaluateOtherPrint other (positionOf term)
      | InProcess  _     -> SpecCalc.print "No value!");
   SpecCalc.print "\n";
   return (value, time_stamp, depUnitIds)
   }

 op printSpec     : Spec -> ReverseContext -> Spec              -> String
 op printMorphism : Spec -> ReverseContext -> Morphism          -> String
 op printDiagram  : Spec -> ReverseContext -> SpecDiagram       -> String
 op printColimit  : Spec -> ReverseContext -> SpecInitialCocone -> String
 op printPrism    : Spec -> ReverseContext -> SpecPrism         -> String  % tentative
 op printInterp   : Spec -> ReverseContext -> SpecInterp        -> String  % tentative

 %% ======================================================================
 %% Spec
 %% ======================================================================

  op printWidth: Nat = 110

  %The following loses too much information
  def printSpec base_spec _(*reverse_context*) spc =
    %% this uses /Languages/MetaSlang/Specs/Printer
    %% which uses /Library/PrettyPrinter/BjornerEspinosa
    %% TODO: use reverse_context ?
    PrettyPrint.toString (format(printWidth, 
                                 ppSpecHidingImportedStuff
                                   (initialize(asciiPrinter,false))
                                   base_spec
                                   spc))

  def printSpecXSymbol base_spec _(*reverse_context*) spc =
    %% this uses /Languages/MetaSlang/Specs/Printer
    %% which uses /Library/PrettyPrinter/BjornerEspinosa
    %% TODO: use reverse_context ?
    PrettyPrint.toString (format(printWidth, 
                                 ppSpecHidingImportedStuff
                                   (initialize(XSymbolPrinter,false))
                                   base_spec
                                   spc))


 % from show, showx:
 def AnnSpecPrinter.printSpecExpanded base_spec (*reverse_context*) spc =
   %% TODO: use reverse_context for imports ?
   AnnSpecPrinter.printSpecFlat spc

 %% This wants to live in /Languages/MetaSlang/Specs/Printer.sw,
 %% but SpecCalc.Term is merely declared (not defined) there,
 %% so the case dispatch won't typecheck.  Sigh.
 def AnnSpecPrinter.ppImportTerm context import_directions im_sp_tm =
   case im_sp_tm of
     | (Quote (Spec spc, _, _), _) ->
        AnnSpecPrinter.ppImportedSpec context spc import_directions 
     | _ ->
       string (indentString "  " (showSCTerm im_sp_tm))

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
   ppFormat (ppMorphismX base_spec reverse_context sm)

 %% Not to be confused with ppMorphism in /Languages/MetaSlang/Specs/Categories/AsRecord.sw (sigh)
 def ppMorphismX base_spec reverse_context sm =
   %% Use of str_1 is a bit of a hack to get the effect that
   %% dom/cod specs are grouped on one line if possible,
   %% and they either follow "morphism" on the first line 
   %% (with map on same line or indented on next line),
   %% or are by themselves, indented, on the second line,
   %% with the map indented starting on the third line.
   let prefix =
       case sm.sm_tm of
	| Some (SpecMorph (dom_tm, cod_tm, _, _), _) ->
	  (ppGroup 
	    (ppConcat 
	      [ppString "morphism ",
	       ppString (showSCTerm dom_tm),
	       ppString " -> ",
	       ppString (showSCTerm cod_tm)
	      ]))
	| _ ->
	  let dom_spec = dom sm in
	  let cod_spec = cod sm in
	  (ppGroup 
	    (ppConcat 
	      [ppString "morphism",
	       ppNest 4 (ppGroup
			  (ppConcat 
			    [ppBreak, 
			     ppString (case evalPartial reverse_context (Spec dom_spec) of
					 | Some rel_uid -> relativeUID_ToString rel_uid  
					 | None         -> printSpec base_spec reverse_context dom_spec),
			     % ppBreak, % too many newlines!
			     ppString " -> ",
			     % ppBreak, % too many newlines!
			     ppString (case evalPartial reverse_context (Spec cod_spec) of
					 | Some rel_uid -> relativeUID_ToString rel_uid  
					 | None         -> printSpec base_spec reverse_context cod_spec)
			    ]))
	      ]))
   in
     ppGroup 
      (ppConcat 
        [prefix,
	 ppNest 1 (ppConcat [ppBreak,
			     ppMorphismMap     sm,
			     ppMorphismPragmas sm])
	])


  %% inspired by ppMorphMap from /Languages/MetaSlang/Specs/Categories/AsRecord.sw,
  %%  but substantially different
  op ppMorphismMap : Morphism -> Doc
  def ppMorphismMap {dom=_, cod=_, typeMap, opMap, pragmas=_, sm_tm=_} =
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
					  % ppBreak, % too many newlines!
					  ppString " +-> ",
					  % ppBreak, % too many newlines!
					  ppQualifiedId cod]), 
		       lst))
                [] 
		(abbrevMap map)
    in
      ppConcat
        (case (ppAbbrevMap "type " typeMap) ++ (ppAbbrevMap "op " opMap) of
	   | []         -> [ppString " {} "]
	   | abbrev_map -> [ppString " {",
			    ppNest 1 (ppSep (ppCons (ppString ",") ppBreak) abbrev_map),
			    ppString "} "])


  op  ppMorphismPragmas : Morphism -> Doc
  def ppMorphismPragmas sm =
    case sm.pragmas of
      | [] -> ppNil
      | _ -> 
        ppGroup (ppConcat [ppBreak,
			   ppSep ppBreak
			         (map (fn  ((prefix, body, postfix), _) ->
				       ppString (prefix ^ body ^ postfix))
				      sm.pragmas)])


 %% ======================================================================
 %% Diagram
 %% ======================================================================

 def printDiagram base_spec reverse_context dg =
   %% this uses /Library/Structures/Data/Categories/Diagrams/Polymorphic
   %% which uses /Library/PrettyPrinter/WadlerLindig

   let shape       = shape    dg    in
   let vertice_set = vertices shape in
   let edge_set    = edges    shape in
   let src_map     = src      shape in
   let target_map  = target   shape in

   let functor     = functor   dg      in
   let vertex_map  = vertexMap functor in
   let edge_map    = edgeMap   functor in

   %% warning: vertex.difference (based on sets) is not defined!
   %%  so we use lists instead for linked_vertices and isolated_vertices
   let linked_vertices = 
       fold (fn linked_vertices -> fn edge -> 
	     let src = eval src_map    edge in
	     let tgt = eval target_map edge in
	     %% simpler and faster to allow duplicates
	     Cons (src, Cons (tgt, linked_vertices)))
            []
	    edge_set
   in
   let isolated_vertices =  
       fold (fn isolated_vertices -> fn vertice ->
	     if  vertice in? linked_vertices then
	       isolated_vertices
	     else
	       Cons (vertice, isolated_vertices))
            []
	    vertice_set
   in
   let pp_vertice_entries = 
       foldl (fn (pp_entries,vertex) -> 
	      Cons (ppGroup 
		    (ppConcat 
		     [ppElem vertex, 
		      % ppBreak, % way too many newlines!
		      ppString " +-> ",
		      % ppBreak, % way too many newlines!
		      let spc = eval vertex_map vertex in
		      ppString (case evalPartial reverse_context (Spec spc) of
				  | Some rel_uid -> relativeUID_ToString rel_uid  
				  | None         -> printSpec base_spec reverse_context spc)]),
		    pp_entries))
             []
	     isolated_vertices
   in
   let pp_edge_entries = 
       fold (fn pp_entries -> fn edge -> 
	     Cons (ppGroup 
		    (ppConcat 
 		      [ppGroup 
		        (ppConcat 
			  [ppElem edge,
			   % ppBreak, % way too many newlines!
			   ppString " : ",
			   % ppBreak, % way too many newlines!
			   ppElem (eval src_map edge),
			   % ppBreak, % too many newlines!
			   ppString " -> ",
			   % ppBreak, % way too many newlines!
			   ppElem (eval target_map edge)]),
			ppBreak, 
			ppString " +-> ",
			ppBreak, 
			let sm = eval edge_map edge in
			case evalPartial reverse_context (Morph sm) of
			  | Some rel_uid -> ppString (relativeUID_ToString rel_uid)  
			  | None         -> ppMorphismX base_spec reverse_context sm]),
		   pp_entries))
            []
            edge_set
   in 
   ppFormat 
     (ppGroup 
       (ppConcat [ppString "diagram {",
		  ppNest 9 (ppSep (ppCons (ppString ",") ppBreak) (pp_vertice_entries ++ pp_edge_entries)),
		  ppString "} "]))

   %% ppFormat (ppDiagram
   %%	     (mapDiagram dg 
   %%	      (fn obj -> subtractSpec obj base_spec) 
   %%	      (fn arr -> arr)))

 %% ======================================================================
 %% Colimit
 %% ======================================================================

 def printColimit base_spec reverse_context col =
   %% Just print the spec at the apex of the colimit.
   printSpec base_spec reverse_context (Cat.apex (Cat.cocone col))

   %%% was:
   %%%  %% ppColimit uses /Languages/MetaSlang/Specs/Categories/AsRecord
   %%%  %% which uses /Library/PrettyPrinter/WadlerLindig
   %%%  %% ppFormat  (ppColimit col)
   %%%  let apex_spec = Cat.apex (Cat.cocone col) in
   %%%  %% Note: localTypes and localOps in apex_spec will both be empty,
   %%%  %%       so whether or not it makes sense, we must work around this fact.
   %%%  let trimmed_apex_spec = subtractSpec apex_spec base_spec in
   %%%  AnnSpecPrinter.printSpec trimmed_apex_spec

 %% ======================================================================
 %% Tentative Prism-related stuff
 %% ======================================================================

 (* Tentative *)
 def printPrism base_spec reverse_context sp = 
   let prefix =
       let sm = head sp.sms in
       case sm.sm_tm of
	| Some (SpecMorph (dom_tm, cod_tm, _, _), _) ->
	  (ppGroup 
	    (ppConcat 
	      [ppString "prism ",
	       ppString (showSCTerm dom_tm),
	       ppString " -> "
	      ]))
	| _ ->
	  let dom_spec = dom sm in
	  (ppGroup 
	    (ppConcat 
	      [ppString "prism",
	       ppNest 4 (ppGroup
			  (ppConcat 
			    [ppBreak, 
			     ppString (case evalPartial reverse_context (Spec dom_spec) of
					 | Some rel_uid -> relativeUID_ToString rel_uid  
					 | None         -> printSpec base_spec reverse_context dom_spec),
			     % ppBreak, % too many newlines!
			     ppString " -> "
			    ]))
	      ]))
   in
   let sms =
       foldl (fn (cod_strs,sm) ->
	      let doc = ppConcat [ppBreak,
				  ppMorphismX base_spec reverse_context sm]
	      in
	      case cod_strs of
		| [_] -> cod_strs ++ [doc]
		| _ -> cod_strs ++ [ppString ", ", doc])
             [ppString " {"]
	     sp.sms
   in
   let sms = ppConcat (sms ++ [ppBreak, ppString "} "]) in
   ppFormat (ppGroup 
	     (ppConcat 
	      [prefix,
	       sms
	       % ppNest 1 (ppConcat [ppBreak (* (ppMorphismMap sm) *) ])
	      ]))


 (* Tentative *)
 def printInterp base_spec reverse_context si = 
   let 
     def pp_spec sp =
       case evalPartial reverse_context (Spec sp) of
	 | Some rel_uid -> relativeUID_ToString rel_uid  
	 | None         -> printSpec base_spec reverse_context sp
   in
   let dom_str = pp_spec si.dom in
   let med_str = pp_spec si.med in
   let cod_str = pp_spec si.cod in
   ppFormat (ppGroup
	     (ppConcat
	      [ppString "interp ",
	       ppString dom_str,
	       ppString " -> ",
	       ppString cod_str,
	       ppString " {",
	       ppMorphismX base_spec reverse_context si.d2m,
	       ppString " -> ",
	       ppString med_str,
	       ppString " <- ",
	       ppMorphismX base_spec reverse_context si.c2m,
	       ppString "} "]))

}
