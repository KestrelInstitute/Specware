AnnSpec qualifying spec 

 import Position
 import MSTerm
 import QualifierMapAsSTHashTable
 import SpecCalc


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Note:  ASpec refers to ImportedSpecs, which refers to Spec, 
 %%        which is an instance of ASpec.

 %% StandardAnnotation is the annotation of fully resolved specs and terms
 %% i.e., sorts Spec, Term, Sort etc. Currently it is just Position,
 %% conceivably it could be more interesting in the future.

 % sort StandardAnnotation = Position	% was ()

 type Spec = ASpec StandardAnnotation

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ASpec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ASpec b = {importInfo   : ImportInfo,	% importInfo is ignored by equality test on specs
		 sorts        : ASortMap    b,
		 ops          : AOpMap      b,
		 properties   : AProperties b}

 type ImportInfo = {imports         : Imports,
		    localOps        : OpNames,
		    localSorts      : SortNames,
		    localProperties : PropertyNames}

 type Aliases = List QualifiedId 

   op someAliasIsLocal? : Aliases * List QualifiedId -> Boolean
  def someAliasIsLocal? (aliases, local_names) =
    exists (fn qid -> member (qid, local_names)) aliases 
    
 type Imports = List Import
 type Import  = (SpecCalc.Term Position) * Spec

 type ASortMap  b = AQualifierMap (ASortInfo b) % i.e., Qualifier -> Id -> info
 type AOpMap    b = AQualifierMap (AOpInfo   b) % i.e., Qualifier -> Id -> info

 type ASortInfo b = SortNames * TyVars * ASortSchemes b 
 type SortNames   = Aliases

 type AOpInfo   b = OpNames * Fixity * ASortScheme b * ATermSchemes b 
 type OpNames     = Aliases

 type AProperties   b  = List (AProperty b) 
 type AProperty     b  = PropertyType * PropertyName * TyVars * ATerm b
 type PropertyType     = | Axiom | Theorem | Conjecture
 type PropertyName     = QualifiedId
 type PropertyNames    = List PropertyName  

 op  propertyName: fa(b) AProperty b -> PropertyName
 def propertyName p = p.2
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 type ASpecs b = List (ASpec b)

 type AOpSignature  b = String * String * TyVars * ASort b
 type SortSignature   = String * String * TyVars 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 op mapSpec    : fa(b) TSP_Maps b -> ASpec b -> ASpec b

 def mapSpec tsp_maps {importInfo, sorts, ops, properties} =
   {
    importInfo       = importInfo,
    sorts            = mapSpecSorts      tsp_maps sorts,
    ops              = mapSpecOps        tsp_maps ops,
    properties       = mapSpecProperties tsp_maps properties
   }

  op mapSpecSorts: fa(b) TSP_Maps b -> ASortMap b -> ASortMap b 
 def mapSpecSorts tsp_maps sorts =
   mapSortInfos (fn (aliases, tvs, defs) ->
		 (aliases, tvs, mapSortSchemes tsp_maps defs))
                sorts

  op mapSpecOps : fa(b) TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOps tsp_maps ops =
   mapOpInfos (fn (aliases, fixity, (tvs, srt), defs) ->
	       (aliases, 
		fixity, 
		(tvs, mapSort tsp_maps srt), 
		mapTermSchemes tsp_maps defs))
              ops

 %% mapSortInfos and mapOpInfos apply the provided function
 %% just once to an info, even if it has multiple aliases,
 %% then arrange for each alias to index that same new info.

  op mapSortInfos : fa(b) (ASortInfo b -> ASortInfo b) -> ASortMap b -> ASortMap b 
 def mapSortInfos sortinfo_map sorts =
   foldriAQualifierMap 
     (fn (index_q, index_id, sort_info as (aliases,_,_), new_map) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	%% When access is via a primary alias, update the info and
	%% record that (identical) new value for all the aliases.
	let new_info = sortinfo_map sort_info in
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, new_info))				   
	      new_map
	      aliases
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     emptyAQualifierMap
     sorts

  op mapOpInfos : fa(b) (AOpInfo b -> AOpInfo b) -> AOpMap b -> AOpMap b 
 def mapOpInfos opinfo_map ops =
   foldriAQualifierMap 
     (fn (index_q, index_id, op_info as (aliases,_,_,_), new_map) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	%% When access is via a primary alias, update the info and 
	%% ecord that (identical) new value for all the aliases.
	let new_info = opinfo_map op_info in
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, new_info))				   
	      new_map
	      aliases
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     emptyAQualifierMap
     ops

  op filterSortMap : fa(b) (ASortInfo b -> Boolean) -> ASortMap b -> ASortMap b 
 def filterSortMap keep? sorts =
   foldriAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_), new_map) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id && keep? info then
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, info))				   
	      new_map
	      aliases
      else
	new_map)
     emptyAQualifierMap
     sorts

  op filterOpMap : fa(b) (AOpInfo b -> Boolean) -> AOpMap b -> AOpMap b 
 def filterOpMap keep? ops =
   foldriAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_,_), new_map) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id && keep? info then
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, info))				   
	      new_map
	      aliases
      else
	new_map)
     emptyAQualifierMap
     ops

  op foldSortInfos : fa(a,b) (ASortInfo a * b -> b) -> b -> ASortMap a -> b
 def foldSortInfos f init sorts =
   foldriAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_), result) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	f (info, result)
      else
	result)
     init
     sorts

  op foldOpInfos : fa(a,b) (AOpInfo a * b -> b) -> b -> AOpMap a -> b
 def foldOpInfos f init ops =
   foldriAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_,_), result) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	f (info, result)
      else
	result)
     init
     ops

  op appSortInfos : fa(b) (ASortInfo b -> ()) -> ASortMap b -> ()
 def appSortInfos f sorts =
   appiAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_)) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	f info
      else
	())
     sorts

  op appOpInfos : fa(b) (AOpInfo b -> ()) -> AOpMap b -> ()
 def appOpInfos f ops =
   appiAQualifierMap 
     (fn (index_q, index_id, info as (aliases,_,_,_)) ->
      let (Qualified (q, id)) :: _ = aliases in
      if index_q = q && index_id = id then
	f info
      else
	())
     ops


  op mapSpecProperties : fa(b) TSP_Maps b -> AProperties b ->  AProperties b 
 def mapSpecProperties tsp_maps properties =
   map (fn (pt, nm, tvs, term) -> 
           (pt, nm, tvs, mapTerm tsp_maps term))
       properties

 op mapTermSchemes : fa(b) TSP_Maps b -> ATermSchemes b -> ATermSchemes b
 op mapSortSchemes : fa(b) TSP_Maps b -> ASortSchemes b -> ASortSchemes b

 def mapTermSchemes tsp_maps term_schemes = 
  map (fn (type_vars, term) -> (type_vars, mapTerm tsp_maps term)) term_schemes

 def mapSortSchemes tsp_maps sort_schemes =
  map (fn (type_vars, srt) -> (type_vars, mapSort tsp_maps srt)) sort_schemes

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

  op appSpec    : fa(a) appTSP a -> ASpec a    -> ()
 def appSpec tsp_apps spc = 
   (
    appSpecOps        tsp_apps spc.ops;
    appSpecSorts      tsp_apps spc.sorts; 
    appSpecProperties tsp_apps spc.properties
   )

  op appSpecSorts : fa(a) appTSP a -> ASortMap a -> ()
 def appSpecSorts tsp_apps sorts = 
   appAQualifierMap (fn (_, _, defs) -> 
		     appSortSchemes tsp_apps defs)
                    sorts 
    
  op appSpecOps : fa(a) appTSP a -> AOpMap a -> ()
 def appSpecOps tsp_apps ops =
   appAQualifierMap (fn (_, _, (_, srt), defs) -> 
		     (appSort        tsp_apps srt ; 
		      appTermSchemes tsp_apps defs))
                    ops
    
  op appSpecProperties : fa(a) appTSP a -> AProperties a -> ()
 def appSpecProperties tsp_apps properties =
    app (fn (_, _, _, term) -> 
	 appTerm tsp_apps term)
        properties

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Sorts, Ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op specSorts : fa(b) ASpec b -> List SortSignature
 op specOps   : fa(b) ASpec b -> List (AOpSignature b)

 def specSorts (spc) = 
   foldriAQualifierMap (fn (q, id, (sort_names, tyVars, opt_def), 
			    result) -> 
			cons ((q, id, tyVars), result)) 
                       [] spc.sorts 

 def specOps (spc) = 
   foldriAQualifierMap (fn (q, id, (op_names, fixity, (tyVars, srt), opt_def),
			    result) -> 
			cons ((q, id, tyVars, srt), result))
                       [] spc.ops 

 % --------------------------------------------------------------------------------
 % return sorts/ops as list with entries of the form (qualifier, id, info)

 op sortsAsList     : fa(b) ASpec b -> List (Qualifier * Id * ASortInfo b)
 op opsAsList       : fa(b) ASpec b -> List (Qualifier * Id * AOpInfo   b)
 op sortInfosAsList : fa(b) ASpec b -> List (ASortInfo b)
 op opInfosAsList   : fa(b) ASpec b -> List (AOpInfo   b)

 def sortsAsList(spc) =
   foldriAQualifierMap (fn (q, id, sort_info, new_list) -> 
			cons ((q, id, sort_info), new_list))
                       [] spc.sorts

 def sortInfosAsList spc =
   foldriAQualifierMap (fn (q, id, info, new_list) -> 
			%% there could be multiple entries for the same sortInfo,
			%% so just consider the entry corresponding to the primary alias
			let (Qualified (primary_q, primary_id)) :: _ = info.1 in
			if q = primary_q && id = primary_id then
			  cons (info, new_list)
			else
			  new_list)
                       [] spc.sorts

 def opsAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) -> 
			cons ((q, id, info), new_list))
                       [] spc.ops

 def opInfosAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) -> 
			%% there could be multiple entries for the same opInfo,
			%% so just consider the entry corresponding to the primary alias
			let (Qualified (primary_q, primary_id)) :: _ = info.1 in
			if q = primary_q && id = primary_id then
			  cons (info, new_list)
			else
			  new_list)
                       [] spc.ops

  op equalSortInfo?: fa(a) ASortInfo a * ASortInfo a -> Boolean
 def equalSortInfo? ((sortNames1, tyvs1, defs1), 
		     (sortNames2, tyvs2, defs2)) 
   =
   sortNames1 = sortNames2
   & tyvs1 = tyvs2
   %% Could take into account substitution of tyvs
   & all (fn def1 -> 
	  exists (fn def2 -> equalSortScheme? (def1, def2)) 
	         defs2) 
         defs1


  op equalOpInfo?: fa(a) AOpInfo a * AOpInfo a -> Boolean
 def equalOpInfo? ((opNames1, fixity1, sortsch1, defs1),
		   (opNames2, fixity2, sortsch2, defs2)) 
   =
   opNames1 = opNames2
   & fixity1 = fixity2
   & equalSortScheme? (sortsch1, sortsch2)
   & all (fn def1 -> 
	  exists (fn def2 -> equalTermScheme? (def1, def2)) 
	         defs2) 
         defs1

  op equalSortScheme?: fa(a) ASortScheme a * ASortScheme a -> Boolean
 def equalSortScheme? ((tyvs1, s1), (tyvs2, s2)) =
   %% TODO: take into account substitution of tyvs
   tyvs1 = tyvs2 & equalSort? (s1, s2)

  op equalTermScheme?: fa(a) ATermScheme a * ATermScheme a -> Boolean
 def equalTermScheme? ((tyvs1, t1), (tyvs2, t2)) =
   %% TODO: take into account substitution of tyvs
   tyvs1 = tyvs2 & equalTerm? (t1, t2)

  op equalProperty?: fa(a) AProperty a * AProperty a -> Boolean
 def equalProperty? ((propType1, propName1, tyVars1, term1), 
		     (propType2, propName2, tyVars2, term2))
   =
   propType1 = propType2 & equalTerm? (term1, term2) & equalTyVars? (tyVars1, tyVars2)


 % --------------------------------------------------------------------------------

  op emptyOpNames : OpNames
 def emptyOpNames = []

  op emptySortNames : SortNames
 def emptySortNames = []

  op emptyPropertyNames : PropertyNames
 def emptyPropertyNames = []

  op memberNames : QualifiedId * List QualifiedId -> Boolean
 def memberNames (qid, qids) = member (qid, qids)

  op memberQualifiedId : Qualifier * Id * List QualifiedId -> Boolean
 def memberQualifiedId (q, id, qids) =
   exists (fn (Qualified (qq, ii)) -> q = qq & id = ii) qids

  op addToNames : QualifiedId * List QualifiedId -> List QualifiedId 
 def addToNames (qid, qids) = cons (qid, qids)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op emptySpec           : fa(a) ASpec         a
 op emptyImports        : Imports
 op emptyAProperties    : fa(a) AProperties   a
 op emptyASortMap       : fa(a) AQualifierMap a
 op emptyAOpMap         : fa(a) AQualifierMap a
 op initialSpecInCat    : fa(a) ASpec         a

 %% Create new spec with altered name, imports, sorts, ops, properties, etc.

 op setImportInfo       : fa(a) ASpec a * ImportInfo       -> ASpec a
 op setImports          : fa(a) ASpec a * Imports          -> ASpec a
 op setLocalOps         : fa(a) ASpec a * OpNames          -> ASpec a
 op setLocalSorts       : fa(a) ASpec a * SortNames        -> ASpec a
 op setLocalProperties  : fa(a) ASpec a * PropertyNames    -> ASpec a
 op setSorts            : fa(a) ASpec a * ASortMap    a    -> ASpec a
 op setOps              : fa(a) ASpec a * AOpMap      a    -> ASpec a
 op setProperties       : fa(a) ASpec a * AProperties a    -> ASpec a

 % substract the ops and sorts in the second argument from those
 % appearing in the first.
 op subtractSpec        : fa (a) ASpec a -> ASpec a -> ASpec a

 %% Create new spec with added sort, op, property, import, etc.

 op addImport           : fa(a) Import                                 * ASpec a -> ASpec a
 op addProperty         : fa(a) (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom            : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjecture       : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheorem          : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheoremLast      : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjectures      : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addTheorems         : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a

 op addLocalSortName    : fa(a) ASpec a * QualifiedId -> ASpec a
 op addLocalOpName      : fa(a) ASpec a * QualifiedId -> ASpec a
 op addLocalPropertyName: fa(a) ASpec a * QualifiedId -> ASpec a

 op localOp?            : fa(a) QualifiedId * ASpec a -> Boolean
 op localSort?          : fa(a) QualifiedId * ASpec a -> Boolean
 op localProperty?      : fa(a) QualifiedId * ASpec a -> Boolean

 op localProperties     : fa(a) ASpec a -> AProperties a

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyImports            = []
 def fa (a) emptyAProperties = []
 def emptyASortMap           = emptyAQualifierMap
 def emptyAOpMap             = emptyAQualifierMap
 def emptyImportInfo         = {imports      = emptyImports,
                                localOps     = emptyOpNames,
                                localSorts   = emptySortNames,
			        localProperties = emptyPropertyNames}

 def emptySpec = 
  {importInfo       = emptyImportInfo,
   sorts            = emptyASortMap,
   ops              = emptyAOpMap,
   properties       = emptyAProperties}

 def initialSpecInCat = 
  {importInfo       = emptyImportInfo,  
   sorts            = emptyASortMap,   
   ops              = emptyAOpMap,     
   properties       = emptyAProperties}

 def setImports         (spc, new_imports)     = spc << {importInfo = spc.importInfo << {imports         = new_imports}}
 def setLocalOps        (spc, new_local_ops)   = spc << {importInfo = spc.importInfo << {localOps        = new_local_ops}}
 def setLocalSorts      (spc, new_local_sorts) = spc << {importInfo = spc.importInfo << {localSorts      = new_local_sorts}}
 def setLocalProperties (spc, new_local_props) = spc << {importInfo = spc.importInfo << {localProperties = new_local_props}}

 def setImportInfo (spc, new_import_info) = spc << {importInfo = new_import_info}
 def setSorts      (spc, new_sorts)       = spc << {sorts      = new_sorts}
 def setOps        (spc, new_ops)         = spc << {ops        = new_ops}
 def setProperties (spc, new_properties)  = spc << {properties = new_properties}

 % ------------------------------------------------------------------------

 def addImport ((specCalcTerm, imported_spec), spc) =
   setImports (spc, cons ((specCalcTerm, imported_spec), spc.importInfo.imports))

 def addProperty (new_property, spc) =
   let spc = setProperties (spc, spc.properties ++ [new_property]) in
   addLocalPropertyName(spc,propertyName new_property)

 def addAxiom       ((name, type_vars, formula), spc) = addProperty ((Axiom      : PropertyType, name, type_vars, formula), spc) 
 def addConjecture  ((name, type_vars, formula), spc) = addProperty ((Conjecture : PropertyType, name, type_vars, formula), spc) 
 def addTheorem     ((name, type_vars, formula), spc) = addProperty ((Theorem    : PropertyType, name, type_vars, formula), spc) 

 def addTheoremLast ((name, type_vars, formula), spc) =  
   setProperties (spc, spc.properties ++ [(Theorem : PropertyType, name, type_vars, formula)])

 def addConjectures (conjectures, spc) = foldl addConjecture spc conjectures
 def addTheorems    (theorems,    spc) = foldl addTheorem    spc theorems

 def addLocalSortName (spc, new_local_sort) =
   let localSorts = spc.importInfo.localSorts in
   if memberNames (new_local_sort, localSorts) then
     spc
   else 
     setLocalSorts (spc, addToNames (new_local_sort, localSorts))

 def addLocalOpName (spc, new_local_op) =
   let localOps = spc.importInfo.localOps in
   if memberNames (new_local_op, localOps) then
     spc
   else 
     setLocalOps (spc, addToNames (new_local_op, localOps))

 def addLocalPropertyName (spc, new_local_op) =
   let localProperties = spc.importInfo.localProperties in
   if memberNames (new_local_op, localProperties) then
     spc
   else 
     setLocalProperties (spc, addToNames (new_local_op, localProperties))

 def localOp?       (Qualified (q, id), spc) = memberQualifiedId (q, id, spc.importInfo.localOps)
 def localSort?     (Qualified (q, id), spc) = memberQualifiedId (q, id, spc.importInfo.localSorts)
 def localProperty? (Qualified (q, id), spc) = memberQualifiedId (q, id, spc.importInfo.localProperties)

 def localProperties spc =
   filter (fn p -> localProperty? (propertyName p, spc)) spc.properties

 op findTheSort  : fa(a) ASpec a * QualifiedId -> Option (ASortInfo a)  
 op findTheOp    : fa(a) ASpec a * QualifiedId -> Option (AOpInfo   a)

 op findAllSorts : fa(a) ASpec a * QualifiedId -> List (ASortInfo a)
 op findAllOps   : fa(a) ASpec a * QualifiedId -> List (AOpInfo   a)

 def findTheSort (spc, Qualified (q, id)) =
   %% We're looking for precisely one sort,
   %% which we might have specified as being unqualified.
   %% (I.e., unqualified is not a wildcard here.)
   findAQualifierMap (spc.sorts, q, id)

 def findTheOp (spc, Qualified (q, id)) =
   %% We're looking for precisely one op,
   %% which we might have specified as being unqualified.
   %% (I.e., unqualified is not a wildcard here.)
   findAQualifierMap (spc.ops, q, id)

 %% Overloading is not particularly meaningful for sorts. 
 %% (Would we ever want both  FOO.FOO x and FOO.FOO x y  as distinct sorts?)
 %% but we might have two or more sorts X.S, Y.S, etc.
 %% If the qualifier is UnQualified then we return unqualified answer first so as to
 %% give preference to it because there is no other way to refer to this entry.
 %% Note that checkSort depends on this behavior.

 def findAllSorts (spc, Qualified (q, id)) =
   let found = (case findAQualifierMap (spc.sorts, q, id) of
		  | Some sort_info -> [sort_info]
		  | None           -> [])
   in
   if q = UnQualified then
     found ++ filter (fn info -> ~(member (info, found)))
                     (wildFindUnQualified (spc.sorts, id))
   else 
     found
 
 def findAllOps (spc, Qualified (q, id)) =
   if q = UnQualified then
     wildFindUnQualified (spc.ops, id)
   else
     case findAQualifierMap (spc.ops, q, id) of
       | Some op_info -> [op_info]
       | None         -> []
		
 %%  find all the matches to id in every second level map
  op wildFindUnQualified : fa (a) AQualifierMap a * Id -> List a
 def wildFindUnQualified (qualifier_map, id) =
   foldriAQualifierMap (fn (_, ii, val, results) ->
			if id = ii then
			  Cons (val, results)
			else
			  results)
                       []
		       qualifier_map

 % this next one is use only in substract spec. it cannot be defined inside
 % the scope of subtractSpec as there is no let-polymorphism in Specware
  op mapDiffOps : fa (a) AOpMap a -> AOpMap a -> AOpMap a
 def mapDiffOps xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of

                          | None -> 
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)

			  | Some (_, _, _, []) -> 
			    (case x_info of

			       | (_, _, _, []) -> 
			         %% there is an undefined y_info corresponding to an undefined x_info, 
			         %% so omit the x_info
			         newMap

			       | _  -> 
				 %% there is an undefined y_info corresponding to an defined x_info, 
				 %% so include the x_info
				 insertAQualifierMap (newMap, q, id, x_info))

			  | _ -> 
			    %% there is a defined y_info, 
			    %% so omit the x_info, whether it is defined or not
			    newMap)

                       emptyAQualifierMap 
                       xMap

  op mapDiffSorts : fa (a) ASortMap a -> ASortMap a -> ASortMap a
 def mapDiffSorts xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of

                          | None -> 
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)

			  | Some (_, _, []) -> 
			    (case x_info of
			       | (_, _, []) -> 
			         %% there is an undefined y_info corresponding to an undefined x_info, 
			         %% so omit the x_info
			         newMap
			       | _  -> 
				 %% there is an undefined y_info corresponding to an defined x_info, 
				 %% so include the x_info
				 insertAQualifierMap (newMap, q, id, x_info))

			  | _ -> 
			    %% there is a defined y_info, 
			    %% so omit the x_info, whether it is defined or not
			    newMap)

                       emptyAQualifierMap 
                       xMap

 def subtractSpec x y = 
   {importInfo = x.importInfo,
    properties = foldr (fn (x, props) ->
			if member (x, y.properties) then
			  props
			else
			  Cons (x, props)) 
                       [] x.properties,
    ops        = mapDiffOps   x.ops   y.ops,
    sorts      = mapDiffSorts x.sorts y.sorts}

  op addDisjointImport: Spec * Spec -> Spec
 def addDisjointImport (spc, imported_spec) =
   let def mergeSortStep (imported_q, imported_id, imported_sort_info, combined_psorts) =
         insertAQualifierMap (combined_psorts,
			      imported_q,
			      imported_id,
			      imported_sort_info)
       def mergeOpStep (imported_q, imported_id, imported_op_info, combined_pops) =
	 insertAQualifierMap (combined_pops,
			      imported_q,
			      imported_id,
			      imported_op_info)
	   
   in
   %let spc = addImport (("", imported_spec), spc) in
   let newSorts = foldriAQualifierMap mergeSortStep spc.sorts imported_spec.sorts in
   let spc      = setSorts (spc, newSorts) in
   let newOps   = foldriAQualifierMap mergeOpStep   spc.ops   imported_spec.ops   in
   let spc      = setOps   (spc, newOps)   in
   setProperties (spc, spc.properties ++ imported_spec.properties)

 %%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% misc old stuff...

 %%
 %% % get the sort/op names as list of strings
 %% % unused?
 %%
 %%  op sortNames : fa(b) ASpec b -> List String
 %%  op opNames   : fa(b) ASpec b -> List String
 %% 
 %%  def sortNames spc =
 %%   foldriAQualifierMap (fn (_, sort_name, _, new_list) -> 
 %%                          List.concat (new_list, [sort_name]))
 %%                      [] spc.sorts
 %% 
 %%  def opNames spc =
 %%   foldriAQualifierMap (fn (_, op_name, _, new_list) -> 
 %%                          List.concat (new_list, [op_name])) 
 %%                      [] spc.ops


 %% old style...
 %% The following havebeen replaced with monadic versions in
 %% SpecCalculus/Semantics/Evaluate/Spec/Utilitites

 %% op addSort             : fa(a) (Qualifier * Id * 
 %%                                 TyVars * Option(ASort a)) * 
 %%                                 ASpec a -> ASpec a
 %%
 %% %% new style...
 %% op addAliasedSort      : fa(a) (Qualifier * Id * 
 %%                                  SortNames * TyVars * Option (ASort a)) * 
 %%                                ASpec a -> ASpec a
 %%
 %% %% old style...
 %% op addOp               : fa(a) (Qualifier * Id * 
 %%                                 Fixity * ASortScheme a * Option (ATerm a)) * 
 %%                                ASpec a -> ASpec a
 %%
 %% %% new style...
 %% op addAliasedOp        : fa(a) (Qualifier * Id * 
 %%                                 OpNames * Fixity * ASortScheme a * Option (ATerm a)) * 
 %%                                ASpec a -> ASpec a
 %%%%%%%%%%%%%%%%%%%%%%%%%%


endspec
