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

 type ASpecs b = List (ASpec b)

 type ASpec b = {importInfo   : ImportInfo,	% importInfo is ignored by equality test on specs
		 sorts        : ASortMap    b,
		 ops          : AOpMap      b,
		 properties   : AProperties b}

 type ImportInfo = {imports         : Imports,
		    localOps        : OpNames,
		    localSorts      : SortNames,
		    localProperties : PropertyNames}

 type SortNames      = List SortName
 type OpNames        = List OpName
 type PropertyNames  = List PropertyName  
 type SortName       = QualifiedId
 type OpName         = QualifiedId
 type PropertyName   = QualifiedId

 type Aliases      = QualifiedIds
 type QualifiedIds = List QualifiedId 

  op someAliasIsLocal? : Aliases * QualifiedIds -> Boolean
 def someAliasIsLocal? (aliases, local_names) =
   exists (fn qid -> member (qid, local_names)) aliases 
    
 type Imports = List Import
 type Import  = (SpecCalc.Term Position) * Spec

 type ASortMap  b = AQualifierMap (ASortInfo b) % i.e., Qualifier -> Id -> info
 type AOpMap    b = AQualifierMap (AOpInfo   b) % i.e., Qualifier -> Id -> info

 type ASortInfo b = {names : SortNames,
		     dfn   : ASort b}

 type AOpInfo   b = {names  : OpNames,
		     fixity : Fixity,
		     dfn    : ATerm b}

 type AProperties   b  = List (AProperty b) 
 type AProperty     b  = PropertyType * PropertyName * TyVars * ATerm b
 type PropertyType     = | Axiom | Theorem | Conjecture
 
 op primarySortName : [b] ASortInfo b -> SortName
 op primaryOpName   : [b] AOpInfo   b -> OpName
 op propertyName    : [b] AProperty b -> PropertyName

 def primarySortName info = hd info.names
 def primaryOpName   info = hd info.names
 def propertyName    p    = p.2

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op definedOpInfo? : [b] AOpInfo b -> Boolean
 def definedOpInfo? info =
   definedTerm? info.dfn

  op definedTerm? : [b] ATerm b -> Boolean
 def definedTerm? tm =
   case tm of
     | Any _ -> false 
     | SortedTerm (tm, _, _) -> definedTerm? tm
     | Pi         (_, tm, _) -> definedTerm? tm
     | And         (tms,  _) -> exists definedTerm? tms
     | _  -> true 

  op definedSortInfo? : [b] ASortInfo b -> Boolean
 def definedSortInfo? info =
   definedSort? info.dfn

  op definedSort? : [b] ASort b -> Boolean
 def definedSort? srt =
   case srt of
     | Any _ -> false 
     | Pi  (_, srt, _) -> definedSort? srt
     | And (srts,   _) -> exists definedSort? srts
     | _  -> true 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of opInfo
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op opInfoDefs : [b] AOpInfo b -> List (ATerm b) 
 def opInfoDefs info =
   case info.dfn of
     | And (tms, _) -> filter definedTerm? tms
     | tm           -> filter definedTerm? [tm]

  op opInfoDeclsAndDefs : [b] AOpInfo b -> List (ATerm b) * List (ATerm b)
 def opInfoDeclsAndDefs info =
   termDeclsAndDefs info.dfn

  op termDeclsAndDefs : [b] ATerm b -> List (ATerm b) * List (ATerm b)
 def termDeclsAndDefs tm =
   let 
     def segregate tms =
       foldl (fn (tm, (decls, defs)) -> 
	      if definedTerm? tm then
		(decls, defs ++ [tm])
	      else
		(decls ++ [tm], defs))
             ([],[])
             tms				      
   in
     case tm of
       | And (tms, _) -> segregate tms
       | tm           -> segregate [tm]

  op termDefs : [b] ATerm b -> List (ATerm b) 
 def termDefs tm =
   case tm of
     | And (tms, _) -> filter definedTerm? tms
     | tm           -> filter definedTerm? [tm]

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of sortInfo
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op sortInfoDefs : [b] ASortInfo b -> List (ASort b) 
 def sortInfoDefs info =
   case info.dfn of
     | And (srts, _) -> filter definedSort? srts
     | srt           -> filter definedSort? [srt]

  op sortInfoDeclsAndDefs : [b] ASortInfo b -> List (ASort b) * List (ASort b)
 def sortInfoDeclsAndDefs info =
   let 
     def segregate srts =
       foldl (fn (srt, (decls, defs)) -> 
	      if definedSort? srt then
		(decls, defs ++ [srt])
	      else
		(decls ++ [srt], defs))
             ([],[])
             srts
   in
     case info.dfn of
       | And (srts, _) -> segregate srts
       | srt           -> segregate [srt]

  op sortDefs : [b] ASort b -> List (ASort b) 
 def sortDefs srt =
   case srt of
     | And (srts, _) -> filter definedSort? srts
     | srt           -> filter definedSort? [srt]

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of primary op def
 %%%  Any uses of these simply ignore any definitions after the 
 %%%  first one, which (IMHO) is probably not a good thing to do,
 %%%  but they are here for backwards compatibility
 %%%  Each use should be reviewed.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op unpackFirstOpDef    : [b] AOpInfo b -> TyVars * ASort b * ATerm b
  op firstOpDefTyVars    : [b] AOpInfo b -> TyVars
  op firstOpDefInnerSort : [b] AOpInfo b -> ASort b
  op firstOpDefInnerTerm : [b] AOpInfo b -> ATerm b

 def unpackFirstOpDef info =
   let (decls, defs) = opInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   unpackTerm first_def 

 def firstOpDefTyVars info =
   let (decls, defs) = opInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   termTyVars first_def

 def firstOpDefInnerSort info =
   let (decls, defs) = opInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   case first_def of
     | Pi (_, tm, _) -> termSort tm % avoid returning Pi sort
     | tm            -> termSort tm

 def firstOpDefInnerTerm info =
   termInnerTerm (hd (opInfoDefs info)) % fail if decl but no def

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%  components of primary sort def
 %%%  Any uses of these simply ignore any definitions after the 
 %%%  first one, which (IMHO) is probably not a good thing to do,
 %%%  but they are here for backwards compatibility
 %%%  Each use should be reviewed.
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op unpackFirstSortDef    : [b] ASortInfo b -> TyVars * ASort b 
  op firstSortDefTyVars    : [b] ASortInfo b -> TyVars
  op firstSortDefInnerSort : [b] ASortInfo b -> ASort b

 def unpackFirstSortDef info =
   let (decls, defs) = sortInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   unpackSort first_def 

 def firstSortDefTyVars info =
   let (decls, defs) = sortInfoDeclsAndDefs info in
   let first_def :: _ = defs ++ decls in
   sortTyVars first_def 
   
 def firstSortDefInnerSort info =
   sortInnerSort (hd (sortInfoDefs info)) % fail if no decl but no def
   
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

  op mapSpec : [b] TSP_Maps b -> ASpec b -> ASpec b
 def mapSpec tsp {importInfo, sorts, ops, properties} =
   {
    importInfo       = importInfo,
    sorts            = mapSpecSorts      tsp sorts,
    ops              = mapSpecOps        tsp ops,
    properties       = mapSpecProperties tsp properties
   }

  op mapSpecSorts : [b] TSP_Maps b -> ASortMap b -> ASortMap b 
 def mapSpecSorts tsp sorts =
   mapSortInfos (fn info -> info << {dfn = mapSort tsp info.dfn})
                sorts

  op mapSpecOps : [b] TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOps tsp ops =
   mapOpInfos (fn info -> info << {dfn = mapTerm tsp info.dfn})
              ops

 %% mapSortInfos and mapOpInfos apply the provided function
 %% just once to an info, even if it has multiple aliases,
 %% then arrange for each alias to index that same new info.

  op primarySortName? : [a] Qualifier * Id * ASortInfo a -> Boolean
  op primaryOpName?   : [a] Qualifier * Id * AOpInfo   a -> Boolean

 def primarySortName? (q, id, info) =
   let Qualified (qq, ii) = primarySortName info in
   q = qq && id = ii

 def primaryOpName? (q, id, info) =
   let Qualified (qq, ii) = primaryOpName info in
   q = qq && id = ii

  op mapSortInfos : [b] (ASortInfo b -> ASortInfo b) -> ASortMap b -> ASortMap b 
 def mapSortInfos sortinfo_map sorts =
   foldriAQualifierMap 
     (fn (q, id, info, new_map) ->
      if primarySortName? (q, id, info) then
	%% When access is via a primary alias, update the info and
	%% record that (identical) new value for all the aliases.
	let new_info = sortinfo_map info in
	foldl (fn (Qualified (q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, new_info))				   
	      new_map
	      info.names
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     emptyAQualifierMap
     sorts

  op mapOpInfos : [b] (AOpInfo b -> AOpInfo b) -> AOpMap b -> AOpMap b 
 def mapOpInfos opinfo_map ops =
   foldriAQualifierMap 
     (fn (q, id, info, new_map) ->
      if primaryOpName? (q, id, info) then
	%% When access is via a primary alias, update the info and 
	%% ecord that (identical) new value for all the aliases.
	let new_info = opinfo_map info in
	foldl (fn (Qualified (q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, new_info))				   
	      new_map
	      info.names
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     emptyAQualifierMap
     ops

  op filterSortMap : [b] (ASortInfo b -> Boolean) -> ASortMap b -> ASortMap b 
 def filterSortMap keep? sorts =
   foldriAQualifierMap 
     (fn (q, id, info, new_map) ->
      if primarySortName? (q, id, info) && keep? info then
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, info))				   
	      new_map
	      info.names
      else
	new_map)
     emptyAQualifierMap
     sorts

  op filterOpMap : [b] (AOpInfo b -> Boolean) -> AOpMap b -> AOpMap b 
 def filterOpMap keep? ops =
   foldriAQualifierMap 
     (fn (q, id, info, new_map) ->
      if primaryOpName? (q, id, info) && keep? info then
	foldl (fn (Qualified(q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, info))				   
	      new_map
	      info.names
      else
	new_map)
     emptyAQualifierMap
     ops

  op foldSortInfos : [a,b] (ASortInfo a * b -> b) -> b -> ASortMap a -> b
 def foldSortInfos f init sorts =
   foldriAQualifierMap 
     (fn (q, id, info, result) ->
      if primarySortName? (q, id, info) then
	f (info, result)
      else
	result)
     init
     sorts

  op foldOpInfos : [a,b] (AOpInfo a * b -> b) -> b -> AOpMap a -> b
 def foldOpInfos f init ops =
   foldriAQualifierMap 
     (fn (q, id, info, result) ->
      if primaryOpName? (q, id, info) then
	f (info, result)
      else
	result)
     init
     ops

  op appSortInfos : [b] (ASortInfo b -> ()) -> ASortMap b -> ()
 def appSortInfos f sorts =
   appiAQualifierMap 
     (fn (q, id, info) ->
      if primarySortName? (q, id, info) then
	f info
      else
	())
     sorts

  op appOpInfos : [b] (AOpInfo b -> ()) -> AOpMap b -> ()
 def appOpInfos f ops =
   appiAQualifierMap 
     (fn (q, id, info) ->
      if primaryOpName? (q, id, info) then
	f info
      else
	())
     ops

  op mapSpecProperties : [b] TSP_Maps b -> AProperties b ->  AProperties b 
 def mapSpecProperties tsp properties =
   map (fn (pt, nm, tvs, term) -> 
           (pt, nm, tvs, mapTerm tsp term))
       properties

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

  op appSpec    : [a] appTSP a -> ASpec a    -> ()
 def appSpec tsp_apps spc = 
   (
    appSpecOps        tsp_apps spc.ops;
    appSpecSorts      tsp_apps spc.sorts; 
    appSpecProperties tsp_apps spc.properties
   )

  op appSpecSorts : [a] appTSP a -> ASortMap a -> ()
 def appSpecSorts tsp sorts = 
   appAQualifierMap (fn info -> appSort tsp info.dfn) sorts 
    
  op appSpecOps : [a] appTSP a -> AOpMap a -> ()
 def appSpecOps tsp ops =
   appAQualifierMap (fn info -> appTerm tsp info.dfn) ops
    
  op appSpecProperties : [a] appTSP a -> AProperties a -> ()
 def appSpecProperties tsp properties =
    app (fn (_, _, _, term) -> 
	 appTerm tsp term)
        properties

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Sorts, Ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % return sorts/ops as list with entries of the form (qualifier, id, info)

 op sortsAsList     : [b] ASpec b -> List (Qualifier * Id * ASortInfo b)
 op opsAsList       : [b] ASpec b -> List (Qualifier * Id * AOpInfo   b)
 op sortInfosAsList : [b] ASpec b -> List (ASortInfo b)
 op opInfosAsList   : [b] ASpec b -> List (AOpInfo   b)

 def sortsAsList(spc) =
   foldriAQualifierMap (fn (q, id, info, new_list) -> 
			cons ((q, id, info), new_list))
                       [] spc.sorts

 def sortInfosAsList spc =
   foldriAQualifierMap (fn (q, id, info, new_list) -> 
			%% there could be multiple entries for the same sortInfo,
			%% so just consider the entry corresponding to the primary alias
			let Qualified (primary_q, primary_id) = primarySortName info in
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
			let Qualified (primary_q, primary_id) = primaryOpName info in
			if q = primary_q && id = primary_id then
			  cons (info, new_list)
			else
			  new_list)
                       [] spc.ops

  op equalSortInfo?: [a] ASortInfo a * ASortInfo a -> Boolean
 def equalSortInfo? (info1, info2) =
   info1.names = info2.names
   %% Could take into account substitution of tvs
   && equalSort? (info1.dfn, info2.dfn)

  op equalOpInfo?: [a] AOpInfo a * AOpInfo a -> Boolean
 def equalOpInfo? (info1, info2) =
   info1.names = info2.names
   && info1.fixity = info2.fixity
   && equalTerm? (info1.dfn, info2.dfn)

  op equalProperty?: [a] AProperty a * AProperty a -> Boolean
 def equalProperty? ((propType1, propName1, tvs1, fm1), 
		     (propType2, propName2, tvs2, fm2))
   =
   propType1 = propType2 && equalTerm? (fm1, fm2) && equalTyVars? (tvs1, tvs2)


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
   exists (fn (Qualified (qq, ii)) -> q = qq && id = ii) qids

  op addToNames : QualifiedId * List QualifiedId -> List QualifiedId 
 def addToNames (qid, qids) = cons (qid, qids)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op emptySpec           : [a] ASpec         a
 op emptyImports        : Imports
 op emptyAProperties    : [a] AProperties   a
 op emptyASortMap       : [a] AQualifierMap a
 op emptyAOpMap         : [a] AQualifierMap a
 op initialSpecInCat    : [a] ASpec         a

 %% Create new spec with altered name, imports, sorts, ops, properties, etc.

 op setImportInfo       : [a] ASpec a * ImportInfo       -> ASpec a
 op setImports          : [a] ASpec a * Imports          -> ASpec a
 op setLocalOps         : [a] ASpec a * OpNames          -> ASpec a
 op setLocalSorts       : [a] ASpec a * SortNames        -> ASpec a
 op setLocalProperties  : [a] ASpec a * PropertyNames    -> ASpec a
 op setSorts            : [a] ASpec a * ASortMap    a    -> ASpec a
 op setOps              : [a] ASpec a * AOpMap      a    -> ASpec a
 op setProperties       : [a] ASpec a * AProperties a    -> ASpec a

 % substract the ops and sorts in the second argument from those
 % appearing in the first.
 op subtractSpec        : [a] ASpec a -> ASpec a -> ASpec a

 %% Create new spec with added sort, op, property, import, etc.

 op addImport           : [a] Import                                 * ASpec a -> ASpec a
 op addProperty         : [a] (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom            : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjecture       : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheorem          : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheoremLast      : [a] (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjectures      : [a] List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addTheorems         : [a] List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a

 op addLocalSortName    : [a] ASpec a * QualifiedId -> ASpec a
 op addLocalOpName      : [a] ASpec a * QualifiedId -> ASpec a
 op addLocalPropertyName: [a] ASpec a * QualifiedId -> ASpec a

 op localOp?            : [a] QualifiedId * ASpec a -> Boolean
 op localSort?          : [a] QualifiedId * ASpec a -> Boolean
 op localProperty?      : [a] QualifiedId * ASpec a -> Boolean

 op localProperties     : [a] ASpec a -> AProperties a

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyImports         = []
 def [a] emptyAProperties = []
 def emptyASortMap        = emptyAQualifierMap
 def emptyAOpMap          = emptyAQualifierMap
 def emptyImportInfo      = {imports      = emptyImports,
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

 def addAxiom       ((name, tvs, formula), spc) = addProperty ((Axiom      : PropertyType, name, tvs, formula), spc) 
 def addConjecture  ((name, tvs, formula), spc) = addProperty ((Conjecture : PropertyType, name, tvs, formula), spc) 
 def addTheorem     ((name, tvs, formula), spc) = addProperty ((Theorem    : PropertyType, name, tvs, formula), spc) 

 def addTheoremLast ((name, tvs, formula), spc) =  
   setProperties (spc, spc.properties ++ [(Theorem : PropertyType, name, tvs, formula)])

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

 op findTheSort  : [a] ASpec a * QualifiedId -> Option (ASortInfo a)  
 op findTheOp    : [a] ASpec a * QualifiedId -> Option (AOpInfo   a)

 op findAllSorts : [a] ASpec a * QualifiedId -> List (ASortInfo a)
 op findAllOps   : [a] ASpec a * QualifiedId -> List (AOpInfo   a)

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
		  | Some info -> [info]
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
       | Some info -> [info]
       | None         -> []
		
 %%  find all the matches to id in every second level map
  op wildFindUnQualified : [a] AQualifierMap a * Id -> List a
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
  op mapDiffOps : [a] AOpMap a -> AOpMap a -> AOpMap a
 def mapDiffOps xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of
                          | None -> 
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)
			  | Some y_info ->
			    if definedOpInfo? y_info then
			      %% omit the x_info, whether it is defined or not
			      newMap
			    else if definedOpInfo? x_info then
			      insertAQualifierMap (newMap, q, id, x_info)
			    else
			      newMap)
                       emptyAQualifierMap 
                       xMap

  op mapDiffSorts : [a] ASortMap a -> ASortMap a -> ASortMap a
 def mapDiffSorts xMap yMap =
   foldriAQualifierMap (fn (q, id, x_info, newMap) ->
			case findAQualifierMap (yMap, q, id) of
                          | None -> 
			    %% no y_info corresponding to the x_info,
			    %% so include the x_info, whether it is defined or not
			    insertAQualifierMap (newMap, q, id, x_info)
			  | Some y_info ->
			    if definedSortInfo? y_info then
			      %% omit the x_info, whether it is defined or not
			      newMap
			    else if definedSortInfo? x_info then
			      insertAQualifierMap (newMap, q, id, x_info)
			    else
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

  op subtractSpecProperties: Spec * Spec -> Spec
  def subtractSpecProperties(spec1, spec2) =
    let spec2PropNames = map (fn (pt, pn, tv, tm) -> pn) spec2.properties in
    let newProperties =
        filter (fn (pt, pn, tv, tm) -> ~(member(pn, spec2PropNames))) spec1.properties in
    {
     importInfo = spec1.importInfo,
     properties = newProperties,
     ops   = spec1.ops,
     %ops   = mapDiffOps spec1.ops spec2.ops,
     sorts = spec1.sorts
     %sorts = mapDiffSorts spec1.sorts spec2.sorts
   }
  
  op addDisjointImport: Spec * Spec -> Spec
 def addDisjointImport (spc, imported_spec) =
   let def mergeSortStep (imported_q, imported_id, imported_info, combined_psorts) =
         insertAQualifierMap (combined_psorts,
			      imported_q,
			      imported_id,
			      imported_info)
       def mergeOpStep (imported_q, imported_id, imported_info, combined_pops) =
	 insertAQualifierMap (combined_pops,
			      imported_q,
			      imported_id,
			      imported_info)
	   
   in
   %let spc = addImport (("", imported_spec), spc) in
   let newSorts = foldriAQualifierMap mergeSortStep spc.sorts imported_spec.sorts in
   let spc      = setSorts (spc, newSorts) in
   let newOps   = foldriAQualifierMap mergeOpStep   spc.ops   imported_spec.ops   in
   let spc      = setOps   (spc, newOps)   in
   setProperties (spc, spc.properties ++ imported_spec.properties)


endspec
