AnnSpec qualifying spec 

 import Position
 import MSTerm
 %import QualifierMapAsSTHashTable
 import QualifierMapAsSTHTable2
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

 type ASpec b = {%importInfo : ImportInfo, 	% importInfo is ignored by equality test on specs
		 sorts      : ASortMap    b,
		 ops        : AOpMap      b,
		 elements   : ASpecElements b,
		 qualified? : Boolean}

% type ImportInfo = {imports         : Imports,
%		    localOps        : OpNames,
%		    localSorts      : SortNames,
%		    localProperties : PropertyNames}

 type SortNames      = List SortName
 type OpNames        = List OpName
 type PropertyNames  = List PropertyName  
 type SortName       = QualifiedId
 type OpName         = QualifiedId
 type PropertyName   = QualifiedId

 type Aliases      = QualifiedIds
 type QualifiedIds = List QualifiedId 

 type Imports = List Import
 type Import  = (SpecCalc.Term Position) * Spec

 type ASortMap  b = AQualifierMap (ASortInfo b) % i.e., Qualifier -> Id -> info
 type AOpMap    b = AQualifierMap (AOpInfo   b) % i.e., Qualifier -> Id -> info

 type ASortInfo b = {names : SortNames,
		     dfn   : ASort b}

 type AOpInfo   b = {names  : OpNames,
		     fixity : Fixity,
		     dfn    : ATerm b,
		     fullyQualified?: Boolean}

 type ASpecElements b  = List (ASpecElement b)
 type ASpecElement b =
   | Import ((SpecCalc.Term Position) * Spec * SpecElements)
   | Op QualifiedId
   | OpDef QualifiedId
   | Sort QualifiedId
   | SortDef QualifiedId
   | Property (AProperty b)
   | Comment String

 type SpecElement  = ASpecElement  StandardAnnotation
 type SpecElements = ASpecElements StandardAnnotation

 op  propertyElement?: [a] ASpecElement a -> Boolean
 def propertyElement? p =
   case p of
     | Property _ -> true
     | _ -> false

 op  sameSpecElement?: [a] ASpecElement a * ASpecElement a -> Boolean
 def sameSpecElement?(e1,e2) =
   case e1 of
     | Import(_,s1,_) ->
       (case e2 of
	 | Import(_,s2,_) -> s1 = s2
	 | _ -> false)
     | Property p1 ->
	(case e2 of
	 | Property p2 -> propertyName p1 = propertyName p2
	 | _ -> false)
     | _ -> e1 = e2

 type AProperty   a = PropertyType * PropertyName * TyVars * ATerm a
 type PropertyType  = | Axiom | Theorem | Conjecture
 type AProperties a = List(AProperty a)
 type Property      = AProperty   StandardAnnotation
 type Properties    = AProperties StandardAnnotation
 
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

  op opInfoAllDefs : [b] AOpInfo b -> List (ATerm b) 
 def opInfoAllDefs info =
   case info.dfn of
     | And (tms, _) -> tms
     | tm           -> [tm]

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

 %%% Qualification flag
 op qualifiedSpec?: [a] ASpec a -> Boolean
 op markQualified:  [a] ASpec a -> ASpec a
 op markUnQualified:  [a] ASpec a -> ASpec a
 
 def qualifiedSpec? spc = spc.qualified?
 def markQualified  spc = spc << {qualified? = true}
 def markUnQualified  spc = spc << {qualified? = false}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 %%% Can't make mapSpec polymorphic because elements in imports have to be Standard

 type TSP_Maps_St = TSP_Maps StandardAnnotation
  op mapSpec : TSP_Maps_St -> Spec -> Spec
 def mapSpec tsp {sorts, ops, elements, qualified?} =
   {
    %importInfo   = importInfo,
    sorts        = mapSpecSorts    tsp sorts,
    ops          = mapSpecOps      tsp ops,
    elements     = mapSpecProperties tsp elements,
    qualified?   = qualified?
   }

  op mapSpecSorts : [b] TSP_Maps b -> ASortMap b -> ASortMap b 
 def mapSpecSorts tsp sorts =
   mapSortInfos (fn info -> info << {dfn = mapSort tsp info.dfn})
                sorts

  op mapSpecOps : [b] TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOps tsp ops =
   mapOpInfos (fn info -> info << {dfn = mapTerm tsp info.dfn})
              ops

 %%% Only map over unqualified ops (for use in qualify)
 op  mapSpecUnqualified : TSP_Maps_St -> Spec -> Spec
 def mapSpecUnqualified tsp {sorts, ops, elements, qualified?} =
   {
    %importInfo   = importInfo,
    sorts        = mapSpecSorts tsp sorts,
    ops          = mapSpecOpsUnqualified tsp ops,
    elements     = mapSpecProperties tsp elements,
    qualified?   = qualified?
   }

 op  mapSpecOpsUnqualified : [b] TSP_Maps b -> AOpMap b -> AOpMap b
 def mapSpecOpsUnqualified tsp ops =
   mapOpInfosUnqualified (fn info ->
			  info << {dfn = mapTerm tsp info.dfn,
				   fullyQualified? = true})
              ops

 %% Useful if we know the defs from qualified specs won't be affected
 op  mapOpInfosUnqualified : [b] (AOpInfo b -> AOpInfo b) -> AOpMap b -> AOpMap b 
 def mapOpInfosUnqualified opinfo_map ops =
   foldriAQualifierMap 
     (fn (q, id, info, new_map) ->
      if primaryOpName? (q, id, info) && ~(info.fullyQualified?) then
	%% When access is via a primary alias, update the info and 
	%% record that (identical) new value for all the aliases.
	let new_info = opinfo_map info
	in
	foldl (fn (Qualified (q, id), new_map) ->
	       insertAQualifierMap (new_map, q, id, new_info))				   
	      new_map
	      info.names
      else
	%% For the non-primary aliases, do nothing,
	%% since they are handled derivatively above.
	new_map)
     ops
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

  op mapSpecProperties : TSP_Maps StandardAnnotation -> SpecElements -> SpecElements 
 def mapSpecProperties tsp elements =
   map (fn el ->
	case el of
	  | Property(pt, nm, tvs, term) -> Property(pt, nm, tvs, mapTerm tsp term)
	  | Import (s_tm,i_sp,elts) -> Import (s_tm,i_sp,mapSpecProperties tsp elts)
	  | _ -> el)
       elements

 op  mapSpecElements: (SpecElement -> SpecElement) -> SpecElements -> SpecElements
 def mapSpecElements f elements =
   map (fn el ->
	case el of
	  | Import (s_tm,i_sp,elts) -> f(Import (s_tm,i_sp,mapSpecElements f elts))
	  | _ -> f el)
     elements

 op  mapPartialSpecElements: (SpecElement -> Option SpecElement) -> SpecElements -> SpecElements
 def mapPartialSpecElements f elements =
   mapPartial
     (fn el ->
      case f el of
	| Some(Import (s_tm,i_sp,elts)) ->
	  Some(Import (s_tm,i_sp,mapPartialSpecElements f elts))
	| new_el -> new_el)
     elements

 op  filterSpecElements: (SpecElement -> Boolean) -> SpecElements -> SpecElements
 def filterSpecElements p elements =
   mapPartial
     (fn el ->
      if ~(p el) then None
	else 
	  Some(case el of
		 | Import (s_tm,i_sp,elts) ->
		   Import (s_tm,i_sp,filterSpecElements p elts)
		 | _ ->  el))
     elements


 op  foldlSpecElements: [a] (SpecElement * a -> a) -> a -> SpecElements -> a
 def foldlSpecElements f ini els =
   foldl (fn (el,result) ->
	  case el of
	    | Import (s_tm,i_sp,elts) ->
	      let result1 = foldlSpecElements f (f(el,result)) elts in
	      f(el,result1)
	    | _ -> f(el,result))
     ini els

 op  foldrSpecElements: [a] (SpecElement * a -> a) -> a -> SpecElements -> a
 def foldrSpecElements f ini els =
   foldr (fn (el,result) ->
	  case el of
	    | Import (s_tm,i_sp,elts) ->
	      let result1 = foldrSpecElements f result elts in
	      f(el,result1)
	    | _ -> f(el,result))
     ini els

 op  mapFoldrSpecElements: [a] (SpecElement * a -> a) -> a -> SpecElements -> a
 def mapFoldrSpecElements f ini els =
   foldr (fn (el,result) ->
	  case el of
	    | Import (s_tm,i_sp,elts) ->
	      let result1 = mapFoldrSpecElements f result elts in
	      f(el,result1)
	    | _ -> f(el,result))
     ini els

 op  existsSpecElement?: (SpecElement -> Boolean) -> SpecElements -> Boolean
 def existsSpecElement? p els =
   foldrSpecElements (fn (el,result) -> result || p el) false els

 %% Just removes duplicate imports although could also remove other duplicate elements
 %% but this would be more expensive and maybe not that helpful
 op  removeDuplicateImports: Spec -> Spec
 def removeDuplicateImports spc =
   let def mapEls(els,imports) =
         case els of
	   | [] -> ([],imports)
	   | el::r_els ->
	     (case el of
	       | Import (s_tm,i_sp,s_els) ->
		 if member(i_sp,imports)
		   then mapEls(r_els,imports)
		   else let (reduced_s_els,imports) = mapEls(s_els,imports) in
		        let (reduced_els,  imports) = mapEls(r_els,Cons(i_sp,imports)) in
			(Cons(Import (s_tm,i_sp,reduced_s_els),reduced_els),imports)
	       | _ ->
		 let (reduced_els,imports) = mapEls(r_els,imports) in
		 (Cons(el,reduced_els),imports))
   in
   let (reduced_els,_) = mapEls(spc.elements,[]) in
   spc << {elements = reduced_els}

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 type appTSP_St = appTSP StandardAnnotation

  op appSpec    : appTSP_St -> Spec -> ()
 def appSpec tsp_apps spc = 
   (
    appSpecOps        tsp_apps spc.ops;
    appSpecSorts      tsp_apps spc.sorts; 
    appSpecElements   tsp_apps spc.elements
   )

  op appSpecSorts : [a] appTSP a -> ASortMap a -> ()
 def appSpecSorts tsp sorts = 
   appAQualifierMap (fn info -> appSort tsp info.dfn) sorts 
    
  op appSpecOps : [a] appTSP a -> AOpMap a -> ()
 def appSpecOps tsp ops =
   appAQualifierMap (fn info -> appTerm tsp info.dfn) ops
    
  op appSpecElements :  appTSP_St -> SpecElements -> ()
 def appSpecElements tsp elements =
    app (fn  el ->
	 case el of
	  | Property(_, _, _, term) -> appTerm tsp term
	  | Import (_,_,elts) -> appSpecElements tsp elts
	  | _ -> ())
        elements

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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op emptySpec         : [a] ASpec         a
 op emptyImports      : Imports
 op emptyAElements    : [a] ASpecElements   a
 op emptyASortMap     : [a] AQualifierMap a
 op emptyAOpMap       : [a] AQualifierMap a
 op initialSpecInCat  : [a] ASpec         a

 %% Create new spec with altered name, imports, sorts, ops, elements, etc.

% op setImportInfo    : [a] ASpec a * ImportInfo       -> ASpec a
 op setImports       : [a] ASpec a * Imports          -> ASpec a
 op setLocalOps      : [a] ASpec a * OpNames          -> ASpec a
 op setLocalSorts    : [a] ASpec a * SortNames        -> ASpec a
 op setLocalElements : [a] ASpec a * PropertyNames    -> ASpec a
 op setSorts         : [a] ASpec a * ASortMap    a    -> ASpec a
 op setOps           : [a] ASpec a * AOpMap      a    -> ASpec a
 op setElements      : [a] ASpec a * ASpecElements a  -> ASpec a
 op appendElement    : [a] ASpec a * ASpecElement a   -> ASpec a
 op prependElement   : [a] ASpec a * ASpecElement a   -> ASpec a
 op addElementAfter  : [a] ASpec a * ASpecElement a * ASpecElement a -> ASpec a


 % substract the ops and sorts in the second argument from those
 % appearing in the first.
 op subtractSpec        :      Spec -> Spec -> Spec
 op subtractLocalSpecElements: [a] ASpec a * ASpec a -> ASpec a
 op subtractSpecProperties:    Spec * Spec -> Spec


 op someSortAliasIsLocal? : [b] Aliases * ASpec b -> Boolean
 op someOpAliasIsLocal?   : [b] Aliases * ASpec b -> Boolean

 op getQIdIfOp: [a] ASpecElement a -> Option QualifiedId

 op localOp?          : [a] QualifiedId * ASpec a -> Boolean
 op localSort?        : [a] QualifiedId * ASpec a -> Boolean
 op localProperty?    : [a] QualifiedId * ASpec a -> Boolean
 op localProperties   : [a] ASpec a -> AProperties a
 op allProperties     : Spec -> Properties
 op localOps          : [a] ASpec a -> List QualifiedId
 op hasLocalOp?       : [a] ASpec a -> Boolean
 op localSorts        : [a] ASpec a -> List QualifiedId
 op hasLocalSort?     : [a] ASpec a -> Boolean
 op localImports      : [a] ASpec a -> Imports


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyImports       = []
 def [a] emptyAElements = []
 def emptyASortMap      = emptyAQualifierMap
 def emptyAOpMap        = emptyAQualifierMap
% def emptyImportInfo    = {imports      = emptyImports,
%			   localOps     = emptyOpNames,
%			   localSorts   = emptySortNames,
%			   localProperties = emptyPropertyNames}

 def emptySpec = 
  {%importInfo     = emptyImportInfo,
   sorts          = emptyASortMap,
   ops            = emptyAOpMap,
   elements       = emptyAElements,
   qualified?     = true}

 def initialSpecInCat = 
  {%importInfo     = emptyImportInfo,  
   sorts          = emptyASortMap,   
   ops            = emptyAOpMap,     
   elements       = emptyAElements,
   qualified?     = true}

% def setImports       (spc, new_imports)     =
%   spc << {importInfo = spc.importInfo << {imports         = new_imports}}
% def setLocalOps      (spc, new_local_ops)   =
%   spc << {importInfo = spc.importInfo << {localOps        = new_local_ops}}
% def setLocalSorts    (spc, new_local_sorts) =
%   spc << {importInfo = spc.importInfo << {localSorts      = new_local_sorts}}
% def setLocalElements (spc, new_local_props) =
%   spc << {importInfo = spc.importInfo << {localProperties = new_local_props}}

% def setImportInfo (spc, new_import_info) = spc << {importInfo = new_import_info}
 def setSorts   (spc, new_sorts)    = spc << {sorts      = new_sorts}
 def setOps     (spc, new_ops)      = spc << {ops        = new_ops}
 def setElements(spc, new_elements) = spc << {elements = new_elements}

 def appendElement  (spc, new_element) = spc << {elements = spc.elements ++ [new_element]}
 def prependElement (spc, new_element) = spc << {elements = Cons(new_element,spc.elements)}
 def addElementAfter(spc, new_element, old_element) =
   spc << {elements = let elts = spc.elements in
	              let i = index(elts,old_element) in
		      take(i,elts) ++ [new_element] ++ drop(i,elts)}

 def someOpAliasIsLocal? (aliases, spc) =
   exists (fn el ->
	   case el of
	     | Op qid    -> member(qid,aliases)
	     | OpDef qid -> member(qid,aliases)
	     | _ -> false)
     spc.elements
 
 def someSortAliasIsLocal? (aliases, spc) =
   exists (fn el ->
	   case el of
	     | Sort qid    -> member(qid,aliases)
	     | SortDef qid -> member(qid,aliases)
	     | _ -> false)
     spc.elements
    
 def getQIdIfOp el =
   case el of
     | Op qid    -> Some qid
     | OpDef qid -> Some qid
     | _ -> None

 def localOp?       (qid, spc) = exists (fn el ->
					  case el of
					   | Op qid1    -> qid = qid1
					   | OpDef qid1 -> qid = qid1
					   | _ -> false)
                                   spc.elements
 def localSort?     (qid, spc) = exists (fn el ->
					  case el of
					   | Sort qid1    -> qid = qid1
					   | SortDef qid1 -> qid = qid1
					   | _ -> false)
                                   spc.elements
 def localProperty? (qid, spc) = exists (fn el ->
					  case el of
					   | Property (_,qid1,_,_) -> qid = qid1
					   | _ -> false)
                                   spc.elements

 def localProperties spc =
    mapPartial (fn el ->
		case el of
		  | Property p -> Some p
		  | _ -> None)
       spc.elements

 def localOps  spc =
    removeDuplicates(mapPartial (fn el ->
				 case el of
				   | Op qid -> Some qid
				   | OpDef qid -> Some qid
				   | _ -> None)
		       spc.elements)

 def localSorts  spc =
    removeDuplicates(mapPartial (fn el ->
				 case el of
				   | Sort qid -> Some qid
				   | SortDef qid -> Some qid
				   | _ -> None)
		       spc.elements)


 def allProperties spc =
   foldrSpecElements (fn (el,result) ->
		      case el of
		       | Property p -> Cons(p,result)
		       | _ -> result)
     []
     spc.elements

 def hasLocalOp? spc =
   exists (fn el ->
	   case el of
	     | Op _    -> true
	     | OpDef _ -> true
	     | _ -> false)
     spc.elements

 def hasLocalSort? spc =
   exists (fn el ->
	   case el of
	     | Sort _    -> true
	     | SortDef _ -> true
	     | _ -> false)
     spc.elements

 def localImports spc =
   mapPartial (fn el ->
	       case el of
		 | Import(sp_tm,sp,_) -> Some(sp_tm,sp)
		 | _ -> None)
     spc.elements


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
     %% various other routines assume that any
     %% unqualified answer will be listed first 
     found ++ filter (fn info -> ~(member (info, found)))
                     (wildFindUnQualified (spc.sorts, id))
   else 
     found
 
 def findAllOps (spc, Qualified (q, id)) =
   let found = (case findAQualifierMap (spc.ops, q, id) of
		  | Some info -> [info]
		  | None           -> [])
   in
   if q = UnQualified then
     %% various other routines assume that any
     %% unqualified answer will be listed first 
     found ++ filter (fn info -> ~(member (info, found)))
                     (wildFindUnQualified (spc.ops, id))
   else
     found

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

  op  mapDiffSorts : [a] ASortMap a -> ASortMap a -> ASortMap a
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
    {%importInfo = x.importInfo,
     elements = filterSpecElements (fn el ->
				    (case el of
				      | Import(_,i_sp,_) -> ~(i_sp = y)
				      | _ -> true)
				    && ~(existsSpecElement? (fn el2 -> sameSpecElement?(el2, el))
						 y.elements))
		   x.elements,
     ops      = mapDiffOps   x.ops   y.ops,
     sorts    = mapDiffSorts x.sorts y.sorts,
     qualified? = x.qualified?}

  def subtractSpecProperties(spec1, spec2) =
    let spec2PropNames = foldrSpecElements (fn (el,result) ->
					    case el of
					      | Property(_, pn, _, _) -> Cons(pn,result)
					      | _ -> result)
                           []
			   spec2.elements
    in
    let newElements =
        filterSpecElements (fn el ->
			    case el of
			      | Property(_, pn, _, _) -> ~(member(pn, spec2PropNames))
			      | _ -> ~(existsSpecElement? (fn el2 -> sameSpecElement?(el2, el))
				         spec2.elements))
	  spec1.elements
    in
    {
     %importInfo = spec1.importInfo,
     elements = newElements,
     ops   = spec1.ops,
     %ops   = mapDiffOps spec1.ops spec2.ops,
     sorts = spec1.sorts,
     %sorts = mapDiffSorts spec1.sorts spec2.sorts
     qualified? = spec1.qualified?
   }
 
  def subtractLocalSpecElements(spec1, spec2) =
    let spec2PropNames = mapPartial (fn el ->
				     case el of
				       | Property(_, pn, _, _) -> Some pn
				       | _ -> None)
          spec2.elements
    in
    let newElements =
        filter (fn el ->
		case el of
		  | Property(_, pn, _, _) -> ~(member(pn, spec2PropNames))
		  | _ -> ~(member(el, spec2.elements)))
	  spec1.elements
    in
    {
     %importInfo = spec1.importInfo,
     elements = newElements,
     ops   = spec1.ops,
     %ops   = mapDiffOps spec1.ops spec2.ops,
     sorts = spec1.sorts,
     %sorts = mapDiffSorts spec1.sorts spec2.sorts
     qualified? = spec1.qualified?
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
   setElements (spc, spc.elements ++ imported_spec.elements)


endspec
