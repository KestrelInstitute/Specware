AnnSpec qualifying spec 
 import Position
%  import ../AbstractSyntax/AnnTerm   
 import MSTerm
 import QualifierMapAsSTHashTable
 import SpecCalc


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Note:  ASpec refers to ImportedSpecs, which refers to Spec, which is
 %%        an instance of ASpec.

 %% StandardAnnotation is the annotation of fully resolved specs and terms
 %% i.e., sorts Spec, Term, Sort etc. Currently it is just Unit but
 %% conceivably it could be more interesting in the future.


 % sort StandardAnnotation = Position	% was ()

 sort Spec = ASpec StandardAnnotation

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ASpec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 sort ASpec b = 
  {
   importInfo   : ImportInfo,		%  not used in equality test on specs
   sorts        : ASortMap    b,
   ops          : AOpMap      b,
   properties   : AProperties b
  }

 sort ImportInfo = {imports      : Imports,
		    importedSpec : Option Spec, % Not currently used?
		    localOps     : OpNames,
		    localSorts   : SortNames}

 sort Aliases = List QualifiedId 

 sort Imports = List Import
 sort Import  = (SpecCalc.Term Position) * Spec

 sort ASortMap  b = AQualifierMap (ASortInfo b) % Qualifier -> Id -> info
 sort AOpMap    b = AQualifierMap (AOpInfo   b) % Qualifier -> Id -> info

 sort ASortInfo b = SortNames * TyVars * ASortSchemes b 
 sort SortNames   = Aliases

 sort AOpInfo   b = OpNames * Fixity * ASortScheme b * ATermSchemes b 
 sort OpNames     = Aliases

 sort AProperties   b  = List (AProperty b) 
 sort AProperty     b  = PropertyType * PropertyName * TyVars * ATerm b
 sort PropertyType     = | Axiom | Theorem | Conjecture
 sort PropertyName     = String
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 sort ASpecs b = List (ASpec b)

 sort AOpSignature  b = String * String * TyVars * ASort b
 sort SortSignature   = String * String * TyVars 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 op mapSpec    : fa(b) TSP_Maps b -> ASpec b -> ASpec b

 def mapSpec tsp_maps {importInfo, sorts, ops, properties} =
  {
   importInfo       = importInfo,

   ops              = mapAQualifierMap 
                       (fn (aliases, fixity, (tvs, srt), defs) -> 
			   (aliases, fixity, (tvs, mapSort tsp_maps srt), 
			    mapTermSchemes tsp_maps defs))
		       ops,

   sorts            = mapAQualifierMap 
                        (fn (aliases, tvs, defs) -> 
                            (aliases, tvs, mapSortSchemes tsp_maps defs))
                        sorts,

   properties       = map (fn (pt, nm, tvs, term) -> 
                              (pt, nm, tvs, mapTerm tsp_maps term))
                          properties
   }


 op mapTermSchemes : fa(b) TSP_Maps b -> ATermSchemes b -> ATermSchemes b
 def mapTermSchemes tsp_maps term_schemes = 
  map (fn (type_vars, term) -> (type_vars, mapTerm tsp_maps term)) term_schemes

 op mapSortSchemes : fa(b) TSP_Maps b -> ASortSchemes b -> ASortSchemes b
 def mapSortSchemes tsp_maps sort_schemes =
  map (fn (type_vars, srt) -> (type_vars, mapSort tsp_maps srt)) sort_schemes

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

(* ### unused?
 op appSpec    : fa(a) appTSP a -> ASpec a    -> ()

 def appSpec tsp spc = 
  let appt  = appTerm        tsp in
  let appts = appTermSchemes tsp in
  let apps  = appSort        tsp in
  let appss = appSortSchemes tsp in
  (appAQualifierMap
     (fn (op_names, fixity, (tvs,srt), defs) -> (apps srt ; appts defs))
     spc.ops ;
   appAQualifierMap
     (fn (sort_names, tvs, defs) -> appss defs)
     spc.sorts ;
   app
     (fn (_, nm, tvs, term) -> appt term)
     spc.properties)
*)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Sorts, Ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op specSorts : fa(b) ASpec b -> List SortSignature
 op specOps   : fa(b) ASpec b -> List (AOpSignature b)

 def specSorts (spc) = 
  foldriAQualifierMap (fn (qualifier, name, (sort_names, tyVars, opt_def), 
                          result) -> 
                         cons ((qualifier, name, tyVars), result)) 
                     [] spc.sorts 

 def specOps (spc) = 
  foldriAQualifierMap (fn (qualifier, name, (op_names, fixity, (tyVars, srt), opt_def),
                          result) -> 
                         cons ((qualifier, name, tyVars, srt), result))
                     [] spc.ops 

 % --------------------------------------------------------------------------------
 % return sorts/ops as list with entries of the form (qualifier, id, info)

 op sortsAsList     : fa(b) ASpec b -> List (Qualifier * Id * ASortInfo b)
 op opsAsList       : fa(b) ASpec b -> List (Qualifier * Id * AOpInfo   b)
 op sortInfosAsList : fa(b) ASpec b -> List (ASortInfo b)
 op opInfosAsList   : fa(b) ASpec b -> List (AOpInfo   b)

 def sortsAsList(spc) =
  foldriAQualifierMap (fn (qualifier, id, sort_info, new_list) -> 
                         cons ((qualifier, id, sort_info), new_list))
                     [] spc.sorts

 def sortInfosAsList(spc) =
  foldriAQualifierMap (fn (_(* qualifier *), _(* id *), this_sort_info, new_list) -> 
		       %% there could be multiple entries to the same sortInfo
		       if exists (fn old_info -> equalSortInfo? (old_info, this_sort_info)) new_list then
			 new_list
		       else
                         cons (this_sort_info, new_list))
                      [] spc.sorts

 def opsAsList(spc) =
  foldriAQualifierMap (fn (qualifier, id, op_info, new_list) -> 
                         cons ((qualifier, id, op_info), new_list))
                     [] spc.ops

 def opInfosAsList(spc) =
  foldriAQualifierMap (fn (_(* qualifier *), _(* id *), this_op_info, new_list) -> 
		       %% there could be multiple entries to the same opInfo
		       if exists (fn old_info -> equalOpInfo? (old_info, this_op_info)) new_list then
			 new_list
		       else
                         cons (this_op_info, new_list))
                      [] spc.ops

 op equalSortInfo?: fa(a) ASortInfo a * ASortInfo a -> Boolean
 def equalSortInfo?((sortNames1,tyvs1,defs1),(sortNames2,tyvs2,defs2)) =
   sortNames1 = sortNames2
     & tyvs1 = tyvs2
     %% Could take into account substitution of tyvs
     & all (fn def1 -> 
	    exists (fn def2 -> equalSortScheme? (def1, def2)) 
	           defs2) 
           defs1


 op equalOpInfo?: fa(a) AOpInfo a * AOpInfo a -> Boolean
 def equalOpInfo?((opNames1,fixity1,sortsch1,defs1),
		  (opNames2,fixity2,sortsch2,defs2)) =
   opNames1 = opNames2
     & fixity1 = fixity2
     & equalSortScheme?(sortsch1,sortsch2)
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

 % --------------------------------------------------------------------------------
 % get the sort/op names as list of strings
(* ### Unused?
 op sortNames : fa(b) ASpec b -> List String
 op opNames   : fa(b) ASpec b -> List String

 def sortNames spc =
  foldriAQualifierMap (fn (_, sort_name, _, new_list) -> 
                         List.concat (new_list, [sort_name]))
                     [] spc.sorts

 def opNames spc =
  foldriAQualifierMap (fn (_, op_name, _, new_list) -> 
                         List.concat (new_list, [op_name])) 
                     [] spc.ops
*)

 op emptyOpNames: OpNames
 def emptyOpNames = []

 op emptySortNames: SortNames
 def emptySortNames = []

 op memberNames: QualifiedId * List QualifiedId -> Boolean
 def memberNames(n,nms) = member(n,nms)

 op memberQualifiedId:  Qualifier * Id * List QualifiedId -> Boolean
 def memberQualifiedId(qualifier,id,qids) =
   exists (fn (Qualified(q,i)) -> q = qualifier & i = id) qids

 op addToNames: QualifiedId * List QualifiedId -> List QualifiedId 
 def addToNames(name,nameSet) = cons(name,nameSet)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 op emptySpec           : fa(a) ASpec         a
 op emptyImports        : Imports
 op emptyAProperties    : fa(a) AProperties   a
 op emptyASortMap       : fa(a) AQualifierMap a
 op emptyAOpMap         : fa(a) AQualifierMap a

 %% Create new spec with altered name, imports, sorts, ops, properties, etc.

 op setImportInfo       : fa(a) ASpec a * ImportInfo       -> ASpec a
 op setImports          : fa(a) ASpec a * Imports          -> ASpec a
 op setImportedSpec     : fa(a) ASpec a * Spec             -> ASpec a
 op setLocalOps         : fa(a) ASpec a * OpNames          -> ASpec a
 op setLocalSorts       : fa(a) ASpec a * SortNames        -> ASpec a
 op setSorts            : fa(a) ASpec a * ASortMap    a    -> ASpec a
 op setOps              : fa(a) ASpec a * AOpMap      a    -> ASpec a
 op setProperties       : fa(a) ASpec a * AProperties a    -> ASpec a

 % substract the ops and sorts in the second argument from those
 % appearing in the first.
 op subtractSpec : fa (a) ASpec a -> ASpec a -> ASpec a

 %% Create new spec with added sort, op, property, import, etc.

 op addImport           : fa(a) Import * ASpec a -> ASpec a

 %% old style...
%%% The following havebeen replaced with monadic versions in
%%% SpecCalculus/Semantics/Evaluate/Spec/Utilitites

%%% op addSort             : fa(a) (Qualifier * Id * 
%%%                                 TyVars * Option(ASort a)) * 
%%%                                 ASpec a -> ASpec a
%%%
%%% %% new style...
%%% op addAliasedSort      : fa(a) (Qualifier * Id * 
%%%                                  SortNames * TyVars * Option (ASort a)) * 
%%%                                ASpec a -> ASpec a
%%%
%%% %% old style...
%%% op addOp               : fa(a) (Qualifier * Id * 
%%%                                 Fixity * ASortScheme a * Option (ATerm a)) * 
%%%                                ASpec a -> ASpec a
%%%
%%% %% new style...
%%% op addAliasedOp        : fa(a) (Qualifier * Id * 
%%%                                 OpNames * Fixity * ASortScheme a * Option (ATerm a)) * 
%%%                                ASpec a -> ASpec a


 op addProperty         : fa(a) (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom            : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjecture       : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheorem          : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheoremLast      : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjectures      : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addTheorems         : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a

 op addLocalSortName    : fa(a) ASpec a * QualifiedId -> ASpec a
 op addLocalOpName      : fa(a) ASpec a * QualifiedId -> ASpec a

 op localOp?            : fa(a) QualifiedId * ASpec a -> Boolean
 op localSort?          : fa(a) QualifiedId * ASpec a -> Boolean



 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyImports            = []
 def fa (a) emptyAProperties = []
 def emptyASortMap           = emptyAQualifierMap
 def emptyAOpMap             = emptyAQualifierMap
 def emptyImportInfo         = {imports      = emptyImports,
                                importedSpec = None,
                                localOps     = emptyOpNames,
                                localSorts   = emptySortNames}

 def emptySpec = 
  {importInfo       = emptyImportInfo,
   sorts            = emptyASortMap,
   ops              = emptyAOpMap,
   properties       = emptyAProperties}

 def setImportInfo ({importInfo=_, sorts, ops, properties}, 
		    new_import_info) =
  {importInfo       = new_import_info,
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setImports ({importInfo = {imports=_, importedSpec, localOps, localSorts},
                  sorts, ops, properties},
                 new_imports) =
  {importInfo       = {imports      = new_imports,
                       importedSpec = importedSpec,
                       localOps     = localOps,
                       localSorts   = localSorts},
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setImportedSpec ({importInfo = {imports, importedSpec=_, localOps, localSorts},
                       sorts, ops, properties},
                      new_imported_spec) =
  {importInfo       = {imports      = imports,
                       importedSpec = Some new_imported_spec,
                       localOps     = localOps,
                       localSorts   = localSorts},
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setLocalOps ({importInfo = {imports, importedSpec, localOps=_, localSorts},
		   sorts, ops, properties},
		  new_local_ops) =
  {importInfo       = {imports      = imports,
                       importedSpec = importedSpec,
                       localOps     = new_local_ops,
                       localSorts   = localSorts},
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setLocalSorts ({importInfo = {imports, importedSpec, localOps, localSorts=_},
		     sorts, ops, properties},
		    new_local_sorts) =
  {importInfo       = {imports      = imports,
                       importedSpec = importedSpec,
                       localOps     = localOps,
                       localSorts   = new_local_sorts},
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setSorts (spc, new_sorts) =
  {importInfo       = spc.importInfo,
   sorts            = new_sorts,
   ops              = spc.ops,
   properties       = spc.properties}

 def setOps (spc, new_ops) =
  {importInfo       = spc.importInfo,
   sorts            = spc.sorts,
   ops              = new_ops,
   properties       = spc.properties}

 def setProperties (spc, new_properties) =
  {importInfo       = spc.importInfo,
   sorts            = spc.sorts,
   ops              = spc.ops,
   properties       = new_properties}

 % ------------------------------------------------------------------------

 def addImport ((specCalcTerm, imported_spec), spc) =
  setImports    (spc, cons ((specCalcTerm, imported_spec), spc.importInfo.imports))

 def addProperty (new_property, spc) =
  setProperties (spc, cons (new_property, spc.properties))

 def addAxiom       ((name, type_vars, formula), spc) =
  addProperty ((Axiom      : PropertyType, name, type_vars, formula), spc) 

 def addConjecture  ((name, type_vars, formula), spc) =
  addProperty ((Conjecture : PropertyType, name, type_vars, formula), spc) 
 
 def addTheorem     ((name, type_vars, formula), spc) =
  addProperty ((Theorem    : PropertyType, name, type_vars, formula), spc) 

 def addTheoremLast ((name, type_vars, formula), spc) =
  setProperties (spc, 
                 spc.properties ++ [(Theorem : PropertyType, name, type_vars, formula)])

 def addConjectures (conjectures, spc) = foldr addConjecture spc conjectures
 def addTheorems    (theorems,    spc) = foldr addTheorem    spc theorems
 def addLocalSortName (spc as {importInfo = {imports, importedSpec, localOps, localSorts},
                               sorts, ops, properties},
                       new_local_sort) =
   if memberNames(new_local_sort,localSorts)
     then spc
     else {importInfo = {imports      = imports,
                         importedSpec = importedSpec,
                         localOps     = localOps,
                         localSorts   = addToNames(new_local_sort,localSorts)},
           sorts      = sorts,
           ops        = ops,
           properties = properties}

 def addLocalOpName (spc as {importInfo = {imports, importedSpec, localOps, localSorts},
                             sorts, ops, properties},
                     new_local_op) =
   if memberNames(new_local_op,localOps)
     then spc
     else {importInfo = {imports      = imports,
                         importedSpec = importedSpec,
                         localOps     = addToNames(new_local_op,localOps),
                         localSorts   = localSorts},
           sorts      = sorts,
           ops        = ops,
           properties = properties}

 def localOp?(Qualified(qualifier,op_name),
	      spc as {importInfo = {imports, importedSpec, localOps, localSorts},
		      sorts, ops, properties})
   = memberQualifiedId(qualifier,op_name,localOps)

 def localSort?(Qualified(qualifier,sort_name),
	      spc as {importInfo = {imports, importedSpec, localOps, localSorts},
		      sorts, ops, properties})
   = memberQualifiedId(qualifier,sort_name,localSorts)

 op findTheSort  : fa(a) ASpec a * QualifiedId -> Option (ASortInfo a)  
 op findTheOp    : fa(a) ASpec a * QualifiedId -> Option (AOpInfo   a)

 op findAllSorts : fa(a) ASpec a * QualifiedId -> List (ASortInfo a)
 op findAllOps   : fa(a) ASpec a * QualifiedId -> List (AOpInfo   a)

 def findTheSort (spc, Qualified (qualifier,id)) =
  %% We're looking for precisely one sort,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (spc.sorts, qualifier, id)

 def findTheOp (spc, Qualified (qualifier,id)) =
  %% We're looking for precisely one op,
  %% which we might have specified as being unqualified.
  %% (I.e., unqualified is not a wildcard here.)
  findAQualifierMap (spc.ops, qualifier, id)


  %% Overloading is not particularly meaningful for sorts. 
 %% (Would we ever want both  FOO.FOO x and FOO.FOO x y  as distinct sorts?)
 %% but we might have two or more sorts X.S, Y.S, etc.
 %% If the qualifier is UnQualified then we return unqualified answer first so as to
 %% give preference to it because there is no other way to refer to this entry.
 %% Note that checkSort depends on this behavior.
 def findAllSorts (spc, Qualified (qualifier,id)) =
  let found = (case findAQualifierMap (spc.sorts, qualifier, id) of
                | Some sort_info -> [sort_info]
		| None           -> [])
  in
  if qualifier = UnQualified
    then found
       ++ filter (fn op_info -> ~(member(op_info,found)))
             (wildFindUnQualified (spc.sorts, id))
    else found
 
 def findAllOps (spc, Qualified (qualifier,id)) =
  if qualifier = UnQualified then
    wildFindUnQualified (spc.ops, id)
  else
    case findAQualifierMap (spc.ops, qualifier, id) of
     | Some op_info -> [op_info]
     | None         -> []
		
 %%  find all the matches to id in every second level map
 op wildFindUnQualified : fa (a) AQualifierMap a * Id -> List a
 def wildFindUnQualified (qualifier_map, id) =
   foldriAQualifierMap (fn (_, mId, val, results) ->
			if id = mId
			 then Cons(val,results)
			 else results)
     []
     qualifier_map

 % this next one is use only in substract spec. it cannot be defined inside
 % the scope of subtractSpec as there is no let-polymorphism in Specware
 op mapDiff : fa (a) AQualifierMap a -> AQualifierMap a -> AQualifierMap a
 def mapDiff xMap yMap =
     foldriAQualifierMap (fn (qual,id,info,newMap) ->
       case findAQualifierMap (yMap,qual,id) of
         | None -> insertAQualifierMap (newMap,qual,id,info)
         | Some _ -> newMap) emptyAQualifierMap xMap

 def subtractSpec x y = {
     importInfo = x.importInfo,
     properties = foldl (fn (x,l) ->
           if member (x,y.properties) then
             l
           else
             Cons (x,l)) [] x.properties,
     ops = mapDiff x.ops y.ops,
     sorts = mapDiff x.sorts y.sorts
   }

(* ### unused
 op addDisjointImport: Spec * Spec -> Spec
 def addDisjointImport (spc, imported_spec) =
   let def mergeSortStep (imported_qualifier, imported_id,
			  imported_sort_info, combined_psorts) =
        insertAQualifierMap (combined_psorts,
			      imported_qualifier,
			      imported_id,
			      imported_sort_info)
       def mergeOpStep (imported_qualifier, imported_id,
			imported_op_info, combined_pops) =
	 insertAQualifierMap (combined_pops,
			      imported_qualifier,
			      imported_id,
			      imported_op_info)
	   
   in
   let spc = addImport (("", imported_spec), spc) in
   let newSorts = foldriAQualifierMap mergeSortStep spc.sorts imported_spec.sorts in
   let spc = setSorts (spc, newSorts) in
   let newOps = foldriAQualifierMap mergeOpStep spc.ops imported_spec.ops in
   let spc = setOps (spc, newOps) in
   setProperties (spc,  spc.properties ++ imported_spec.properties)
*)
endspec
