% derived from SW4/Languages/MetaSlang/ADT/Specs/ASpec.sl v1.5
% derived from SW4/Languages/MetaSlang/ADT/Specs/ASpecSig.sl v1.2

AnnSpec qualifying spec {
 import Position
 import ../AbstractSyntax/AnnTerm   
 import /Library/Legacy/DataStructures/StringMapSplay % for qualifier maps

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                SpecRef
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %%  This is a bit of a hack for now.
 %%  A SpecRef is a string which if parsed and evaluated will yield a spec

 sort SpecRef = String % a bit of a hack -- emulate URI

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Note:  ASpec refers to ImportedSpecs, which refers to Spec, which is
 %%        an instance of ASpec.

 %% StandardAnnotation is the annotation of fully resolved specs and terms
 %% i.e., sorts Spec, Term, Sort etc. Currently it is just Unit but
 %% conceivably it could be more interesting in the future.


 sort StandardAnnotation = Position	% was ()

 sort Spec = ASpec StandardAnnotation

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ASpec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Spec    = ASpec StandardAnnotation
 %%% PosSpec = ASpec Position

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

 sort Imports = List Import
 sort Import  = SpecRef * Spec

 sort ASortMap  b = AQualifierMap (ASortInfo b) % Qualifier -> Id -> info
 sort AOpMap    b = AQualifierMap (AOpInfo   b) % Qualifier -> Id -> info

 sort ASortInfo b = SortNames * TyVars * Option (ASort b) 
 sort SortNames   = List QualifiedId 

 sort AOpInfo   b = OpNames * Fixity * ASortScheme b * Option (ATerm b) 
 sort OpNames     = List QualifiedId 

 sort AProperties   b  = List (AProperty b) 
 sort AProperty     b  = PropertyType * PropertyName * TyVars * ATerm b
 sort PropertyType     = | Axiom | Theorem | Conjecture
 sort PropertyName     = String
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 sort ASpecs b = List (ASpec b)

 sort AOpSignature  b = String * String * TyVars * ASort b
 sort SortSignature   = String * String * TyVars 

 sort ASortScheme   b = TyVars * ASort b

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                AQualifierMap
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % AQualifierMap implemented as nested StringMap
 % Assumes implementation of Qualifier and Id as Strings
 sort AQualifierMap b  = StringMap (StringMap b)    

 %% op findStringMap: fa(a) String * StringMap(StringMap a) -> StringMap a
 %% def findStringMap (id, dm) =
 %%  case find (dm, id) of
 %%     | None   -> StringMap.empty
 %%     | Some m -> m

 op foldriAQualifierMap : fa(a,b) (Qualifier * Id * a * b -> b) -> b
                                   -> (AQualifierMap a) -> b
 op emptyAQualifierMap  : fa(a) AQualifierMap a
 op findAQualifierMap   : fa(a) AQualifierMap a * Qualifier * Id -> Option a 
 op insertAQualifierMap : fa(a) AQualifierMap a * Qualifier * Id * a
                                 -> AQualifierMap a 
 op mapAQualifierMap    : fa(a,b) (a -> b)  -> AQualifierMap a -> AQualifierMap b
 op mapiAQualifierMap   : fa(a,b) (Qualifier * Id * a -> b)  -> AQualifierMap a
                                  -> AQualifierMap b
 op appAQualifierMap    : fa(a)   (a -> ()) -> AQualifierMap a -> ()
 op qualifiers          : fa(a) AQualifierMap a -> List Qualifier

 % Currently implemented as nested StringMap

 def foldriAQualifierMap = StringMap.foldriDouble  % f ini qm
 def emptyAQualifierMap  = StringMap.empty         % 
 def findAQualifierMap   = StringMap.find2         % (m, x, y)
 def insertAQualifierMap = StringMap.insert2       % (qm, x, y, v)
 def mapAQualifierMap    = StringMap.mapDouble     % f m
 def mapiAQualifierMap   = StringMap.mapiDouble     % f m
 def appAQualifierMap    = StringMap.appDouble     % f m
 def qualifiers m =
    StringMap.foldri (fn(qname,_,quals) -> cons(qname,quals)) [] m

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 op mapSpec    : fa(b) TSP_Maps b -> ASpec b -> ASpec b

 def mapSpec tsp_maps {importInfo, sorts, ops, properties} =
  {
   importInfo       = importInfo,

   ops              = mapAQualifierMap 
                       (fn (aliases, fixity, (tvs, srt), opt_def) -> 
			   (aliases, fixity, (tvs, mapSort tsp_maps srt), 
			    mapTermOpt tsp_maps opt_def))
		       ops,

   sorts            = mapAQualifierMap 
                        (fn (aliases, tvs, opt_def) -> 
                            (aliases, tvs, mapSortOpt tsp_maps opt_def))
                        sorts,

   properties       = map (fn (pt, nm, tvs, term) -> 
                              (pt, nm, tvs, mapTerm tsp_maps term))
                          properties
   }


 op mapTermOpt    : fa(b) TSP_Maps b -> Option (ATerm b) -> Option (ATerm b)
 def mapTermOpt tsp_maps opt_term = 
  case opt_term
    of None      -> None
     | Some term -> Some (mapTerm tsp_maps term)

 op mapSortOpt    : fa(b) TSP_Maps b -> Option (ASort b) -> Option (ASort b)
 def mapSortOpt tsp_maps opt_sort =
  case opt_sort
    of None     -> None
     | Some srt -> Some (mapSort tsp_maps srt)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 op appSpec    : fa(a) appTSP a -> ASpec a    -> ()

 def appSpec tsp spc = 
  let appt  = appTerm    tsp in
  let appto = appTermOpt tsp in
  let apps  = appSort    tsp in
  let appso = appSortOpt tsp in
  (appAQualifierMap
     (fn (op_names, fixity, (tvs,srt), opt_def) -> (apps srt ; appto opt_def))
     spc.ops ;
   appAQualifierMap
     (fn (sort_names, tvs, opt_def) -> appso opt_def)
     spc.sorts ;
   app
     (fn (_, nm, tvs, term) -> appt term)
     spc.properties)

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
 def equalSortInfo?((sortNames1,tyvs1,optDef1),(sortNames2,tyvs2,optDef2)) =
   sortNames1 = sortNames2
     & tyvs1 = tyvs2
     %% Could take into account substitution of tyvs
     & equalOpt?(optDef1,optDef2,equalSort?)

 op equalOpInfo?: fa(a) AOpInfo a * AOpInfo a -> Boolean
 def equalOpInfo?((opNames1,fixity1,sortsch1,optDef1),
		  (opNames2,fixity2,sortsch2,optDef2)) =
   opNames1 = opNames2
     & fixity1 = fixity2
     & equalSortScheme?(sortsch1,sortsch2)
     & equalOpt?(optDef1,optDef2,equalTerm?)

 op equalSortScheme?: fa(a) ASortScheme a * ASortScheme a -> Boolean
 def equalSortScheme?((tyvs1,def1),(tyvs2,def2)) =
   tyvs1 = tyvs2
     %% Could take into account substitution of tyvs
     & equalSort?(def1,def2)


 % --------------------------------------------------------------------------------
 % get the sort/op names as list of strings

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

 op setImports          : fa(a) ASpec a * Imports          -> ASpec a
 op setImportedSpec     : fa(a) ASpec a * Spec             -> ASpec a
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
 def fa (b) emptyAProperties = []
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

 def setImports ({importInfo = {imports, importedSpec, localOps, localSorts},
                  sorts, ops, properties},
                 new_imports) =
  {importInfo       = {imports      = new_imports,
                       importedSpec = importedSpec,
                       localOps     = localOps,
                       localSorts   = localSorts},
   sorts            = sorts,
   ops              = ops,
   properties       = properties}

 def setImportedSpec ({importInfo = {imports, importedSpec, localOps, localSorts},
                       sorts, ops, properties},
                      new_imported_spec) =
  {importInfo       = {imports      = imports,
                       importedSpec = Some new_imported_spec,
                       localOps     = localOps,
                       localSorts   = localSorts},
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

 def addImport ((spec_ref, imported_spec), spc) =
  setImports    (spc, cons ((spec_ref, imported_spec), spc.importInfo.imports))

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
}
