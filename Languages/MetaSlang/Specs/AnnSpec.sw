% derived from SW4/Languages/MetaSlang/ADT/Specs/ASpec.sl v1.5
% derived from SW4/Languages/MetaSlang/ADT/Specs/ASpecSig.sl v1.2

spec {
 import ../AbstractSyntax/AnnTerm   
 import /Library/Legacy/DataStructures/StringMapSplay % for qualifier maps

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                SpecRef
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %%  This is a bit of a hack for now.
 %%  A SpecRef is a string which if parsed and evaluated will yield a spec

 sort SpecRef = String % a bit of a hack -- emulate URI

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 %% Note:  ASpec refers to ImportedSpecs, which refers to Spec, which is
 %%        an instance of ASpec.

 %% StandardAnnotation is the annotation of fully resolved specs and terms
 %% i.e., sorts Spec, Term, Sort etc. Currently it is just Unit but
 %% conceivably it could be more interesting in the future.


 sort StandardAnnotation = ()

 sort Spec = ASpec StandardAnnotation

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ASpec
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% Spec    = Apsec StandardAnnotation
 %%% PosSpec = Apsec Position

 sort ASpec b = 
  {
   imports      : Imports,
   importedSpec : Option Spec,   % Used by type checker
   sorts        : ASortMap    b,
   ops          : AOpMap      b,
   properties   : AProperties b
  }

 %% ---------------------------------------------------------------------
 %%  imports : Imports = List Import = List (SpecRef * Spec)
 %% ---------------------------------------------------------------------

 sort Imports = List Import
 sort Import  = SpecRef * Spec

 %% ---------------------------------------------------------------------
 %% sorts  : ASortMap b = AQualifierMap (ASortInfo b)
 %% ops    : AOpMap   b = AQualifierMap (AOpInfo b)
 %% ---------------------------------------------------------------------

 sort ASortMap  b = AQualifierMap (ASortInfo b) % Qualifier -> Id -> info
 sort AOpMap    b = AQualifierMap (AOpInfo   b) % Qualifier -> Id -> info

 sort ASortInfo b = SortNames * TyVars * Option (ASort b) 
 sort SortNames   = List QualifiedId 

 sort AOpInfo   b = OpNames * Fixity * ASortScheme b * Option (ATerm b) 
 sort OpNames     = List QualifiedId 

 %% ---------------------------------------------------------------------
 %% properties : AProperties b  = List (AProperty b) 
 %% ---------------------------------------------------------------------

 sort AProperties   b  = List (AProperty b) 
 sort AProperty     b  = PropertyType * PropertyName * TyVars * ATerm b
 sort PropertyType     = | Axiom | Theorem | Conjecture
 sort PropertyName     = String
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 sort ASpecs b = List (ASpec b)

 sort AOpSignature  b = String * String * TyVars * ASort b
 sort SortSignature   = String * String * TyVars 

 sort ASortScheme   b = TyVars * ASort b

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                AQualifierMap
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP map over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%% "TSP" means "Term, Sort, Pattern"

 op mapSpec    : fa(b) TSP_Maps b -> ASpec b -> ASpec b

 def mapSpec tsp_maps {imports, importedSpec, sorts, ops, properties} =
  {
   imports          = imports,

   importedSpec     = importedSpec,

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

 def mapTermOpt tsp_maps opt_term = 
  case opt_term
    of None      -> None
     | Some term -> Some (mapTerm tsp_maps term)

 def mapSortOpt tsp_maps opt_sort =
  case opt_sort
    of None     -> None
     | Some srt -> Some (mapSort tsp_maps srt)

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Recursive TSP application over Specs
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Sorts, Ops
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

 op sortsAsList : fa(b) ASpec b -> List (Qualifier * Id * ASortInfo b)
 op opsAsList   : fa(b) ASpec b -> List (Qualifier * Id * AOpInfo   b)

 def sortsAsList(spc) =
  foldriAQualifierMap (fn (qualifier, id, sort_info, new_list) -> 
                         cons ((qualifier, id, sort_info), new_list))
                     [] spc.sorts

 def opsAsList(spc) =
  foldriAQualifierMap (fn (qualifier, id, op_info, new_list) -> 
                         cons ((qualifier, id, op_info), new_list))
                     [] spc.ops

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


 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                Spec Consructors
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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

 %% Create new spec with added sort, op, property, import, etc.

 op addImport           : fa(a) Import * ASpec a -> ASpec a

 %% old style...
 op addSort             : fa(a) (Qualifier * Id * 
                                 TyVars * Option(ASort a)) * 
                                 ASpec a -> ASpec a

 %% new style...
 op addAliasedSort      : fa(a) (Qualifier * Id * 
                                  SortNames * TyVars * Option (ASort a)) * 
                                ASpec a -> ASpec a

 %% old style...
 op addOp               : fa(a) (Qualifier * Id * 
                                 Fixity * ASortScheme a * Option (ATerm a)) * 
                                ASpec a -> ASpec a

 %% new style...
 op addAliasedOp        : fa(a) (Qualifier * Id * 
                                 OpNames * Fixity * ASortScheme a * Option (ATerm a)) * 
                                ASpec a -> ASpec a


 op addProperty         : fa(a) (AProperty a)                          * ASpec a -> ASpec a
 op addAxiom            : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjecture       : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheorem          : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addTheoremLast      : fa(a) (PropertyName * TyVars * ATerm a)      * ASpec a -> ASpec a
 op addConjectures      : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a
 op addTheorems         : fa(a) List (PropertyName * TyVars * ATerm a) * ASpec a -> ASpec a

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %%%                ImportedSpecs operations 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 def emptyImports            = []
 def fa (b) emptyAProperties = []
 def emptyASortMap           = emptyAQualifierMap
 def emptyAOpMap             = emptyAQualifierMap

 def emptySpec = 
  {imports          = emptyImports,
   importedSpec     = None,
   sorts            = emptyASortMap,
   ops              = emptyAOpMap,
   properties       = emptyAProperties}

 def setImports (spc, new_imports) =
  {imports          = new_imports,
   importedSpec     = spc.importedSpec,  % presumably None if we're still setting imports
   sorts            = spc.sorts,
   ops              = spc.ops,
   properties       = spc.properties}

 def setImportedSpec (spc, new_imported_spec) =
  {imports          = spc.imports,
   importedSpec     = Some new_imported_spec,
   sorts            = spc.sorts,
   ops              = spc.ops,
   properties       = spc.properties}

 def setSorts (spc, new_sorts) =
  {imports          = spc.imports,
   importedSpec     = spc.importedSpec,
   sorts            = new_sorts,
   ops              = spc.ops,
   properties       = spc.properties}

 def setOps (spc, new_ops) =
  {imports          = spc.imports,
   importedSpec     = spc.importedSpec,
   sorts            = spc.sorts,
   ops              = new_ops,
   properties       = spc.properties}

 def setProperties (spc, new_properties) =
  {imports          = spc.imports,
   importedSpec     = spc.importedSpec,
   sorts            = spc.sorts,
   ops              = spc.ops,
   properties       = new_properties}

 % ------------------------------------------------------------------------

 def addImport ((spec_ref, imported_spec), spc) =
  setImports    (spc, cons ((spec_ref, imported_spec), spc.imports))

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
}
