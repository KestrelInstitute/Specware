spec
 sort MetaSlang.Id = String
 sort MetaSlang.Qualifier = Id
 sort AQualifierMap b
 %sort SpecCalc.Monad a
 sort SpecCalc.Env a
 %% From /Languages/SpecCalculus/Semantics/Environment
 %sort Env a = State -> (Result a) * State

 op foldriAQualifierMap : fa(a,b) (Qualifier * Id * a * b -> b) -> b
                                   -> (AQualifierMap a) -> b
 op emptyAQualifierMap  : fa(a) AQualifierMap a
 op findAQualifierMap   : fa(a) AQualifierMap a * Qualifier * Id -> Option a 
 op removeAQualifierMap   : fa(a) AQualifierMap a * Qualifier * Id -> AQualifierMap a
 op insertAQualifierMap : fa(a) AQualifierMap a * Qualifier * Id * a
                                  -> AQualifierMap a 
 op mapAQualifierMap    : fa(a,b) (a -> b)  -> AQualifierMap a -> AQualifierMap b
 op mapiAQualifierMap   : fa(a,b) (Qualifier * Id * a -> b)  -> AQualifierMap a
                                  -> AQualifierMap b
 op mapiPartialAQualifierMap : fa(a,b) (Qualifier * Id * a -> Option b)
                                  -> AQualifierMap a
                                  -> AQualifierMap b
 op appAQualifierMap    : fa(a) (a -> ()) -> AQualifierMap a -> ()
 op qualifiers          : fa(a) AQualifierMap a -> List Qualifier
 op qualifierIds        : fa(a) AQualifierMap a -> List Id

 op equalAQualifierMap?  : fa(a) AQualifierMap a * AQualifierMap a -> Boolean
 op subsetAQualifierMap? : fa(a) AQualifierMap a * AQualifierMap a -> Boolean

 op foldOverQualifierMap :
    fa(a,b) (Qualifier * Id * a * b -> SpecCalc.Env b)
         -> b
         -> (AQualifierMap a)
         -> SpecCalc.Env b
endspec
