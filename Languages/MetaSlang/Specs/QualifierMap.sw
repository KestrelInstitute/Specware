(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AQualifierMapType =
AnnSpec qualifying
spec
 type AQualifierMap b
endspec  

QualifierMap =
AnnSpec qualifying
spec
 import AQualifierMapType
 type MetaSlang.Id        = String
 type MetaSlang.Ids       = List Id
 type MetaSlang.Qualifier = Id
 %type SpecCalc.Monad a
 type SpecCalc.Env a
 %% From /Languages/SpecCalculus/Semantics/Environment
 %type Env a = State -> (Result a) * State

 op foldriAQualifierMap      : [a,b] (Qualifier * Id * a * b -> b) -> b -> (AQualifierMap a) -> b
 op emptyAQualifierMap       : [a] AQualifierMap a
 op findAQualifierMap        : [a] AQualifierMap a * Qualifier * Id -> Option a 

 op removeAQualifierMap      : [a] AQualifierMap a * Qualifier * Id     -> AQualifierMap a
 op insertAQualifierMap      : [a] AQualifierMap a * Qualifier * Id * a -> AQualifierMap a 

 op mapAQualifierMap         : [a,b]                  (a -> b)        -> AQualifierMap a -> AQualifierMap b
 op mapiAQualifierMap        : [a,b] (Qualifier * Id * a -> b)        -> AQualifierMap a -> AQualifierMap b
 op mapiPartialAQualifierMap : [a,b] (Qualifier * Id * a -> Option b) -> AQualifierMap a -> AQualifierMap b

 op appAQualifierMap         : [a]                  (a -> ()) -> AQualifierMap a -> ()
 op appiAQualifierMap        : [a] (Qualifier * Id * a -> ()) -> AQualifierMap a -> ()

 op qualifiers               : [a] AQualifierMap a -> List Qualifier
 op qualifierIds             : [a] AQualifierMap a -> List Id

 op equalAQualifierMap?      : [a] AQualifierMap a * AQualifierMap a -> Bool
 op subsetAQualifierMap?     : [a] AQualifierMap a * AQualifierMap a -> Bool

 op foldOverQualifierMap :
    [a,b] (Qualifier * Id * a * b -> SpecCalc.Env b)
         -> b
         -> (AQualifierMap a)
         -> SpecCalc.Env b
 %%  find all the matches to id in every second level map
 op wildFindUnQualified : [a] AQualifierMap a * Id -> List a

endspec
