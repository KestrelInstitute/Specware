(* Demodulation *)

Demod qualifying
spec
  import /Library/Legacy/DataStructures/NatMapSplay
  import TermIndex 

   type Demod a = 
        {index : TermIndex.index,
         idMap : NatMap.Map a }

   op empty     : [a] Demod a
   op isEmpty   : [a] Demod a -> Boolean

   op numRules  : [a] Demod a -> Nat
   op listRules : [a] Demod a -> List a
   op addRule   : [a] MS.Term * a * Demod a -> Demod a
   op addRules  : [a] List (MS.Term * a) * Demod a -> Demod a
   op getRules  : [a] Demod a * MS.Term -> List a
   op mergeRules  : [a] Demod a * Demod a -> Demod a

(*  Demodulation structure for maintaining rewrite rules and 
    applying them. *)

   def empty = {index = TermIndex.empty,
                idMap = NatMap.empty}

   def isEmpty({idMap,index=_}) = 0 = NatMap.numItems idMap

   def listRules({index=_,idMap}) = NatMap.listItems idMap

   def addRule (term,rule,{index,idMap}) = 
       let newId = (NatMap.numItems idMap) + 1 in
       {idMap = NatMap.insert(idMap,newId,rule),
        index = TermIndex.indexTerm (index,term,newId)}

   def addRules(rules,demod) = 
       foldl 
	(fn((trm,rule),demod) -> addRule(trm,rule,demod))	
	    demod rules

   def getRules ({idMap,index},term) = 
       let cands = TermIndex.generalizations (index,term) in
       mapPartial (fn i -> NatMap.find(idMap,i)) cands

   def numRules{index = _,idMap} = NatMap.numItems idMap

   def mergeRules(rls1,rls2) =
     if numRules rls1 > numRules rls2
       then mergeRules1(rls2,rls1)
       else mergeRules1(rls1,rls2)

   op  mergeRules1  : [a] Demod a * Demod a -> Demod a
   def mergeRules1({index = index1,idMap = idMap1},{index = index2,idMap = idMap2}) =
     let size2 = NatMap.numItems idMap2 in
     % ids are 0 to n-1 so to convert i -> i + size2 to get 
     let index1inc = incrementIndices(index1,size2) in
     {idMap = NatMap.foldri (fn (key,val,m) -> NatMap.insert(m,key+size2,val))
                idMap2 idMap1,
      index = mergeDiscNets(index1inc,index2)}
     
   op  incrementIndices: TermIndex.index * Nat -> TermIndex.index
   def incrementIndices((s,m),i) =
     (IntegerSet.map (fn v -> v+i) s,
      foldri (fn (key,val,new_m) -> insert(new_m,key,incrementIndices(val,i)))
        TermDiscNet.empty m)

endspec (* spec Demod *)






