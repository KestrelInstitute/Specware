\section{Demodulation}
\begin{spec}
Demod qualifying
spec
  import /Library/Legacy/DataStructures/NatMapSplay
  import TermIndex 

    sort demod a = 
	 {index : TermIndex.index,
	  idMap : NatMap.Map a }

    op empty     : fa(a) demod a
    op isEmpty   : fa(a) demod a -> Boolean

    op listRules : fa(a) demod a -> List a
    op addRule   : fa(a) Term * a * demod a -> demod a
    op addRules  : fa(a) List (Term * a) * demod a -> demod a
    op getRules  : fa(a) demod a * Term -> List a
 
\end{spec}
  Demodulation structure for maintaining rewrite rules and 
  applying them.

\begin{spec}


    def empty = 
	 {index = TermIndex.empty,
	  idMap = NatMap.empty}

    def isEmpty({idMap,index=_}) = 0 = NatMap.numItems idMap

    def listRules({index=_,idMap}) = NatMap.listItems idMap

    def addRule (term,rule,{index,idMap}) = 
	let newId = (NatMap.numItems idMap) + 1 in
	{idMap = NatMap.insert(idMap,newId,rule),
         index = TermIndex.indexTerm (index,term,newId)}

   def addRules(rules,demod) = 
       foldr 
	(fn((trm,rule),demod) -> addRule(trm,rule,demod))	
	    demod rules

   def getRules ({idMap,index},term) = 
       let cands = TermIndex.generalizations (index,term) in
       mapPartial (fn i -> NatMap.find(idMap,i)) cands

endspec (* spec Demod *)

\end{spec}









