\section{Term indexing}

 Implementation of path indexing, as described in Stickel's report,
 using a discrimination net to compute the getTerms functions.

 Reference: Mark E. Stickel,  The Path-Indexing Method for Indexing
 Terms, Technical Note 473, SRI International, October
 1989

 In OTTER 3.0, McCune writes (file fpa.c):
   \begin{quote}
   FPA indexing is used when searching for unifiable terms, as in inference
   rules and in unit conflict, and it is used when searching for instances,
   as in back subsumption.  (It can also be used when searching for
   more general terms, as in forward subsumption, demodulation,
   and unit-deletion, but discrimination tree indexing is usually better.)
   \end{quote}


To index a term, translate into an appropriate path, then
for each point in the path add the mapping symbol->term to
the corresponding node. This is done by adding symbol to the
end of the path; the set of terms will be at the node reached. 

How to distinguish positions from functions? Don't really have
to, since they are alternated; just give integer values to the
symbols, and it won't matter if some symbols have the same
value as a position. 



 SpecialFlag indicates if there are special function symbols under
 which indexing should not be done. isSpecial identifies these
 function symbols; if there are no special symbols, hopefully
 partial evaluation will optimize this away. 

\begin{spec}
TermIndex qualifying
spec
  import /Library/Legacy/Utilities/Lisp
  import TermDiscNet
  import ../Specs/StandardSpec

 sort index = TermDiscNet.disc_net

 op TermIndex.empty : index
 op indexTerm       : index * Term * Nat -> index
 op generalizations : index * Term -> List Nat

 def  TermIndex.empty = TermDiscNet.EmptyDiscNet

 sort sym_entry = | Star | S Nat

 op printPath: List Key -> ()
 def printPath path = 
     (app (fn i -> String.toScreen(Integer.toString i^" ")) path;
      String.writeLine "")

 def getApplys(M: Term,Ms) = 
     case M
       of Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_),Fun(Nat n,_,_),_) -> 
	  (cons(M,Ms),true)
	| Apply(M,M2,_) -> getApplys(M,cons(M2,Ms))
	| _ -> (cons(M,Ms),false)


 def getFunIndex = 
     fn (Fun(Op(qid,fixity),_,_):Term) -> 
	Lisp.uncell(Lisp.apply(Lisp.symbol("CL","SXHASH"),[Lisp.cell qid]))
      | _ -> 0

 def subterms = 
     fn [Record(fields,_)] -> List.map (fn (_,M) -> M) fields
      | Ms -> Ms 

 def indexTerm (index,term,id) = 
     let
	 def genPathSymPairs(prefix,M) = 
	     let (M::Ms,isFlex?) = getApplys(M,[]) in
		if isFlex?
		   then [prefix ++ [Integer.~ 1]]
		else
		let indexT = getFunIndex M in
		let Ms = subterms Ms in
                let
		    def getRec(i,ts) =
			case ts
			  of [] -> []
			   | t::ts -> 
			     genPathSymPairs(prefix ++ [indexT,i],t) ++
			     getRec(i + 1,ts)
		in
		    List.cons((prefix List.@ [indexT]),getRec(1,Ms))
		
	    def addOne(path,index) = 
		TermDiscNet.addForPath(index,path,id)
        in
        let pairs = genPathSymPairs([],term) in
	(%String.writeLine(MetaSlangPrint.printTerm term);
	 %List.app printPath pairs;
	 List.foldr addOne index pairs)
	

(* NOTE: To avoid conflicts with Star here, symToInt has to be non-negative.
 * This can be avoided with another constructor and defining an ordering
 * relation... But at expense of efficiency...
 *)

    def makePath(p,entry: sym_entry) = 
	case entry
	  of Star -> p ++ [Integer.~ 1]
	   | S x  -> p ++ [x]

    op  getTerms : TermDiscNet.disc_net * List Integer * sym_entry -> IntegerSet.Set

    def getTerms(index,p,r) = 
	case TermDiscNet.findForPath(index,makePath(p,r))
	  of Some set -> set
	   | None -> IntegerSet.empty

    def generalizations (index,term) = 
	let
	    def get(p,M:Term) = 
		let (M::Ms,isFlex?) = getApplys(M,[]) in
		if isFlex?
		   then getTerms(index,p,Star)
		else
		let subTerms = subterms Ms 		in
		let arity = length subTerms 	in
		let indexT = getFunIndex M 		in
		let set1     = getTerms(index,p,Star)	in
		let set2 = 
			if arity = 0 
			    then getTerms(index,p,S(indexT))
			else 
			    getList(p ++ [indexT],1,subTerms)
		in
		    IntegerSet.union(set1,set2)
	    def getList(path,i,terms) = 
		case terms
		  of [] -> IntegerSet.empty
		   | [term] -> get(path ++ [i],term)
		   | term::terms -> 
		     let set = get(path ++ [i],term) in
		    if IntegerSet.isEmpty set 
			then set 
		    else IntegerSet.intersection(set,getList(path,i + 1,terms))
	
	in
	    IntegerSet.listItems(get([],term))
	
endspec (* structure TermIndex *)
\end{spec}

