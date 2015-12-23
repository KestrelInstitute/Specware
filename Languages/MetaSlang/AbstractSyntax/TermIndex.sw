(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

(* Term indexing

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

sjw 8/22/2014
The representation described in the paper allows for a number of uses of this data structure.
We only use the "generalizations" feature. I have specialized it somewhat for this purpose in
the course of fixing a bug. It could be further specialized, which would be useful for
large rule sets.
*)

TermIndex qualifying
spec
  import /Library/Legacy/Utilities/Lisp
  import TermDiscNet
  import ../Specs/StandardSpec

 type Index = TermDiscNet.Disc_net

 op TermIndex.empty : Index
 op indexTerm       : Index * MSTerm * Nat -> Index
 op generalizations : Index * MSTerm -> List Nat

 def  TermIndex.empty = TermDiscNet.EmptyDiscNet

 type Sym_entry = | Star | SymS Int

 op printPath: List Key -> ()
 def printPath path = 
     (app (fn i -> toScreen(Integer.show i^" ")) path;
      writeLine "")

 def getApplys (M: MSTerm, Ms) = 
     case M
       of Apply (Fun(Op(Qualified (UnQualified,"%Flex"),_),_,_),Fun(Nat n,_,_),_) -> 
	  (M::Ms,true)
	| Apply(M,M2,_) -> getApplys(M,M2::Ms)
	| _ -> (M::Ms,false)


 def getFunIndex = 
     %% The only rule here is that different indices imply different terms.
     %% The precise values don't matter.
     %% And it's even ok if different terms have the same index (e.g., if
     %% sxhash should return 3) -- that just makes things slightly less
     %% efficient.
     fn (Fun(Op(qid,fixity),_,_)) ->
        if qid = Qualified (UnQualified,"%Flex")
          then 0
          else Lisp.uncell(Lisp.apply(Lisp.symbol("CL","SXHASH"),[Lisp.cell qid]))
      | (Fun(Embed(qid,_),   _,_)) -> Lisp.uncell(Lisp.apply(Lisp.symbol("CL","SXHASH"),[Lisp.cell qid]))
      | (Fun(Not,           _,_)) ->  1
      | (Fun(And,           _,_)) ->  2
      | (Fun(Or,            _,_)) ->  3
      | (Fun(Implies,       _,_)) ->  4
      | (Fun(Iff,           _,_)) ->  5
      | (Fun(Equals,        _,_)) ->  6 % was 1
      | (Fun(NotEquals,     _,_)) ->  7
      | (IfThenElse    (_,_,_,_)) ->  8 % was 2
      | (Bind (Forall,    _,_,_)) ->  9 % was 3
      | (Bind (Exists,    _,_,_)) -> 10 % was 4
      | (Bind (Exists1,   _,_,_)) -> 11 % was 4
      | Lambda _                  -> 12 % was 5
      | Let _                     -> 13 % was 6
      | LetRec _                  -> 14 % was 7
      | The _                     -> 15 
      | _ -> 0

 def subterms = 
     fn [Record(fields,_)] | length fields > 1 && (head fields).1 = "1" ->
              map (fn (_,M) -> M) fields
      | Ms -> Ms 

 def indexTerm (index,term,id) = 
     let
	 def genPathSymPairs(prefix,M) =
             % let _ = writeLine("genp: "^anyToString prefix^"\n"^printTerm M) in
	     let (M::Ms,isFlex?) = getApplys(M,[]) in
		if isFlex?
		   then [prefix ++ [-1]]
		else
		let indexT = getFunIndex M in
                if Ms = [] then [prefix ++ [indexT]]
                else
		let Mss = subterms Ms in
                let
		    def getRec(i,ts) =
			case ts
			  of [] -> []
			   | t::ts -> 
			     genPathSymPairs(prefix ++ [indexT,i],t) ++
			     getRec(i + 1,ts)
		in
		    (if length Mss = 1
                      then genPathSymPairs(prefix ++ [indexT], head Mss)
                      else getRec(1,Mss))
		
	    def addOne(index,path) = 
		TermDiscNet.addForPath(index,path,id)
        in
        let pairs = genPathSymPairs([],term) in
	(%writeLine("Term: "^printTerm term^"\nPairs: "^anyToString pairs);
	 %List.app printPath pairs;
	 foldl addOne index pairs)

    def makePath(p,entry: Sym_entry) = 
	case entry
	  of Star -> p
	   | SymS x  -> p ++ [x]

    op  getTerms : TermDiscNet.Disc_net * List Int * Sym_entry -> IntSet.Set

    def getTerms(index,p,r) = 
	case TermDiscNet.findForPath(index,makePath(p,r))
	  of Some node ->
            (case r of
               | Star -> allContents node
               | SymS _ -> contents node)
	   | None -> IntSet.empty

(* Old
    def generalizations (index,term) = 
	let
	    def get(p,M) = 
		let (M::Ms,isFlex?) = getApplys(M,[]) in
		if isFlex?
		   then getTerms(index,p,Star)
		else
		let subTerms = subterms Ms 		in
		let arity = length subTerms 	in
		let indexT = getFunIndex M 		in
		let set1     = getTerms(index,p,SymS (-1))	in
		let set2 = 
			if arity = 0 
			    then getTerms(index,p,SymS(indexT))
			else 
			    getList(p ++ [indexT],1,subTerms)
		in
		    IntSet.union(set1,set2)
	    def getList(path,i,terms) = 
		case terms
		  of [] -> IntSet.empty
		   | [term] -> get(path ++ [i],term)
		   | term::terms -> 
		     let set = get(path ++ [i],term) in
		    if IntSet.isEmpty set 
			then set 
		    else IntSet.intersection(set,getList(path,i + 1,terms))
	
	in
        IntSet.listItems(get([],term))
*)

    def generalizations (index,term) = 
	let
	    def get(p,M) =
                % let _ = writeLine("get: "^anyToString p^"\n"^printTerm M) in
		let (M::Ms,isFlex?) = getApplys(M,[]) in
		if isFlex?
		   then getTerms(index,p,Star)
		else
		let subTerms = subterms Ms in
		let arity = length subTerms in
		let indexT = getFunIndex M in
		let set1 = getTerms(index,p,SymS (-1)) in
		let set2 = 
		       (if arity = 0 
                          then getTerms(index,p,SymS(indexT))
                        else if arity = 1
                          then get(p ++ [indexT], head subTerms)
			else 
                          let p = p ++ [indexT] in
                          if length Ms = 1 then
                          let set_tup = getTerms(index,p,SymS (-1)) in
			  IntSet.union(set_tup, getList(p,1,subTerms))
                        else getList(p,1,subTerms))
		in
                IntSet.union(set1,set2)
	    def getList(path,i,terms) = 
		case terms
		  of [] -> IntSet.empty
		   | [term] -> get(path ++ [i],term)
		   | term::terms -> 
		     let set = get(path ++ [i],term) in
                     if IntSet.isEmpty set 
                       then set 
                     else IntSet.intersection(set,getList(path,i + 1,terms))
	in
        IntSet.listItems(get([],term))
	
end-spec
