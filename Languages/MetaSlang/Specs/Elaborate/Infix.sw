(* Resolve infixe operators     *)

spec {
 import ../PosSpec
 import ../Printer % for error messages

 % def printTerm term = MetaSlangPrint4.printTerm(deleteTerm term)

 %% ========================================================================

 sort FixatedPTerm = | Infix   PTerm *  (Associativity * Precedence)
                     | Nonfix  PTerm

 %% ========================================================================

 op resolveInfixes : (PTerm -> FixatedPTerm) * Position * List(PTerm) -> PTerm

 %    fun printTagged(Nonfix t) = TextIO.print("Nonfix "^AstPrint4.printTerm t^"\n")
 %      | printTagged(Infix(t,(assoc,p))) = 
 %	TextIO.print("Infix "^
 %		     AstPrint4.printTerm t^" "^
 %		     (case assoc of Left => "left " | Right => "right ")^
 %		     Int.toString p^"\n")

 %% ========================================================================

 (* 
  This scans a list of terms and reparses it according to 
  infixes and precedence of those.
  All infixes associate to the right.
  *)

 def resolveInfixes(tagTermWithInfixInfo,pos,terms) = 
	let
	    def applyInfix(t1,infOp,t2) = 
		ApplyN([infOp,mkTuple([t1,t2])],pos)
        in
        let
	    def applyPrefixes(terms) = 
                case terms
	          of [] -> []
	           | [t] ->  [t]
	           | (Nonfix t)::(Nonfix t_)::tags -> 
		      applyPrefixes(cons(Nonfix(ApplyN([t,t_],pos)),tags))
	           | (t :: tags) -> cons(t,applyPrefixes(tags))
         in
         let tagged = map tagTermWithInfixInfo terms in
	 let tagged = applyPrefixes(tagged) in
         let 
	    def scan(delta0,terms) : List FixatedPTerm = 
	        case terms
	          of [Nonfix(t1)] -> [Nonfix(t1)]
	           | [Infix(t,_)] -> [Nonfix(t)]
	           | [] -> System.fail (printPosition pos^": No terms to apply")
	           | (Infix(t,p)) :: _ ->  
		     System.fail (printPosition pos^": Infix "^printTerm t ^" given without left argument")
	           | (Nonfix(t1)):: (Infix(infix1,(a1,delta1)))::rest -> 
		    let rest = scan(delta1,rest) in
		    if delta0 > delta1 or (delta0 = delta1 & a1 = Left) then
                    %% The prior infix operator binds tighter than the first one here,
                    %%  or binds the same and we're left-associating.
                    %% Just return the existing list, and a subsequent re-scan will 
                    %%  see the prior infix operator as the first, and the first one 
                    %%  here as the second, which will be handled below.
                    cons(Nonfix(t1),cons(Infix(infix1,(a1,delta1)),rest))
		    else
                    %% The first infix operator here (infix1) binds tighter than the 
                    %%  prior infix operator.
		    (case rest
		      of (Nonfix t2)::(Infix(infix2,(a2,delta2)))::(Nonfix t3)::rest -> 
			 if delta1 > delta2 or (delta1 = delta2 & a1 = Left) then
			 %% The first infix operator here also binds tighter than the second, 
                         %%  or it binds the same and we're left-associating.
			 [Nonfix(applyInfix(t1,infix1,t2)),
			  Infix(infix2,(a2,delta2)),
		          Nonfix(t3)] ++ rest
			 else 
			 %% The second infix operator here binds tighter than the first, 
                         %%  or it binds the same and we're right-associating.
                         %%  Because t3 might be followed by an infix operator binding 
                         %%  tighter than infix2, we must first scan from t3 on.
                         (case scan(delta2, [(Nonfix t3)] ++ rest) 
                            of (Nonfix new_t3)::new_rest ->
                               scan(delta0, 
                                    [Nonfix(t1),Infix(infix1,(a1,delta1)),
                                     Nonfix(applyInfix(t2,infix2,new_t3))] ++ new_rest))
		       | [Nonfix(t2)] -> 
                         %% As indicated above, the first infix operator here (infix1) 
                         %%  binds tighter than the prior infix operator.
			 [Nonfix(applyInfix(t1,infix1,t2))]
		       | _ -> System.fail (printPosition pos^": Infix "^printTerm infix1^
					  " given without left argument"))
		
	           | (Nonfix _) :: (Nonfix _) :: _ -> System.fail (printPosition pos^":Unreduced nonfix")
         in
         let
	    def scanrec(tagged) = 
		case scan(0,tagged)
		  of [Nonfix t] -> t
		   | [Nonfix(t1),Infix(infix1,(a1,delta1)),Nonfix(t2)] -> applyInfix(t1,infix1,t2)
		   %% Need special case for Left, 0 to avoid infinite recursion
	           | (Nonfix(t1)):: (Infix(infix1,(Left,0)))::rest ->
		     applyInfix(t1,infix1,scanrec(rest))
	           | tagged -> scanrec(tagged) 
         in
	 let term = scanrec(tagged) in
         term
}



