(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

% synchronized with version 1.1.1.1 of SW4/Languages/MetaSlang/TypeChecker/Infix.sl

(* Resolve infixe operators     *)

Infix qualifying spec 
 import Utilities

 type FixatedTerm = | Infix   MSTerm *  (Associativity * Precedence)
                    | Nonfix  MSTerm

 op resolveInfixes : Option LocalEnv * (MSTerm -> FixatedTerm) * Position * MSTerms -> MSTerm

 %    fun printTagged(Nonfix t) = TextIO.print("Nonfix "^AstPrint4.printTerm t^"\n")
 %      | printTagged(Infix(t,(assoc,p))) = 
 %        TextIO.print("Infix "^
 %                     AstPrint4.printTerm t^" "^
 %                     (case assoc of Left => "left " | Right => "right ")^
 %                     Int.toString p^"\n")

 (* 
  This scans a list of terms and reparses it according to 
  infixes and precedence of those.
  All infixes associate to the right.
  *)

%%  resolveInfixes is invoked by the typechecker here,
%%  but also by convertToMMTerm in ~/Work/Generic/Planware/Sources/CodeGen/,
%%  which is invoked directly from the parser semantic routines.
%%  That makes it awkward to provide a plausible environment for the message,
%%  so for now, revert to fail when there are problems while parsing.
 def resolveInfixes(opt_env,tagTermWithInfixInfo,pos,terms) = 
   let def local_error str =
	case opt_env of
	  | Some env -> error (env, str, pos)
	  | _ -> fail str
   in
   let def applyInfix(t1,infOp,t2) = ApplyN([infOp,mkTuple([t1,t2])],pos) in
   let def applyPrefixes(terms) = 
	 case terms of
	   | [] -> []
	   | [t] -> [t]
	   | (Nonfix t)::(Nonfix t2)::tags -> 
		  applyPrefixes(Cons(Nonfix(ApplyN([t,t2],pos)),tags))
	   | t::tags -> Cons (t,applyPrefixes tags)
   in
   let tagged = map tagTermWithInfixInfo terms in
   let tagged = applyPrefixes tagged in
   let 
     def scan (delta0,terms) : List FixatedTerm = 
       case terms of
	 | [Nonfix(t1)] -> [Nonfix(t1)]
	 | [Infix(t,_)] -> [Nonfix(t)]
	 | [] -> (local_error (printAll pos^" : No terms to apply"); [])
	 | (Infix(t,p)) :: rest ->  
	   (%local_error ("Infix "^printTerm t ^" given without left argument");
	    scan (delta0,applyPrefixes([Nonfix t] ++ rest)))
	 | (Nonfix(t1)) :: (Infix(infix1,(a1,delta1))) :: rest -> 
	   let rest = scan(delta1,rest) in
	   if delta0 > delta1 || (delta0 = delta1 && a1 = Left) then
	     %% The prior infix operator binds tighter than the first one here,
	     %%  or binds the same and we're left-associating.
	     %% Just return the existing list, and a subsequent re-scan will 
	     %%  see the prior infix operator as the first, and the first one 
	     %%  here as the second, which will be handled below.
	     Cons(Nonfix(t1),Cons(Infix(infix1,(a1,delta1)),rest))
	   else
	     %% The first infix operator here (infix1) binds tighter than the 
	     %%  prior infix operator.
	     (case rest of
		| (Nonfix t2)::(Infix(infix2,(a2,delta2)))::(Nonfix t3)::rest -> 
		  if delta1 > delta2 || (delta1 = delta2 && a1 = Left) then
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
		 | _ -> (local_error ("Missing right operand near infix operator "^printTerm infix1);
			 [Nonfix(t1)]))

	 | (Nonfix _)::(Nonfix _)::_ ->
	      (local_error ("Unreduced nonfix"); [head terms])
  in
   let def scanrec(tagged) = 
	 case scan(0,tagged) of
	   | [Nonfix t] -> t
	   | [Nonfix t1,Infix(infix1,(a1,delta1)),Nonfix t2] -> applyInfix(t1,infix1,t2)
		 %% Need special case for Left, 0 to avoid infinite recursion
	   | (Nonfix t1 )::(Infix(infix1,(Left,0)))::rest ->
		   applyInfix(t1,infix1,scanrec(rest))
	   | tagged -> scanrec tagged
   in
   let term = scanrec(tagged) in
   term
endspec
