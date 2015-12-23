(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

JGen qualifying spec

import /Languages/MetaSlang/CodeGen/Generic/PatternMatch

(* Utilities for translating the output of the pattern-match compiler to Java.
A case statement gets translated to a TranslationBuiltIn.block which provides a scope for 
TranslationBuiltIn.mkSuccess to return from. At the top level if there is a coproduct 
dispatch without an otherwise case then methods are generated for the cases.
Within a TranslationBuiltIn.failWith an if ... then ... else TranslationBuiltIn.break 
translates to if ... then ....
TranslationBuiltIn.mkFail (for when no case applies) translates to an error.00 

*)

(*
 * op  translateMatchJava: Spec -> Spec
 * def translateMatchJava spc =
 *   % opt_counter is added so Accord can avoid resetting counter over an accord program
 *   let spc = translateMatch spc in
 *   mapSpec (fn t -> case t of
 * 	             | Let([(VarPat(v,_),vt as (Apply(Fun(Select _,_,_),_,_)))], body, _) ->
 * 	               substitute(body,[(v,vt)])
 * 		     | _ -> t,
 * 	   id,id)
 *     spc
 *)

op  parseCoProductCase: Spec -> MSTerm -> Option(MSTerm * List (Id * MSTerm) * Option MSTerm * Bool)

def parseCoProductCase spc term =
  let def makeCases(id,case_tm,then_exp,els_exp,block?) =
        let def parseRest t =
	      case t of
		| IfThenElse(Apply(Fun(Embedded (Qualified(_,id)),srt,_),case_tm1,_),
			     then_exp,els_exp, _)  ->
		  if equivTerm? spc (case_tm,case_tm1)
		    then let (cases,otherwise_tm) = parseRest els_exp in
			 (Cons((id,simpSuccess (then_exp,block?)),cases),otherwise_tm)
		    else ([],Some (simpSuccess (t,block?)))
		| Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"), _), _, _) ->
		  ([],None)		% No otherwise case
		| _ -> ([],Some (simpSuccess(t,block?)))
	in
	let (cases,otherwise_tm) = parseRest els_exp in
	Some(case_tm,Cons((id,then_exp),cases),otherwise_tm,block?)
      def simpSuccess (tm,block?) =
	if block?
	  then case tm of
	         | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "mkSuccess"), _), _, _), s_tm,_) ->
	           s_tm
		 | IfThenElse(p,x,y,a) ->
		   IfThenElse(p,simpSuccess(x,block?),y,a)
		 | _ -> tm
	  else tm
  in
  case term of

    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "block"), _), _, _),
	     Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _, _),
		    Record([("1",IfThenElse(Apply(Fun(Embedded (Qualified(_,id)),srt,_),case_tm,_),
					    then_exp, els_exp, _)),
			    ("2",default)],_) , _), _)
      ->
      makeCases(id,case_tm,then_exp,simpSuccess(default,true),true)

    | IfThenElse(Apply(Fun(Embedded (Qualified(_,id)),srt,_),case_tm,_),
		 then_exp, els_exp, _) ->
      makeCases(id,case_tm,then_exp,els_exp,false)      

    %% A definition using IfThenElse such as this:
    %%   def null(l) = case l of [] -> true | _ -> false
    %% now may be optimized to a defintion using Embedded, such as this:
    %%   def null(l) = embed? Nil l
    | Apply(Fun(Embedded(Qualified(_,id)),srt,_),case_tm,_) ->
      Some(case_tm, [(id,mkTrue())], Some(mkFalse()), false)

    | _ -> None

%op  coProductCase?: Term * Bool -> Bool

%def coProductCase?(term,allowOtherwise?) =
  

%op caseTerm: (Term | caseTerm?) -> Term

%def caseTerm(term) =
%  let Apply (Lambda (match, _), trm, _) = term in
%    trm

%op caseCases: (Term | caseTerm?) -> Match
%def caseCases(trm) =
%  let  Apply (Lambda (match, _), trm, _) = trm in
%    match


endspec
