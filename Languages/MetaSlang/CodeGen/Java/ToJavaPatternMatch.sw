JGen qualifying spec

import ../../Transformations/PatternMatch

(* Utilities for translating the output of the pattern-match compiler to Java.
A case statement gets translated to a TranslationBuiltIn.block which provides a scope for 
TranslationBuiltIn.mkSuccess to return from. At the top level if there is a coproduct 
dispatch without an otherwise case then methods are generated for the cases.
Within a TranslationBuiltIn.failWith an if ... then ... else TranslationBuiltIn.break 
translates to if ... then ....
TranslationBuiltIn.mkFail (for when no case applies) translates to an error.00 

*)

op  translateMatchJava: Spec -> Spec
def translateMatchJava spc =
  let spc = translateMatch spc in
  mapSpec (fn t -> case t of
	             | Let([(VarPat(v,_),vt as (Apply(Fun(Select _,_,_),_,_)))], body, _) ->
	               substitute(body,[(v,vt)])
		     | _ -> t,
	   id,id)
    spc

op  parseCoProductCase: MS.Term -> Option(MS.Term * List (Id * MS.Term) * Option MS.Term)

def parseCoProductCase term =
  let def makeCases(id,case_tm,then_exp,els_exp) =
        let def parseRest t =
	      case t of
		| IfThenElse(Apply(Fun(Embedded id,srt,_),case_tm1,_),
			     then_exp,els_exp, _)  ->
		  if equalTerm?(case_tm,case_tm1)
		    then let (cases,otherwise_tm) = parseRest els_exp in
			 (Cons((id,then_exp),cases),otherwise_tm)
		    else ([],Some t)
		| Fun (Op (Qualified ("TranslationBuiltIn", "mkBreak"), _), _, _) ->
		  ([],None)		% No otherwise case
		| _ -> ([],Some t)
	in
	let (cases,otherwise_tm) = parseRest els_exp in
	Some(case_tm,Cons((id,then_exp),cases),otherwise_tm)
  in
  case term of
    | Apply (Fun (Op (Qualified ("TranslationBuiltIn", "block"), _), _, _),
	      Apply (Fun (Op (Qualified ("TranslationBuiltIn", "failWith"), _), _, _),
		     IfThenElse(Apply(Fun(Embedded id,srt,_),case_tm,_),
				then_exp, els_exp, _), _), _) ->
      makeCases(id,case_tm,then_exp,els_exp)
    | IfThenElse(Apply(Fun(Embedded id,srt,_),case_tm,_),
		 then_exp, els_exp, _) ->
      makeCases(id,case_tm,then_exp,els_exp)      
    | _ -> None

%op  coProductCase?: Term * Boolean -> Boolean

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
