(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

ACL2 qualifying spec

import /Languages/SpecCalculus/AbstractSyntax/Types
import /Languages/MetaSlang/AbstractSyntax/AnnTerm
import /Library/PrettyPrinter/WadlerLindig
% import /Languages/MetaSlang/Specs/Printer
import /Languages/SpecCalculus/Semantics/Value
import /Languages/SpecCalculus/Semantics/Environment
 %import /Languages/SpecCalculus/Semantics/Monad
import /Languages/SpecCalculus/AbstractSyntax/ShowUtils
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements
import /Languages/MetaSlang/Transformations/Pragma
import /Library/Legacy/Utilities/System

% We use this throughout to thread through the possibility of an error.
% This makes the code pretty ugly; would have been nice to use some kind of monad, but
% perhaps not worth the hassle of actually figuring it out.
type PPError a = 
  | Good a
  | Bad String

% Map a function that can produce an error over a list.
% If there is an error on any individual element, lift that to an error for the whole
% function.
op [a, b] ppErrorMap : (a -> PPError b) -> List a -> PPError (List b)
def ppErrorMap f l =
  case l of
    | [] -> Good []
    | (x :: xs) -> 
      case (f x, ppErrorMap f xs) of
        | (Good y, Good ys) -> Good (y::ys)
        | (Bad s, _) -> Bad s
        | (_, Bad s) -> Bad s

% Zip together two lists with a function.
op [a,b,c] zipWith (f:(a * b -> c), l1:List a, l2:List b) : List c =
  case (l1,l2) of
    | ([],_)  -> []
    | (_,[])  -> []
    | (x::xs,y::ys) -> f (x, y) :: zipWith (f,xs,ys)

type Context = {printTypes?: Bool,
                printPositionInfo?: Bool,
                fileName: String,
                %currentUID: UnitId,
                %uidsSeen: List UnitId,	% Used to avoid infinite recursion because of circularity
                recursive?: Bool,
                showImportedSpecs? : Bool  %Can cause exponential blowup.  Recommend importing /Library/Base/Empty into the spec being shown if you set this to true
                }

op fileNameOfValue (value:Value) : Option String =
  case value of
    | Spec        spc           -> fileNameOfSpec spc
%      | Morph       spec_morphism -> ppMorphism c  spec_morphism
%      | SpecPrism   spec_prism    -> ppPrism     spec_prism     % tentative
%      | SpecInterp  spec_interp   -> ppInterp    spec_interp    % tentative
%      | Diag        spec_diagram  -> ppDiagram  c  spec_diagram
%      | Colimit     spec_colimit  -> ppColimit  c  spec_colimit
%      | Other       other_value   -> ppOtherValue other_value
%      | InProcess                 -> ppString "InProcess"
%      | UnEvaluated _             -> ppString "some unevaluated term"
    | _                         -> None

op fileNameOfSpec (spc:Spec) : Option String =
  case findLeftmost (fn el -> some?(fileNameOfSpecElement(el,spc))) spc.elements of
    | Some el -> fileNameOfSpecElement (el,spc)
    | None -> None

op fileNameOfSpecElement (el : SpecElement, spc : Spec) : Option String =
  case el of
    | Op       (qid, _,       _) -> fileNameOfOpId   (qid, spc)
    | OpDef    (qid, _, _,    _) -> fileNameOfOpId   (qid, spc)
    | Type     (qid,          _) -> fileNameOfTypeId (qid, spc)
    | TypeDef  (qid,          _) -> fileNameOfTypeId (qid, spc)
    | Property (_, _, _, trm, _) -> fileNameOfTerm   trm
    | _ -> None

op fileNameOfOpId(qid:QualifiedId, spc:Spec) : Option String =
  case findTheOp(spc,qid) of
    | Some {names=_,fixity=_,dfn,fullyQualified?=_} -> fileNameOfTerm dfn
    | _ -> None

op fileNameOfTypeId(qid:QualifiedId,spc:Spec) : Option String =
  case findTheType(spc,qid) of
    | Some {names=_,dfn} -> fileNameOfType dfn
    | _ -> None

op fileNameOfTerm (tm:MSTerm) : Option String =
  foldSubTerms (fn (t,val) ->
		  case val of
		    | Some _ -> val
		    | None ->
                      case termAnn t of
                        | File(nm,_,_) -> Some nm
                        | _ -> None)
  None tm

op fileNameOfType (s:MSType) : Option String =
  case typeAnn s of
    | File(nm,_,_) -> Some nm
    | _ -> None

op ppGrConcat (x:List WLPretty) : WLPretty = ppNest 0 (ppConcat x) % ppGroup (ppConcat x)
op ppGr1Concat (x:List WLPretty) : WLPretty = ppNest 1 (ppConcat x)
op ppGr2Concat (x:List WLPretty) : WLPretty = ppNest 2 (ppConcat x)
op ppNum (n:Int) : WLPretty = ppString(show n)
op ppSpace : WLPretty = ppString " "
op ppSpaceBreak : WLPretty = ppConcat[ppSpace, ppBreak]

%% THE BELOW CODE IS PROBABLY NOT RELEVANT %%
% Abstract types, no definitions.
op ppType (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      Good (ppConcat [ppString "((", ppString id, ppString " *) => *)"])
    | _ -> Bad "Bad argument to ppType (really bad)"

op ppTypeLocalDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Type (qid, pos) -> 
      let Qualified (q, id) = qid in
      Good (ppConcat [ppString "(local (defun ", ppString id, ppString " (x) (declare (ignore x)) t))"])
    | _ -> Bad "Bad argument to ppTypeLocalDef (really bad)"
%% THE ABOVE CODE IS PROBABLY NOT RELEVANT %%

% Print the name of this type (base types, booleans, type variables, and subtypes)
op ppTypeName (spc:Spec) (t:MSType) : PPError WLPretty = 
  case t of
    | Base (Qualified (_, pid),actuals as (_::_),_) ->
      (case ppErrorMap (ppTypeName spc) actuals of
         | Good actuals -> 
           Good (ppConcat [ppString "(:inst ", ppString pid, ppString " ",
                           ppSep (ppString " ") actuals,
                           ppString ")"])
         | Bad s -> Bad s)
    | Base (Qualified (_, pid),_,_) -> Good (ppString pid)
    | Boolean _ -> Good (ppString "bool")
    | Subtype (parentType, restriction, _) -> 
      (case (ppTypeName spc parentType, ppTerm restriction spc) of
         | (Good sParentType, Good sRestriction) ->
           Good (ppConcat [ppString "(:subtype ", sParentType,
                           ppString " ", sRestriction, ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | TyVar (tv,_) -> Good (ppString tv)
    | Product _ -> Bad "ppTypeName doesn't accept product types yet"
    | CoProduct _ -> Bad "ppTypeName doesn't accept coproduct types yet"
    | Arrow _ -> Bad "ppTypeName doesn't accept arrow type (really bad)"
    | _ -> Bad "Can't handle t in typeName"

%%%%%%%%%%%%%%%%%%%%%%%%
%% ppCoProductTypeDef %%
%%%%%%%%%%%%%%%%%%%%%%%%

%% Prints a (defcoproduct) form from the spec, the coproduct name, its type cases, and 
%% its type variables.
op ppCoProductTypeDefHelper (spc:Spec) (typeCases : List (QualifiedId * Option MSType)) : PPError (List WLPretty) = 
  let def ppTypeCaseHelper (id,optTy) =
  case optTy of
    | None    -> Good (ppString "")
    | Some (Product ([],_)) -> Good (ppString "")
    | Some (Product ((caseId,ty)::fields,pos)) ->
      (case (ppTypeName spc ty, ppTypeCaseHelper (id, Some (Product (fields,pos)))) of
         | (Good tn,
            Good rst) -> Good (ppConcat [tn, ppString " ", rst])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | Some ty -> 
      (case ppTypeName spc ty of
         | Good tn -> Good tn
         | Bad s -> Bad s)
  in let def ppTypeCase (Qualified(_, id),optTy) =
  case ppTypeCaseHelper (id,optTy) of
    | Good s -> Good (ppConcat [ppString "(", ppString id, ppString " ", s, ppString ")"])
    | Bad s -> Bad s
  in ppErrorMap ppTypeCase typeCases

op ppCoproductTypeDef (spc:Spec) (id : Id) (typeCases : List (QualifiedId * Option MSType)) (typeVars : List String) : PPError WLPretty = 
  case (ppCoProductTypeDefHelper spc typeCases, typeVars) of
    | (Good tcstrs,[]) ->
      Good (ppConcat [ppString "(defcoproduct ", ppString id, ppNewline,
                      ppSep (ppConcat [ppNewline, ppString "  "])
                        tcstrs,
                      ppString ")"])
    | (Good tcstrs,typeVars) ->
      Good (ppConcat [ppString "(defcoproduct ", ppString id, ppNewline,
                      ppString "  :type-vars (",
                      ppSep (ppString " ") (map ppString typeVars),
                      ppString ")", ppNewline,
                      ppSep (ppConcat [ppNewline, ppString "  "])
                        tcstrs,
                      ppString ")"])
    | (Bad s,_) -> Bad s

%%%%%%%%%%%%%%%
%% ppTypeDef %%
%%%%%%%%%%%%%%%

%% Prints out a type definition.
 
op ppTypeDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | TypeDef (qid, pos) ->
      let Qualified (q, id) = qid in
      let Some typeDefInfo = findTheType (spc, qid) in
      let name = typeDefInfo.names @ 0 in
      let dfn = typeDefInfo.dfn in
      (case dfn of 
         | Pi (tyVars, CoProduct (l,_), _) -> ppCoproductTypeDef spc id l tyVars
         | CoProduct (l,_) -> ppCoproductTypeDef spc id l []
         | Subtype (parentType, condition, _) ->
           (case (ppTypeName spc parentType, ppTerm condition spc) of
              | (Good sParentType, Good sCondition) ->
                Good (ppConcat [ppString "(defsubtype ", ppString id, ppString "-p ",
                                sParentType, ppString " ", sCondition, ppString")"])
              | (Bad s,_) -> Bad s
              | (_,Bad s) -> Bad s)
         | _ ->
           (case ppTypeName spc dfn of
              | Good tn ->
                Good (ppConcat [ppString "(defpredicate ", ppString id, ppString "-p (x)", 
                                ppNewline,
                                ppString "  (", tn, ppString " x))"])
              | Bad s -> Bad s))
    | _ -> Bad "Bad argument to ppTypeDef"

%%%%%%%%%%%%%%%
%% opVarList %%
%%%%%%%%%%%%%%%

%% Given a function term, get the list of variables

op opVarListHelper (l : MSMatch) : PPError (List MSVar) =
  case l of
    | [] -> Good []
    | ((VarPat (v,_), _, trm)::[]) -> Good [v]
    | ((RecordPat ((_,VarPat (v,_))::[],_), _, trm)::[]) -> Good [v]
    | ((RecordPat ((_,VarPat (v,_))::xs,x), y, trm)::[]) ->
      (case (opVarListHelper ((RecordPat (xs,x), y, trm)::[])) of 
        | Good val -> Good (v :: val)
        | Bad str -> Bad str)
    | _ -> Bad ("Can't handle trm in opVarListHelper"^(anyToString l))

op opVarList (trm : MSTerm) : PPError (List MSVar) =
  case trm of
    | Fun _ -> Good []
    | Lambda (l, _) -> opVarListHelper l
    | IfThenElse _ -> Good []
    | Apply _ -> Good []
    | _ -> Bad "Can't handle trm in opVarList"

%%%%%%%%%%%%%%%%
%% thmVarList %%
%%%%%%%%%%%%%%%%

%% Given a theorem body, unwrap all the top level foralls and just return the body

op thmVarListHelper (trm:MSTerm) : List MSVar =
  case trm of
    | Bind (Forall, [], subtrm, pos) -> thmVarListHelper subtrm
    | Bind (Forall, v::vs, subtrm, pos) ->
      v::(thmVarListHelper (Bind (Forall,vs,subtrm,pos)))
    | _ -> []

% Collect all the top-level bound variables in a term.
op thmVarList (trm:MSTerm) : List MSVar =
  thmVarListHelper trm

%%%%%%%%%%%
%% ppFun %%
%%%%%%%%%%%

op ppFun (f : MSFun) : PPError WLPretty =
  case f of
    | Bool x -> 
      (case x of | false -> Good (ppString "nil") | _ -> Good (ppString "t"))
    | Nat x -> Good (ppString (intToString x))
    | String x -> Good (ppConcat [ppString "\"", ppString x, ppString "\""])
%    | Char x -> Good (ppString x)
    | Not -> Good (ppString "not")
    | And -> Good (ppString "and")
    | Or -> Good (ppString "or")
    | Implies -> Good (ppString "implies")
    | Iff -> Good (ppString "iff")
    | Equals -> Good (ppString "equal")
    | Op (Qualified (q,id),_) -> Good (ppString id)
    | Embed (Qualified(_, id),_) -> Good (ppString id)
    | _ -> Bad "Can't handle f in ppFun"

%%%%%%%%%%%%%%%%%%
%% ppTermLambda %%
%%%%%%%%%%%%%%%%%%

%% Print a lambda term; we just print the body of the term, ignoring the fact 
%% that it's a function. This is fine to do on the top level of an op definition.

op ppTermLambda (trm : MSTerm) (spc : Spec) : PPError WLPretty =
  case trm of
    | Lambda ((_,_,trm)::[],_) -> ppTerm trm spc
    | Lambda _ -> Bad "Top level lambda contained more than match"
    | _ -> Bad "ppTermLambda only accepts lambdas"

%%%%%%%%%%%%%%%
%% ppPattern %%
%%%%%%%%%%%%%%%

op ppPatternHelper (pat:MSPattern) (spc:Spec) : PPError WLPretty =
case pat of 
  | WildPat _ -> Good (ppString "_")
  | NatPat (n,_) -> Good (ppString (intToString n))
  | VarPat ((v,_),_) -> Good (ppString v)
  | RecordPat ([],_) -> Good (ppString "")
  | RecordPat ((_,inPat)::rst,pos) ->
    (case (ppPattern inPat spc, ppPatternHelper (RecordPat (rst,pos)) spc) of
       | (Good sInPat, Good srst) ->
         Good (ppConcat [sInPat, ppString " ", srst])
       | (Bad s,_) -> Bad s
       | (_,Bad s) -> Bad s)
  | _ -> Bad "Bad pattern in ppPatternHelper"

op ppPattern (pat:MSPattern) (spc:Spec) : PPError WLPretty =
  case pat of
    | WildPat _ -> Good (ppString "_")
    | NatPat (n,_) -> Good (ppString (intToString n))
    | VarPat ((v,_),_) -> Good (ppString v)
    | EmbedPat (Qualified(_, id),None,Base (_,actuals as (_::_),_),_) ->
      (case ppErrorMap (ppTypeName spc) actuals of
         | Good actualstrs ->
           Good (ppConcat [ppString "((:inst ", ppString id, 
                           ppString " ", ppSep (ppString " ") actualstrs, 
                           ppString "))"])
         | Bad s -> Bad s)
    | EmbedPat (Qualified(_, id),None,_,_) ->
      Good (ppConcat [ppString "(", ppString id, ppString ")"])
    | EmbedPat (Qualified(_, id),Some inPat,Base (_,actuals as (_::_),_),_) ->
      (case (ppErrorMap (ppTypeName spc) actuals, ppPatternHelper inPat spc) of
         | (Good actualstrs, Good sInPat) ->
           Good (ppConcat [ppString "((:inst ", ppString id,
                           ppString " ", ppSep (ppString " ") actualstrs,
                           ppString ") ",
                           sInPat, ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | EmbedPat (Qualified(_, id),Some inPat,_,_) -> 
      (case ppPatternHelper inPat spc of
         | Good sInPat -> Good (ppConcat [ppString "(", ppString id, ppString " ", sInPat, ppString ")"])
         | Bad s -> Bad s)
    | RecordPat _ ->
      (case ppPatternHelper pat spc of
         | Good spat -> Good (ppConcat [ppString "(list ", spat, ppString ")"])
         | Bad s -> Bad s)
    | AliasPat (VarPat ((v,_),_),pat,_) ->
      (case ppPattern pat spc of
         | Good spat -> Good (ppConcat [ppString "(as ", ppString v, ppString " ", spat, ppString ")"])
         | Bad s -> Bad s)
    | RestrictedPat (pat, constraint, _) ->
      (case (ppPattern pat spc, ppTerm constraint spc) of
         | (Good spat, Good sconstraint) -> 
           Good (ppConcat [spat, ppString " ", sconstraint])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | _ -> Bad "Bad pattern in ppPattern"

%%%%%%%%%%%%%%%%%%%%%%%
%% ppTermApplyLambda %%
%%%%%%%%%%%%%%%%%%%%%%%

%% This prints a case-of statement. It looks a mess, because ``case'' is not a
%% syntax-level construct, it's a big application of a lambda with multiple matches.

op ppTermApplyLambdaHelper (match:MSMatch) (spc:Spec) : PPError WLPretty =
  case match of
    | (pat,_,trm)::rst ->
      (case (ppPattern pat spc, ppTerm trm spc, ppTermApplyLambdaHelper rst spc) of
         | (Good spat, Good strm, Good srst) ->
           Good (ppConcat [ppString "(", spat, ppNewline, strm, ppString ")", ppNewline, srst])
         | (Bad s,_,_) -> Bad s
         | (_,Bad s,_) -> Bad s
         | (_,_,Bad s) -> Bad s)
    | [] -> Good (ppString "")
    | _ -> Bad "Can't handle match in ppTermApplyLambdaHelper"

op ppTermApplyLambda (match:MSMatch) (trm:MSTerm) (spc:Spec) : PPError WLPretty =
  case (ppTermApplyLambdaHelper match spc, ppTerm trm spc) of
    | (Good smatch, Good strm) ->
      (case trm of
         | Record _ ->
           Good (ppConcat [ppString "(case-of (list ", strm, ppString ")", ppNewline, smatch, ppString ")"])
         | _ ->
           Good (ppConcat [ppString "(case-of ", strm, ppNewline, smatch, ppString ")"]))
    | (Bad s,_) -> Bad s
    | (_,Bad s) -> Bad s

%%%%%%%%%%%%%%
%% ppLambda %%
%%%%%%%%%%%%%%

%% print a lambda term.

op ppLambda (match:MSMatch) (spc:Spec) : PPError WLPretty =
case match of
  | (VarPat ((v,_),_),_,trm)::[] -> 
    (case ppTerm trm spc of
       | Good strm ->
         Good (ppConcat [ppString "(lambda (", ppString v, ppString ") ",
                         strm, ppString ")"])
       | Bad s -> Bad s)
  | _ -> Bad "Unsupported feature in ppLambda"

%%%%%%%%%%%%
%% ppTerm %%
%%%%%%%%%%%%

%% Print an arbitrary term.

op ppTerm (trm : MSTerm) (spc : Spec) : PPError WLPretty =
  case trm of
    % BOZO TODO: Actually look up the op in question and compute the type substitution.
    %            Right now all we're doing is looking at the types of the
    %            args and assuming the vars match. Really stupid.
    %
    % See unfoldOpRef in /Languages/MetaSlang/Specs/Utilities.sw for an example of
    % what needs to be done.

    % | Fun (Op (qid,_), _, _) | some? (findTheOp (spc,qid)) ->
    %    let Some {names=_,fixity=_,dfn,fullyQualified?=_} = findTheOp (spc,qid) in
    %    (case dfn of
    %       | Pi (tyVars, trm) ->
    %         (case 
    | Fun (f, Arrow (_,Base (_,actuals as (_::_),_),_), _) -> 
      (case (ppFun f,ppErrorMap (ppTypeName spc) actuals) of
         | (Good fstr, Good actualstrs) ->
           Good (ppConcat [ppString "(:inst ",
                           fstr,
                           ppString " ",
                           ppSep (ppString " ") actualstrs,
                           ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | Fun (f, Arrow (Base (_,actuals as (_::_),_),_,_), _) -> 
      (case (ppFun f,ppErrorMap (ppTypeName spc) actuals) of
         | (Good fstr, Good actualstrs) ->
           Good (ppConcat [ppString "(:inst ",
                           fstr,
                           ppString " ",
                           ppSep (ppString " ") actualstrs,
                           ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | Fun (f, Base (_, actuals as (_::_),_),_) ->
      (case (ppFun f, ppErrorMap (ppTypeName spc) actuals) of
         | (Good fstr, Good actualstrs) ->
           Good (ppConcat [ppString "((:inst ",
                           fstr,
                           ppString " ",
                           ppSep (ppString " ") actualstrs,
                           ppString "))"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | Fun (f as Embed e, Base _, _) -> 
      (case ppFun f of
         | Good fstr -> Good (ppConcat [ppString "(", fstr, ppString ")"])
         | Bad s -> Bad s)
    | Fun (f, _, _) -> ppFun f
    | Var ((v,_),_) -> Good (ppString v)
    | Record ([],pos) -> Good (ppString "")
    | Record ((_,trm)::[], pos) -> ppTerm trm spc
    | Record ((_,trm)::xs, pos) -> 
      (case (ppTerm trm spc, ppTerm (Record (xs,pos)) spc) of
        | (Good strm, Good srst) -> Good (ppConcat [strm, ppString " ", srst])
        | (Bad s,_) -> Bad s
        | (_,Bad s) -> Bad s)
    | Lambda (match,_) -> ppLambda match spc
    | IfThenElse (t1,t2,t3,_) ->
      (case (ppTerm t1 spc, ppTerm t2 spc, ppTerm t3 spc) of
         | (Good st1, Good st2, Good st3) -> 
           Good (ppConcat [ppString "(if ", st1, ppNewline,
                           ppString "    ", st2, ppNewline,
                           ppString "  ", st3, ppString ")"])
         | (Bad s,_,_) -> Bad s
         | (_,Bad s,_) -> Bad s
         | (_,_,Bad s) -> Bad s)
    | Apply (Lambda (match,_), trm, _) -> ppTermApplyLambda match trm spc
    | Apply (t1,t2,_) ->
      (case (ppTerm t1 spc, ppTerm t2 spc) of
         | (Good st1, Good st2) ->
           Good (ppConcat [ppString "(", st1, ppString " ", st2, ppString ")"])
         | (Bad s,_) -> Bad s
         | (_,Bad s) -> Bad s)
    | Bind (Forall,_,trm,_) -> ppTerm trm spc
    | Bind _ -> Bad "Existential quantifier in ppTerm"
    | _ -> Bad "Can't handle trm in ppTerm"
    
%%%%%%%%%%%%%
%% ppOpDef %%
%%%%%%%%%%%%%

%% Print an opDef, using defun-typed.

op ppOpDef (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Op (qid, defd, pos) ->
      let Qualified (q, id) = qid in
      let Some opDefInfo = findTheOp (spc, qid) in
      let name = opDefInfo.names @ 0 in
      let dfn = opDefInfo.dfn in
      (case dfn of
         | TypedTerm (trm, Arrow (_,tpe,_),pos) -> 
           (case (ppTermLambda trm spc, opVarList trm, ppTypeName spc tpe) of
              | (Good strm, Good varlist, Good tpestring) ->
                let typedVarList = ppErrorMap (fn (id,tpe) ->
                                                 (case ppTypeName spc tpe of
                                                    | Good tn -> Good (ppConcat [ppString "(",
                                                                                 ppString id,
                                                                                 ppString " ",
                                                                                 tn,
                                                                                 ppString ")"])
                                                    | Bad s -> Bad s)) varlist in
                (case (typedVarList, getProofPragma id spc.elements) of 
                   | (Good sTypedVarList,None) ->
                     Good (ppConcat [ppString "(defund-typed ", ppString id,
                                     ppString " (", ppSep (ppString " ") sTypedVarList, ppString ")", ppNewline,
                                     ppString "             ", tpestring, ppNewline,
                                     ppString "  ", strm, ppString ")"])
                   | (Good sTypedVarList,Some decl) ->
                     Good (ppConcat [ppString "(defund-typed ", ppString id,
                                     ppString " (", ppSep (ppString " ") sTypedVarList, ppString ")", ppNewline,
                                     ppString "             ", tpestring, ppNewline,
                                     ppString decl, ppNewline,
                                     ppString "  ", strm, ppString ")"])
                   | (Bad s,_) -> Bad s)
              | (Bad s,_,_) -> Bad s
              | (_,Bad s,_) -> Bad s
              | (_,_,Bad s) -> Bad s)
         | TypedTerm (trm, tpe, _) ->
           (case (ppTerm trm spc, ppTypeName spc tpe) of
              | (Good strm, Good stpe) ->
                Good (ppConcat [ppString "(defun ", ppString id,
                                ppString " ()", ppNewline,
                                ppString "  ", strm, ppString ")"])
              | (Bad s,_) -> Bad s
              | (_,Bad s) -> Bad s)
         | Pi (tyVars, TypedTerm (trm, Arrow (_,tpe,_), _), _) -> 
           (case (ppTermLambda trm spc, opVarList trm, ppTypeName spc tpe) of
              | (Good strm, Good varlist, Good tpestring) ->
                let typedVarList = ppErrorMap (fn (id,tpe) ->
                                                 (case ppTypeName spc tpe of
                                                    | Good tn -> Good (ppConcat [ppString "(",
                                                                                 ppString id,
                                                                                 ppString " ",
                                                                                 tn,
                                                                                 ppString ")"])
                                                    | Bad s -> Bad s)) varlist in
                (case (typedVarList, getProofPragma id spc.elements) of 
                   | (Good sTypedVarList,None) ->
                     Good (ppConcat [ppString "(defun-typed ", ppString id, ppNewline,
                                     ppString "  :type-vars (",
                                     ppSep (ppString " ") (map ppString tyVars),
                                     ppString ")", ppNewline,
                                     ppString " (", ppSep (ppString " ") sTypedVarList, ppString ")", ppNewline,
                                     ppString "             ", tpestring, ppNewline,
                                     ppString "  ", strm, ppString ")"])
                   | (Good sTypedVarList,Some decl) ->
                     Good (ppConcat [ppString "(defun-typed ", ppString id,
                                     ppString "  :type-vars (",
                                     ppSep (ppString " ") (map ppString tyVars),
                                     ppString ")", ppNewline,
                                     ppString " (", ppSep (ppString " ") sTypedVarList, ppString ")", ppNewline,
                                     ppString "             ", tpestring, ppNewline,
                                     ppString decl, ppNewline,
                                     ppString "  ", strm, ppString ")"])
                   | (Bad s,_) -> Bad s)
              | (Bad s,_,_) -> Bad s
              | (_,Bad s,_) -> Bad s
              | (_,_,Bad s) -> Bad s)
         | _ -> Bad "Can't handle dfn in ppOpDef")
    | _ -> Bad "Bad argument to ppOpDef"

% op ppTypeThm (elem:SpecElement) (spc:Spec) : PPError WLPretty =
%   case elem of
%     | Op (qid, defd, pos) ->
%       let Qualified (q, id) = qid in
%       let Some opDefInfo = findTheOp (spc, qid) in
%       let name = opDefInfo.names @ 0 in
%       let dfn = opDefInfo.dfn in
%       (case dfn of
%          | TypedTerm (trm,tpe,_) ->
%            (case tpe of
%               | Boolean _ ->
%                 Good (ppConcat [ppString "(defthm-typed ", ppString id, ppString "-type-constraint", ppNewline,
%                                 ppString "  (booleanp (", ppString id, ppString ")))"])
%               | Arrow (Boolean _,codomain,_) ->
%                 (case ppTypeName codomain of
%                    | Good cdtn ->
%                      Good (ppConcat [ppString "(defthm-guarded ", ppString id, ppString "-type-constraint", ppNewline,
%                                      ppString "  (implies (booleanp x)", ppNewline,
%                                      ppString "           (", cdtn, ppString " (", ppString id, ppString " x))))"])
%                    | Bad s -> Bad s)
%               | Arrow (Base (Qualified (type_q, type_id),_,_), codomain,_) ->
%                 (case ppTypeName codomain of
%                    | Good cdtn ->
%                      Good (ppConcat [ppString "(defthm-guarded ", ppString id, ppString "-type-constraint", ppNewline,
%                                      ppString "  (implies (", ppString type_id, ppString " x)", ppNewline,
%                                      ppString "           (", cdtn, ppString " (", ppString id, ppString " x))))"])
%                    | Bad s -> Bad s)
%               | Arrow (Product (types,_), codomain,_) ->
%                 (case ppTypeName codomain of
%                    | Good cdtn ->
%                      % Get the list of variables
%                      (case opVarList trm of
%                        Good varlist ->
%                         let svarlist = map (fn (v,_) -> ppString v) varlist in
%                         % Get the list of types
%                         let types = map (fn (_,t) -> t) types in
%                         % Zip the two up
%                         let typeRestrictions = zipWith ((fn (v, t) -> 
%                                                            let Good tn = ppTypeName t in
%                                                            ppConcat [ppString "(",tn,ppString " ",v,ppString ")"]),
%                                                         svarlist, types) in
%                         Good (ppConcat [ppString "(defthm-guarded ", ppString id, ppString "-type-constraint", ppNewline,
%                                         ppString "  (implies (and ",
%                                         ppNest 1 (ppSep ppNewline typeRestrictions),
%                                         ppString ")", ppNewline, 
%                                         ppString "           (", cdtn, ppString " (",
%                                         ppString id, ppString " ", ppSep (ppString " ") svarlist, ppString "))))"])
%                    | Bad s -> Bad s)
%                  | Bad s -> Bad s)
%               | _ -> Bad "Can't handle tpe in ppTypeThm")
%          | _ -> Bad "Bad argument to ppTypeThm")
%     | _ -> Bad "Bad argument to ppTypeThm"

%%%%%%%%%%%
%% ppThm %%
%%%%%%%%%%%

%% Print a theorem using defthm-typed

op ppThm (elem:SpecElement) (spc:Spec) : PPError WLPretty =
  case elem of
    | Property (p as (Theorem,Qualified(q,pn),tyVars as (_::_),trm,_)) ->
      (case ppTerm trm spc of
         | Good strm -> 
           let varStrings = ppErrorMap (fn (id,tpe) ->
                                          (case ppTypeName spc tpe of
                                             | Good tn -> Good (ppConcat [ppString "(",
                                                                          ppString id, 
                                                                          ppString " ",
                                                                          tn,
                                                                          ppString ")"])
                                             | Bad s -> Bad s)) (thmVarList trm) in
           (case (varStrings,getProofPragma pn spc.elements) of
              | (Good vs,None) ->
                Good (ppConcat [ppString "(defthm-typed ", ppString pn, ppNewline,
                                ppString "  :type-vars (",
                                ppSep (ppString " ") (map ppString tyVars),
                                ppString ")", ppNewline,
                                ppString "  (",
                                ppSep (ppConcat [ppNewline,ppString "                "])
                                  vs,
                                ppString ")", ppNewline,
                                strm, ppString ")"])
              | (Good vs,Some args) ->
                Good (ppConcat [ppString "(defthm-typed ", ppString pn, ppNewline,
                                ppString "  :type-vars (",
                                ppSep (ppString " ") (map ppString tyVars),
                                ppString ")", ppNewline,
                                ppString "  (",
                                ppSep (ppConcat [ppNewline,ppString "                "])
                                  vs,
                                ppString ")", ppNewline,
                                strm, ppNewline,
                                ppString args, ppString ")"])
              | (Bad s,_) -> Bad s)
         | Bad s -> Bad s)
    | Property (p as (Theorem,Qualified(q,pn),_,trm,_)) -> 
      (case ppTerm trm spc of
         | Good strm -> 
           let varStrings = ppErrorMap (fn (id,tpe) ->
                                          (case ppTypeName spc tpe of
                                             | Good tn -> Good (ppConcat [ppString "(",
                                                                          ppString id, 
                                                                          ppString " ",
                                                                          tn,
                                                                          ppString ")"])
                                             | Bad s -> Bad s)) (thmVarList trm) in
           (case (varStrings,getProofPragma pn spc.elements) of
              | (Good vs,None) ->
                Good (ppConcat [ppString "(defthm-typed ", ppString pn, ppNewline,
                                ppString "  (",
                                ppSep (ppConcat [ppNewline,ppString "                "])
                                  vs,
                                ppString ")", ppNewline,
                                strm, ppString ")"])
              | (Good vs,Some args) ->
                Good (ppConcat [ppString "(defthm-typed ", ppString pn, ppNewline,
                                ppString "  (",
                                ppSep (ppConcat [ppNewline,ppString "                "])
                                  vs,
                                ppString ")", ppNewline,
                                strm, ppNewline,
                                ppString args, ppString ")"])
              | (Bad s,_) -> Bad s)
         | Bad s -> Bad s)
    | _ -> Bad "Bad argument to ppThm"

%%%%%%%%%%%%%%%%%%%%
%% getProofPragma %%
%%%%%%%%%%%%%%%%%%%%

% Look up the proof pragma for a specific function/op, and return the content

op matchProofPragma (name:Id) (prag:String) : Option String =
let prag = stripOuterSpaces prag in
case splitAtStr (prag," ") of
  | Some ("ACL2",rstPrag) -> 
    (case splitAtStr (rstPrag," ") of
       | Some (pName,rstPrag) | stripOuterSpaces pName = name -> Some (stripOuterSpaces rstPrag)
       | Some (pName,rstPrag) -> None
       | _ -> None)
  | _ -> None

op getProofPragma (name:Id) (elts:SpecElements) : Option String =
case elts of
  | [] -> None
  | (Pragma ("proof",prag,"end-proof",_))::rst ->
    (case matchProofPragma name prag of
       | Some s -> Some s
       | None -> getProofPragma name rst)
  | _::rst -> getProofPragma name rst

%%%%%%%%%%%%%%%%%%%
%% ppSpecElement %%
%%%%%%%%%%%%%%%%%%%

op swPathToACL2Path (path:List String) : String =
case path of
  | [] -> ""
  | (x::[]) -> "acl2/" ^ x
  | (x::xs) -> x ^ "/" ^ (swPathToACL2Path xs)

op ppSpecElement (elt:SpecElement) (spc:Spec) : PPError WLPretty =
  case elt of
    | Type _ -> ppType elt spc
    | TypeDef _ -> ppTypeDef elt spc
    | Op _ -> ppOpDef elt spc
    | Property (Theorem,_,_,_,_) -> ppThm elt spc
    | Import ((UnitId (SpecPath_Relative uid),_),_,_,_) | uid.path = ["Library","Base"] ->
      Good (ppString "; base import")
    | Import ((UnitId (SpecPath_Relative uid),_),_,_,_) -> 
      (case getEnv "SPECWARE4" of
         | Some specware4 -> 
           let fullPath = specware4 ^ "/" ^ (swPathToACL2Path uid.path) in
           let fullPath = (case (uid.hashSuffix) of
                             | None -> fullPath
                             | Some suff -> fullPath ^ "_" ^ suff) in
           Good (ppConcat [ppString "(include-book \"",
                           ppString fullPath,
                           ppString "\")"])
         | _ -> Bad "blah")
    | Import _ -> Good (ppString "; can't handle import")
    | Pragma ("proof",prag,"end-proof",_) | verbatimPragma? prag ->
        let verbatim_str = case search("\n", prag) of
                             | None -> ""
                             | Some n -> subFromTo(prag, n, length prag)
        in
        Good (ppString verbatim_str)
    | Pragma _ -> Good (ppString "")
    | _ -> Bad "Bad SpecElement"

%%%%%%%%%%%%%%%%%%%%
%% ppSpecElements %%
%%%%%%%%%%%%%%%%%%%%

op filterNonEmpty (strs:List Doc) : List WLPretty =
case strs of
  | [] -> []
  | (DocText "")::rst -> filterNonEmpty rst
  | (x::rst) -> x :: (filterNonEmpty rst)

op ppSpecElements (elts:SpecElements) (spc:Spec) : PPError WLPretty =
  case ppErrorMap (fn t -> ppSpecElement t spc) elts of
    | Good eltsStrings ->
      Good (ppSep (ppConcat [ppNewline, ppNewline]) (filterNonEmpty eltsStrings))
    | Bad s -> Bad s

%%%%%%%%%%%%
%% ppSpec %%
%%%%%%%%%%%%

op ppSpec (c: Context) (spc:Spec) : PPError WLPretty =
%  let spc = adjustElementOrder spc in
  let spc = explicateEmbeds spc in
  let spc = removeImplicitConstructorOps spc in
  case (getEnv "SPECWARE4", ppSpecElements spc.elements spc ) of
    | (Some specware4, Good s) -> 
      Good (ppGr2Concat [ppString "(in-package \"ACL2\")",
                         ppNewline,
                         ppString "(include-book \"",
                         ppString specware4,
                         ppString "/Languages/ACL2/specware-book\")",
                         ppNewline,
                         ppString "(set-ignore-ok t)",
                         ppNewline,
                         ppString "(set-bogus-defun-hints-ok t)",
                         ppNewline,
                         s])
    | (None,_) -> Bad "Please set SPECWARE4 environment variable"
    | (_,Bad s) -> Bad s

%%%%%%%%%%%%%
%% ppValue %%
%%%%%%%%%%%%%

op ppValue (c: Context) (value:Value) : PPError WLPretty =
  case value of
    | Spec spc -> ppSpec c spc
    | _ -> Bad "Can't handle value in ppValue"

op printValue (c:Context) (value:Value) : PPError String =
  let file_nm = case fileNameOfValue value of
                  | Some str -> str
                  | _ -> ""
  in
  let main_pp_val = ppValue (c << {fileName = file_nm}) value in
  case main_pp_val of
    | Good s -> Good (ppFormat s)
    | Bad s -> Bad s

op printValueTop (value : Value, uid : UnitId, showImportedSpecs? : Bool) : PPError String =
  printValue {printTypes? = true,
              printPositionInfo? = false,
              fileName = "", %FIXME the caller already has the file name? ah, this is used to print position information?
              %currentUID = uid,
              %uidsSeen = [uid],
              recursive? = true,
              showImportedSpecs? = showImportedSpecs?}
             value

op  uidToACL2Name : UnitId -> String
def uidToACL2Name {path, hashSuffix=_} =
  let device? = deviceString? (head path) in
  let main_name = last path in
  let path_dir = butLast path in 
  let mainPath = flatten (foldr (fn (elem, result) -> "/"::elem::result)
                            ["/acl2/", main_name]
                            (if device? then tail path_dir else path_dir))
  in if device?
       then (head path) ^ mainPath
       else mainPath


op unitIdToACL2String(uid: UnitId): (String * String * String) =
  case uid.hashSuffix of
    | Some loc_nm | loc_nm ~= last uid.path -> (last uid.path, uidToACL2Name uid, "_" ^ loc_nm)
    | _ ->           (last uid.path, uidToACL2Name uid, "")

op  uidNamesForValue: Value -> Option (String * String * UnitId)
def uidNamesForValue val =
  case uidStringPairForValue val of
    | None -> None
    | Some((thynm, filnm, hash), uid) ->
      Some(if thynm = hash then (thynm, filnm, uid)
           else (thynm ^ hash, filnm ^ hash, uid))

op  uidStringPairForValue: Value -> Option ((String * String * String) * UnitId)
def uidStringPairForValue val =
  case MonadicStateInternal.readGlobalVar "GlobalContext" of
    | None -> None
    | Some global_context ->
  case findUnitIdForUnit(val, global_context) of
    | None -> None
    | Some uid -> Some (unitIdToACL2String uid, uid)

op genACL2Core (val : Value, showImportedSpecs? : Bool) : Bool =
  case uidNamesForValue val of
    | None -> let _ = writeLine "Error: Can't get UID string from value" in false
    | Some (thy_nm, uidstr, uid) -> 
%      let uidstr = fileNameInSubDir(uidstr, "acl2") in
      let filename = uidstr ^ ".lisp" in
      let _ = ensureDirectoriesExist filename in
      let _ = writeLine("Writing ACL2 to: " ^ filename ^ "\n") in
      case printValueTop(val,uid,showImportedSpecs?) of
        | Good s -> 
          let _ = writeStringToFile(s,filename) in true
        | Bad s ->
          let _ = writeLine("Error occurred: " ^ s) in false

op evaluateGenACL2Helper (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String, showImportedSpecs? : Bool) : Option String = 
  case UIDStringFromArgString(optional_argstring, lastUnitIdLoaded, homedir) of
    | None -> None
    | Some uid_str -> 
      let success? = (case evaluateUnitId uid_str of
                        | None -> let _ = writeLine("Error: Unknown UID " ^ uid_str) in false
                        | Some val -> genACL2Core(val, showImportedSpecs?)) in
      if success? then Some uid_str else None

op evaluateGenACL2 (optional_argstring : Option String, lastUnitIdLoaded : Option String, homedir : String) : Option String =
  evaluateGenACL2Helper (optional_argstring, lastUnitIdLoaded, homedir, false)

end-spec
