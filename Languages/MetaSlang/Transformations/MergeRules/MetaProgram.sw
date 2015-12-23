(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% This spec exports a transformation 'mergeRules' 
%%
%% S0 = S1 { at f { mergeRules [f1,f2]}}
%%
%% that combines a collection of functions (here 'f1', 'f2' identified
%% as parameters to the transformation) into a single function
%% 'f'. The input functions must have the form.
%% 
%%  f1 : (s : StateType |  Pre[s] ) -> (s' : StateType | Post[s,s'])
%%  f2 : (s : StateType |  Pre[s] ) -> (s' : StateType | Post[s,s'])
%%
%% Where 'StateType' can vary between transformation invocations, but
%% must be uniform. The state variables 's' and 's'' can vary between
%% functions 'f1' and 'f2', but will be renamed uniformly in the
%% resulting function 'f'. 'Pre' is a precondition of type 'StateType
%% -> Bool' which 's' can appear free in, and 'Post' is a
%% postcondition of type 'StateType -> StateType -> Bool' in which
%% 's' and 's'' can both appear free.

%% TODO: Describe the rule combination algorithm and correctness
%% criteria as documented in Doug's 'rule-composition.sw' note in the
%% HACMS 'Docs' subdirectory.

%% Issues:
%%
%% - Naming is incredibly brittle. Need to come up with a sane
%%   solution. E.g. if two rules share pre/post condition constraints,
%%   but existentially quantified names are different, then the
%%   algorithm will not work correctly.
%%
%% - We need to normalize pre- and post- state names, instead of
%%   relying on them being the same. This should be easy to implement.
%% 
%% - When generating case-splits, the algorithm doesn't handle
%%   renaming of pattern variables (e.g. if one clause has the
%%   predicate 't = Some x' and a second clause has the predicate 't =
%%   Some y', then we should choose a fresh name 'z' to use as the
%%   pattern variable, and rename x to z in the first clause and y to
%%   z in the second clause.
%%
MergeRules qualifying
spec

import ../Rewriter
import ../Coalgebraic
import /Languages/MetaSlang/Specs/Elaborate/TypeChecker
import /Languages/MetaSlang/AbstractSyntax/Equalities


% When merging, we may need to simplify given some rewrite rules. The
% 'mergeRules' spec transform take such a list.
type Rewrites = List RuleSpec

%% A rule to be merged has the form:
%%
%% op rule(h:StateType,i1:T1,...,in:Tn | pre):{(h',o1,...,om) : (StateType * OT1 * ... * OTn) | post}
%%

type STRule = { st_stateType : MSType,   % StateType
                st_prestate : Id, % h
                st_precondition : Option MSTerm, % pre
                st_poststate : Id, % h'
                st_postcondition : Option MSTerm, % post
                st_inputs : List (Id*MSType), % [(i1,T1),...,(in,Tn)]
                st_outputs : List (Id*MSType) % [(o1,OT1),...,(on,OTn)]
              }

op SpecTransform.mergeRules(spc:Spec)(args:QualifiedIds)(trace?:TraceFlag)
      (theorems:Rewrites)(noUnfolds:QualifiedIds)(unfoldDepth:Option Int)(smtArgs:QualifiedIds):Env Spec =
%% This transformation takes a list of "rules", defined as specware ops, and
%% combines them into a single op.
%% Arguments:
%%  spc: The specification to transform
%%  qids: The names of the ops defining the ruleset to transform.
%% Returns:
%%  An op with the pre (resp. post) conditions of the named input rules merged
%%  into a single pre (resp. post) condition.
% op SpecTransform.mergeRules(spc:Spec)(args:QualifiedIds):Env Spec =
  let unfoldDepth = case unfoldDepth of | Some i -> i | None -> 1 in

  let (fname::qids) = args in
  let _ = writeLine("MergeRules "^show fname) in
  let _ = if trace? then app (fn o -> writeLine ("Input Rule: "^(show o))) qids else () in
  { ruleSpecs as (rs1::_) <- mapM (fn o -> getOpPreAndPost(spc,o,theorems,trace?)) qids
  ; ups <- combineRuleSpecs spc ruleSpecs theorems noUnfolds unfoldDepth
  ; let ps = map (fn (a,b,_) -> (a,b)) ups in
    let unfolds = flatten (map (fn (_,_,c) -> c) ups) in
    let _ = if trace? then writeLine "Unfold terms" else () in
    let _ = if trace? then app (writeLine o printQualifiedId) unfolds else () in
    let stateType = rs1.st_stateType in
    let preStateVar = rs1.st_prestate in
    let postStateVar = rs1.st_poststate in
    let inputs = rs1.st_inputs in
    let outputs = rs1.st_outputs in
    let obs = findObservers spc stateType in
    let (vars,is) = unzip ps in
    let vars' = nubBy (fn (i,j) -> i.1 = j.1 && i.2 = j.2) (flatten vars : ExVars) in 
    let args : BTArgs =
          { spc=spc, obs=obs,
            stateVar=postStateVar,
            assumptions=[],
            outputs= List.map (fn i -> i.1) outputs,
            vars=vars' % (List.map (fn i -> i.1) vars')
            } in

    % Look at each clause, and each atomic expression in that clause, and
    % classify its syntactic form.
    let cclauses : List (List CClass) = map (classifyClause args) (flatten is) in
    %% Remove any atomic expressions representing true.
    let noTauto : List (List CClass) = map (fn clause -> filter (fn a -> ~ (isTrueAtom? a)) clause) cclauses in
    let noContra = filter (fn clause -> ~ (exists? (fn a ->  (isFalseAtom? a)) clause)) noTauto in
    let _ = if trace? then writeLine (anyToString (length noContra) ^ " total postconditions.") else () in
    % let _ = writeLine "Postconditions:" in
    % let _ = writeLine (printDNF (map (map classToTerm) noContra)) in
    
    let _ = if trace? then writeLine "About to begin merge" else () in    
    let (rterm,pred,prf) = bt2 args noContra in
    let _ = if trace? then writeLine "Done with merge" else ()in
    % let _ = writeLine (printTerm rterm) in
    let calculatedPostcondition = mkSimpleExists vars' rterm in    

    let _ = if trace? then writeLine ("Calculated Unhandled Input Predicate: " ^ printTerm (dnfToTerm pred)) else () in
    %% Use this representation, rather than DNF, since it's easier to read.
    let preAsConj = mkNot (dnfToTerm pred) in % mkAnd (map (fn conj -> mkNot (mkMinimalExists vars' (ands conj))) pred) in
    let _ = if trace? then writeLine ("Generated Precondition: " ^ printTerm preAsConj) else () in
    let body = mkCombTerm( (preStateVar,stateType)::inputs) ((postStateVar,stateType)::outputs) preAsConj calculatedPostcondition in
    let refinedType =
          mkCombType( (preStateVar,stateType)::inputs) ((postStateVar,stateType)::outputs) preAsConj calculatedPostcondition in
    let qvars = (preStateVar,stateType)::(postStateVar,stateType)::inputs ++ outputs in 

    let spc' = case findTheOp(spc, fname)  of
                | Some oi ->
                  % let TypedTerm(_,ty,_) = body in
                  % let _ = writeLine "Refining quid" in
                  let orig_postCondn =
                    case rs1.st_postcondition of
                      | Some condn -> condn
                      | None -> mkTrue ()
                  in
                  let pf = prove_MergeRules (prf, orig_postCondn,
                                             unfolds, smtArgs) in
                  let (Some pf_pred) = getProofPredicate pf in
                  let _ = if trace? then writeLine ("MergeRules: building a proof of ("
                                                      ^ printTerm pf_pred ^ ")") else () in
                  addRefinedTypeH(spc,oi,refinedType,Some body,Some pf)
                | None ->
                  let _ = if trace? then writeLine (anyToString fname ^ " is not already defined.") else () in
                  addOpDef(spc,fname,Nonfix,body)
    in

    % let thmName = mainId fname ^ "_mergeRules_correct" in
    % let thm = mkRefinementThm qvars prf in 
    % let spc' = addTheoremLast ((mkUnQualifiedId thmName,[],thm,noPos), spc) in
    % let prfText = mkIsarProof prf "" in
    % let spc' = addPragma (("proof", " Isa " ^ thmName ^ "\n" ^ prfText ^ "\n", "end-proof",noPos),spc') in
    return spc'
  }

op mkCombTerm(dom:List (Id * MSType))(ran:List (Id * MSType))(pre:MSTerm)(post:MSTerm):MSTerm =
    let (domNames, domTypes) = unzip dom in
    let (ranNames,ranTypes) = unzip ran in
    let domType = mkProduct domTypes in
    let ranType = mkProduct ranTypes in
    let domPred = mkLambda (mkTuplePat (map mkVarPat dom), pre) in
    let ranPred = mkLambda (mkTuplePat (map mkVarPat ran), post) in
    let domType = mkSubtype (domType, domPred) in
    let ranType = mkSubtype (ranType, ranPred) in
    let body = mkLambda (mkRestrictedPat (mkTuplePat (map mkVarPat dom), pre),Any noPos) in
    body

op mkCombType(dom:List (Id * MSType))(ran:List (Id * MSType))(pre:MSTerm)(post:MSTerm):MSType =
    let (domNames, domTypes) = unzip dom in
    let (ranNames,ranTypes) = unzip ran in
    let domType = mkProduct domTypes in
    let ranType = mkProduct ranTypes in
    let domPred = mkLambda (mkTuplePat (map mkVarPat dom), pre) in
    let ranPred = mkLambda (mkTuplePat (map mkVarPat ran), post) in
    let domType = mkSubtype (domType, domPred) in
    let ranType = mkSubtype (ranType, ranPred) in
    mkArrow(domType, ranType)
    


%% Get the pre and post condition for an op, extracted from its type. The
%% type of the op must be a function with at least one argument, (with
%% the state being the first argument) to one or more values. If the
%% result of the op is a single type, it must match the type of the
%% first argument to the op. If the result is a tuple of types, then
%% the first element of the tuple must match the first argument of the
%% op.
%% Arguments:
%%%  spc: The spec that contains the op.
%%   qid: The op to extract.
%% Returns:
%%   An STRule representing the elements of the rule.
op getOpPreAndPost(spc:Spec, qid:QualifiedId, theorems:Rewrites, trace?: TraceFlag):Env STRule = 
   % let _ = writeLine ("Looking up op " ^ (show qid)) in
   let def printOthers(p:Id*MSType) = writeLine (p.1 ^ " " ^ printType p.2) in
   case getOpDef(spc,qid) of
     | None -> raise (Fail ("Could not get term pre and post conditions for op " ^ (show qid)))
       % The type should be of the form {x:StateType | Preconditions} -> {y:StateType | Postcondition}
     | Some (tm, ty as (Arrow (dom, codom,_))) ->
       let _ = if trace? then writeLine ("Arrow type is " ^ printType ty) else () in
       let _ = if trace? then writeLine ("Term  is " ^ printTerm tm) else () in       
       let _ = if trace? then writeLine ("Domain is " ^ (printType dom)) else () in
       let _ = if trace? then writeLine ("Codomain is " ^ (printType codom)) else () in
       { (preStateVar,preStateType,inputArgs,preCondition) <-
          getSubtypeComponents spc dom theorems
       ; (postStateVar,postStateType,outputVals,postCondition) <-
          getSubtypeComponents spc codom theorems
         % Require the pre- and poststate types  match.
         % FIXME: Need equality modulo annotations
         % guard (preStateType = postStateType) (
         %   "In the definition of the coalgebraic function: " ^ (show qid) ^ "\n" ^
         %   "Type of prestate:                 " ^ printType preStateType ^ "\n" ^
         %   "Does not match type of poststate: " ^ printType postStateType)
       ; let _ = if trace? then writeLine "inputs" else () in
         let _ = if trace? then app printOthers inputArgs else () in
         let _ = if trace? then writeLine "outputs" else () in
         let _ = if trace? then app printOthers outputVals else () in
         return ()          
       ; return { st_stateType = preStateType,
                  st_prestate = preStateVar,
                  st_poststate = postStateVar,
                  st_precondition = preCondition,
                  st_postcondition = postCondition,
                  st_inputs = inputArgs,
                  st_outputs = outputVals
                 }

       }
     | Some (tm,ty) -> 
         let m1 = ("getOpPreAndPost:\n Type is " ^ (printType ty)) in 
         let m2 = ("Which is not of the correct form.") in
         raise (Fail (m1 ^ m2))


%% Get the predicate constraining a subtype. 
%% return the bound variable, and its classifier.
%% If there is no predicate (it is not a subtype), 
%% then return None. If there is a subtype,then return the
%% subtype expression. The subtype expression assumes
%% that the bound variable is in scope in the expression.
%% In the case that the type is *not* a subtype, then
%% the bound variable is "_".
%% Arguments:
%%  spc: The spec that the subtype expression appears in.
%%  ty:  The type 
%% Returns:
%%  3-tuple (Bound variable, classifier, other components and types, Option (subtype expression) )
op getSubtypeComponents(spc:Spec)(ty:MSType)(theorems:Rewrites):Env (Id * MSType * List (Id * MSType) * Option MSTerm) =
  case ty of
   | Subtype (binding,pred,_) ->
      { (n,ty,rest,body) <- getLambdaComponents spc pred 
      ; return (n,ty,rest,Some body)
      }
   | Base (_,_,_) -> return ("_",ty,[],None) 
   | _ ->  
     let _ = (writeLine ("getSubtypeComponents" ^ anyToString ty))
     in raise (Fail ("Can't extract subtype from " ^ printType ty))


%% From `fn (x:T | guard)  -> body` extract (x,T,body).
%% Constraints: function is unary, binding a variable (only)guard is true.
%% _Surely_ this is defined somewhere???
op getLambdaComponents(spc:Spec)(tm:MSTerm):Env (Id * MSType * List (Id*MSType) * MSTerm) =
  % let _ = writeLine ("Looking at subtype predicate " ^ printTerm tm) in
  case tm of                                         
   | Lambda ([(VarPat ((n,ty),_),guard,body)], _) ->
      % let _ = writeLine ("Bound Var: " ^ anyToString n) in
      % let _ = writeLine ("Classifier: " ^ printType ty ) in
      % let _ = writeLine ("Guard: " ^ printTerm guard) in
      % let _ = writeLine ("Body: " ^ printTerm body) in
      return (n,ty,[],body)
   | Lambda ([(pat as (RecordPat (fields,recordLoc)),guard,body)], lamLoc) ->
        (case getRecPatternElements pat of
          | Some (s,stype,rest) -> return (s,stype,rest,body)
          | None ->
            raise (Fail ("Cannot fetch state elements." ^ anyToString fields)))
   | Lambda ([(pat,guard,body)], _) -> 
       raise (Fail ("getLambdaComponents: Not a unary lambda" ^ anyToString pat))
   | _ -> raise (Fail "getLambdaComponents: Not a unary lambda.")

%% Given a record pattern of the form RecordPat [(s:Stype, p1:T1,
%% p2:T2, ...)] return Some (s, Stype, [(p1,T1),...]. If the pattern
%% does not have that form, then return None.
op getRecPatternElements(pat:MSPattern):Option (Id*MSType*List (Id*MSType)) =
  case pat of
    | RecordPat (("1", (VarPat ((s,stype), varPatLoc)))::rest, patLoc) ->
      let def tupleElements x:Option (List (Id*MSType)) =
            case x of
              | [] -> Some []
              | ((idx, (VarPat ((vname,vtype), _)))::rest) ->
                  (case tupleElements rest of
                     | Some l -> Some ((vname,vtype)::l)
                     | None -> let _ = writeLine "e1" in None)
              | _ -> let _ = writeLine "e2" in None
      in (case tupleElements rest of
             | Some params -> Some (s,stype,params)
             | None -> let _ = writeLine "e3" in None)
    | _ -> let _ = writeLine "e4" in None
               


%% combineRuleSpecs normalizes pre/post condition naming, and generates
%% a "DNF" representation of the pre- and post-conditions as a list of lists
%% of MSTerms, where each outer term corresponds to a disjunct, and each
%% inner term corresponds to a conjunction, where each element is an
%% atomic formula. Moreover, we normalize the names of the pre- and poststate 
%% variables.
%% FIXME: Currently, there's no variable renaming going on...
op combineRuleSpecs(spc:Spec)(rules:List STRule)(theorems:Rewrites)
    (noUnfolds:List QualifiedId)(unfoldDepth:Int):Env (List (ExVars * DNFRep * List QualifiedId)) =
% op combineRuleSpecs(spc:Spec)(rules:List (MSType*Id*Option MSTerm*Id*Option MSTerm))(theorems:Rewrites):Env (List (ExVars * DNFRep)) =
  let types = map (fn r -> r.st_stateType) rules  in
  let preconditions = map (fn r -> case r.st_precondition of Some t -> t | None -> (mkTrue ())) rules in
  let postconditions = map (fn r -> case r.st_postcondition of Some t -> t | None -> (mkTrue ())) rules in
  { pres <-
     mapM (normalizeCondition spc theorems noUnfolds unfoldDepth) preconditions 
  ; posts <-
     mapM (normalizeCondition spc theorems noUnfolds unfoldDepth) postconditions
  ; let rels = zipWith (fn x -> fn y -> (nubBy equalVar?  (x.1 ++ y.1), andDNF x.2 y.2, x.3 ++ y.3)) pres posts in 
    % let _ = (writeLine (anyToString (List.length (List.flatten (List.map (fn i -> i.2) posts))) ^ " total postconditions.")) in
    % let _ = map printIt ps in
    % let _ = writeLine "Preconditions" in
    % let _ = List.map (fn p -> writeLine (printDNF (p.2))) pres in
    % let _ = writeLine "Postconditions" in
    % let _ = List.map (fn p -> writeLine (printDNF (p.2))) posts in
    return rels
  }
 
type ExVars = List (AVar Position)
type DNFRep = (List MSTerms)
%% Remove existential quantifers, flatten to DNF.
op normalizeCondition(spc:Spec)(theorems:Rewrites)
   (noUnfolds:List QualifiedId)(undepth:Int)(tm:MSTerm):Env(ExVars *  DNFRep * List QualifiedId) = 
  % let _ = writeLine ("Normalizing " ^ printTerm tm) in
  case tm of
    | Bind (Exists,vars,body,_) -> 
      { (vs',dnf,us) <- normalizeCondition spc theorems noUnfolds undepth  body 
      ; return (vs' ++ vars,dnf,us)
      }
   | (Apply (Fun (f as And,_,_), Record (args,_),_)) -> 
       let Some a1 = getField (args,"1") in
       let Some a2 = getField (args,"2") in
       { (v1,r1,us1) <- normalizeCondition spc theorems noUnfolds undepth a1
       ; (v2,r2,us2) <- normalizeCondition spc theorems noUnfolds undepth a2 
       ; return (v1 ++ v2, (flatten (map  (fn l -> map (fn r -> l ++ r) r2) r1)), us1 ++ us2)
       }
    | (Apply (Fun (f as Or,_,_), Record (args,_),_)) ->
       % let _ = writeLine ("Splitting in " ^ printTerm tm) in
       let Some a1 = getField (args,"1") in
       let Some a2 = getField (args,"2") in
       { (v1,dnf1,us1) <- normalizeCondition spc theorems noUnfolds undepth a1;
         (v2,dnf2,us2) <- normalizeCondition spc theorems noUnfolds undepth a2;
         return (v1 ++ v2, dnf1 ++ dnf2,us1 ++ us2)
       }
   | IfThenElse (p,t,e,_) -> 
     { (vp,rp,us1) <- normalizeCondition spc theorems noUnfolds undepth p;
       (vt,rt,us2) <- normalizeCondition spc theorems noUnfolds undepth t;
       (ve,re,us3) <- normalizeCondition spc theorems noUnfolds undepth e;
       let ut = andDNF rp rt in
       let ue = andDNF (negateDNF rp) re in
       return (vp ++ vt ++ ve, ut ++ ue, us1 ++ us2 ++ us3)
      }
   | Apply(Fun(NotEquals,ty,a1),args,a2) ->
        return ([],[[mkNot (Apply(Fun(Equals,ty,a1),args,a2))]],[])

    | (Let ([(VarPat (var,varLoc), definition)],body,_)) ->
        normalizeCondition spc theorems noUnfolds undepth (substitute (body, [(var,definition)]))

    | _ | undepth > 0 && isUnfoldable? tm spc noUnfolds  ->
            % let _ = writeLine ("Simplifying \n" ^ printTerm tm) in
            let tm' = betan_step (unfoldTerm (tm,spc)) in
            % let tm' = simplifyOne spc (unfoldTerm (tm,spc)) in
            % let _ = writeLine ("Simplified to \n"^ printTerm tm') in
            { (vs,ts,us) <- normalizeCondition spc theorems noUnfolds (undepth - 1) tm';
             return (vs,ts,unfoldFunction tm::us)
             }
            % normalizeCondition spc theorems noUnfolds (undepth - 1) tm'

    | _ -> case rewriteWithRules_opt (spc, theorems, tm) of
            | Some (tm', _) -> normalizeCondition spc theorems noUnfolds undepth tm'
            | None -> return ([],[[tm]],[]) 


type CDNFRep = List (List CClass)
type TraceTree =
  | Contra (CDNFRep * (List MSTerm) * List (Id * MSType)) % inputs, assumptions, vars
  | Tauto (CDNFRep * (List MSTerm) * List (Id * MSType)) % inputs, assumptions, vars
  | TIf (MSTerm * CDNFRep * (List MSTerm) * MSTerm * TraceTree * TraceTree * DNFRep * List (Id * MSType))  % input, assumptions, branch term, true child, false child, precondition, vars
  | TCase (MSTerm * CDNFRep * (List MSTerm) * MSTerm * List (MSPattern * TraceTree) * DNFRep * List (Id * MSType))   % result, input, assumptions, scrutinee, alts, precondition
  | TLocal (MSTerm * CDNFRep * List MSTerm * List (List (Id*MSType) * MSTerm) * TraceTree * DNFRep * List (Id * MSType)) % input, assumptions, variables,  child, precondition
  | TFactoring  (MSTerm * CDNFRep * (List MSTerm) * List MSTerm *  TraceTree * DNFRep * List (Id * MSType)) % result, input, assumptions, factors, child, pre
  | Unknown


% Apply a function to all the terms in a proof, as with mapTerm.
% README: This will only work if the function does not somehow change
% the underlying structure of the TraceTree; e.g., case expressions
% referred to in the input TraceTree should still have the same basic
% form in the output
%
% FIXME: add some sort of consistency check after the mapping
op mapTraceTree (tsp: TSP_Maps_St) (t: TraceTree) : TraceTree =
  case t of
    | Contra (inps, assumps, vars) ->
      Contra (mapCDNFRep tsp inps, map (mapTerm tsp) assumps,
              mapVars tsp vars)
    | Tauto (inps, assumps, vars) ->
      Tauto (mapCDNFRep tsp inps, map (mapTerm tsp) assumps,
             mapVars tsp vars)
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) ->
      TIf (mapTerm tsp res, mapCDNFRep tsp inps,
           map (mapTerm tsp) assumps, mapTerm tsp split,
           mapTraceTree tsp lt, mapTraceTree tsp rt,
           mapDNFRep tsp fail, mapVars tsp vars)
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) ->
      TCase (mapTerm tsp res, mapCDNFRep tsp inps,
             map (mapTerm tsp) assumps, mapTerm tsp scrutinee,
             map (fn (pat,tree) ->
                    (mapPattern tsp pat, mapTraceTree tsp tree)) alts,
             mapDNFRep tsp fail, mapVars tsp vars)
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) ->
      TLocal (mapTerm tsp res, mapCDNFRep tsp inps,
              map (mapTerm tsp) assumps,
              map (fn (vars,body) ->
                     (mapVars tsp vars, mapTerm tsp body)) defvars,
              mapTraceTree tsp sub,
              mapDNFRep tsp fail, mapVars tsp vars)
    | TFactoring (res,inps,assumps,factors,sub,fail,vars) ->
      TFactoring (mapTerm tsp res, mapCDNFRep tsp inps,
                  map (mapTerm tsp) assumps,
                  map (mapTerm tsp) factors, mapTraceTree tsp sub,
                  mapDNFRep tsp fail, mapVars tsp vars)

op mapDNFRep (tsp: TSP_Maps_St) (rep: DNFRep) : DNFRep =
  map (map (mapTerm tsp)) rep

op mapCDNFRep (tsp: TSP_Maps_St) (rep: CDNFRep) : CDNFRep =
  map (map (mapCClass tsp)) rep

op mapCClass (tsp: TSP_Maps_St) (cclass: CClass) : CClass =
  case cclass of
    | CAtom (t,ids,b,typ) ->
      CAtom (mapTerm tsp t, ids, b, mapType tsp typ)
    | CDef (vars,t,deps,b,ty1,ty2) ->
      CDef (mapVars tsp vars, mapTerm tsp t, deps, b,
            mapType tsp ty1, mapType tsp ty2)
    | CConstrain (v,t,deps,b,ty) ->
      CConstrain (mapTerm tsp v, mapTerm tsp t, deps, b,
                  mapType tsp ty)
    | CCase (pat,t,deps,b,ty) ->
      CCase (mapPattern tsp pat, mapTerm tsp t, deps, b,
             mapType tsp ty)


op traceInputs(t:TraceTree):CDNFRep =
  case t of
    | Contra (inps, assumps, vars) -> inps
    | Tauto (inps, assumps, vars) -> inps
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) -> inps
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) -> inps
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) -> inps
    | TFactoring (res,inps,assumps,fators,sub,fail,vars) -> inps

op traceAssumptions(t:TraceTree):List MSTerm =
  case t of
    | Contra (inps, assumps, vars) -> assumps
    | Tauto (inps, assumps, vars) -> assumps
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) -> assumps
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) -> assumps
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) -> assumps
    | TFactoring (res,inps,assumps,fators,sub,fail,vars) -> assumps
    | Unknown -> []


op traceFailure(t:TraceTree):DNFRep =
  case t of
    | Contra (inps, assumps, vars) -> [] % FIXME: Should be something else.
    | Tauto (inps, assumps, vars) -> [] % FIXME: Should be something else.
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) -> fail
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) -> fail
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) -> fail
    | TFactoring (res,inps,assumps,fators,sub,fail,vars) -> fail


op traceResult(t:TraceTree):MSTerm =
  case t of
    | Contra (inps, assumps, vars) -> mkFalse ()
    | Tauto (inps, assumps, vars) -> mkTrue () 
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) -> res
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) -> res
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) -> res
    | TFactoring (res,inps,assumps,fators,sub,fail,vars) -> res

op traceVars(t:TraceTree):List (Id * MSType) =
  case t of
    | Contra (inps, assumps, vars) -> vars
    | Tauto (inps, assumps, vars) -> vars
    | TIf (res,inps,assumps,split,lt,rt,fail,vars) -> vars
    | TCase (res,inps,assumps,scrutinee,alts,fail,vars) -> vars
    | TLocal (res,inps,assumps,defvars,sub,fail,vars) -> vars
    | TFactoring (res,inps,assumps,fators,sub,fail,vars) -> vars


op traceType(t:TraceTree):String =
  case t of
    | Contra _ -> "(* Contradiction *)"
    | Tauto  _ -> "(* Tautology *)"
    | TIf  _ -> "(* If *)"
    | TCase  _ -> "(* Case *)"
    | TLocal _ -> "(* Local Variable *)"
    | TFactoring _ -> "(* Factoring *)"
      
      
      
% op mkRefinement (i:Int)(qvars:List MSVar)(vars:List (Id * MSType))(assumps:List MSTerm)(pre:DNFRep)(res:MSTerm)(input:CDNFRep): MSTerm =
%    let inp = dnfToTerm (map (map classToTerm) input) in
%    let locals = filter (fn (i:MSVar) -> i.1 in? vars) (freeVars inp) in
%    let quant = case locals of
%                  | [] -> inp 
%                  | _ -> Bind (Exists,locals,inp,noPos) in
%    let ref =
%     Bind (Forall, qvars,
%           mkImplies (mkAnd assumps,
%                   mkImplies(negateTerm (dnfToTerm pre),
%                             mkImplies(res,quant))), noPos) in
%    let _ = writeLine (printTerm ref) in
%    ref


% op mkRefinementThm (qvars:List (Id * MSType))(t:TraceTree):MSTerm =
%     Bind (Forall, qvars,
%           mkImplies (mkAnd (traceAssumptions t),
%                   mkImplies(negateTerm (dnfToTerm (traceFailure t)),
%                             mkImplies(traceResult t,cdnfToTerm (traceInputs t)))), noPos)

op equant (tr:TraceTree):MSTerm =
  if empty? (traceVars tr)
      then cdnfToTerm (traceInputs tr)
      else
        let body = cdnfToTerm (traceInputs tr) in
        let typedVars = liveVars (traceVars tr) body in
        if empty? typedVars
          then body
          else (Bind (Exists,typedVars, body,noPos)) 

% op equant(isabelleTerm:MSTerm -> String)(tr:TraceTree):String =
%   if empty? (traceVars tr)
%       then isabelleTerm (cdnfToTerm (traceInputs tr))
%       else
%         let body = cdnfToTerm (traceInputs tr) in
%         let typedVars = liveVars (traceVars tr) body in
%         if empty? typedVars
%           then isabelleTerm body
%           else isabelleTerm (Bind (Exists,typedVars, body,noPos)) 

op IsaTermPrinter.ppIdStr : String -> String

op mkIsarProof(spc:Spec)(isabelleTerm:MSTerm-> String)(nm : Option String)(t:TraceTree)(uindent:String):String =
  let def inputTerm inps =
        case inps of
          | [] -> mkTrue ()
          | _ -> cdnfToTerm inps in
  let thmName = case nm of | None -> "ok" | Some n -> n in
  
uindent ^ "have " ^ thmName ^ ": \"" ^ (isabelleTerm (mkAnd (traceAssumptions t))) ^
         " ==> (" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure t)))) ^ ")" ^
         " ==> " ^ (isabelleTerm (traceResult t)) ^
         " ==> " ^ isabelleTerm (equant t) ^ "\"\n" ^
uindent ^ "proof - " ^ (traceType t) ^ "\n" ^
(let indent = uindent ^ "  " in         
indent ^ "assume assumptions : \"" ^ (isabelleTerm (mkAnd (traceAssumptions t))) ^ "\"\n" ^
indent ^ "assume fails : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure t)))) ^"\"\n" ^
indent ^ "assume result : \"" ^ (isabelleTerm (traceResult t)) ^ "\"\n" ^

(case t of
     | TIf (result, inputs, assumptions, split, tt, ff, pre, vars) ->
indent ^ "show ?thesis\n" ^
indent ^ "proof (cases \"" ^ (isabelleTerm split) ^ "\")\n" ^
indent ^ "   assume pred: \"" ^ (isabelleTerm split) ^ "\"\n" ^   
indent ^ "     (* True Case *)\n" ^
        
indent ^ "       (* Theorem for subterm *)\n" ^
(mkIsarProof spc isabelleTerm (Some "okTrue") tt (indent ^ "    ")) ^ 

indent ^ "     (* Assumptions for subterm *)\n" ^
indent ^ "     from pred assumptions have assumptions' : \"" ^ (isabelleTerm (mkAnd (traceAssumptions tt))) ^ "\" by auto\n" ^

indent ^ "     (* Failures for subterm *)\n" ^
indent ^ "     from pred fails have fails' : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure tt)))) ^ "\" by auto\n" ^

indent ^ "     (* simplification of resultTerm, given predicate *)\n" ^
indent ^ "     have result' : \"" ^ isabelleTerm (traceResult tt) ^ "\" by (rule iffD1[OF if_P, OF pred, OF result])\n" ^
indent ^ "     have rtrue : \"" ^ isabelleTerm (equant tt) ^ "\" by (fact okTrue[OF assumptions', OF fails', OF result' ])\n" ^

indent ^ "     from pred assumptions rtrue show ?thesis by auto\n" ^
indent ^ "   next\n" ^

indent ^ "     (* False Case *)        \n" ^

   
indent ^ "     assume npred: \"" ^ (isabelleTerm (mkNot split)) ^ "\"\n" ^
indent ^ "     (* Theorem for subterm *)\n"^
(mkIsarProof spc isabelleTerm (Some "okFalse") ff (indent ^ "     ")) ^ 
        
indent ^ "     (* Assumptions for subterm *)\n" ^
indent ^ "     from npred assumptions have nassumptions' : \"" ^ (isabelleTerm (mkAnd (traceAssumptions ff)))  ^ "\" by auto\n" ^
indent ^ "     (* Failures for subterm *)\n" ^
indent ^ "     from npred fails have nfails' : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure ff)))) ^ "\" by auto\n" ^
indent ^ "     (* simplification of resultTerm, given predicate *)\n" ^
indent ^ "     have nresult' : \"" ^ isabelleTerm (traceResult ff) ^ "\" by  (rule iffD1[OF if_not_P, OF npred, OF result])\n" ^
indent ^ "     have rfalse : \"" ^ isabelleTerm (equant ff) ^ "\" by (fact okFalse[OF nassumptions', OF nfails', OF nresult' ])\n" ^
% indent ^ "     from nresult' nassumptions' nfails' okFalse have rfalse : \"" ^ isabelleTerm (cdnfToTerm (traceInputs ff)) ^ "\" by simp\n" ^
indent ^ "     from npred assumptions rfalse show ?thesis by auto\n" ^
indent ^ "qed (* End proof by cases *)\n" ^
uindent ^ "qed\n"    
    | TCase (result,inputs,assumptions,scrutinee,alts,pre,vars) ->
      let def altPrf (pat:MSPattern,pf:TraceTree) =
         let Some pterm = patternToTerm pat in
         % We use 'parenPat' to mark Isabelle cases. If a constructor
         % is nullary, then it's an Isabelle syntax error to put
         % parens around the pattern. So we have to define this little
         % helper function.
         let def parenPat (term:MSTerm):String =
              case term of
                | Apply (_,_,_) -> "(" ^ isabelleTerm pterm ^ ")"
                | _ -> isabelleTerm pterm
         in 
         let eq = isabelleTerm pterm ^ " = " ^ isabelleTerm scrutinee in
         let cons = 
             case pat of
               | EmbedPat (Qualified(_, id),_,_,_) ->  id 
               | _ -> "constructor"
         in
indent ^ "      case " ^ parenPat pterm ^ "\n" ^
indent ^ "\n" ^
mkIsarProof spc isabelleTerm None pf (indent ^ "      ") ^
indent ^ "      from " ^ cons ^ " assumptions have assumptions' : \"" ^
                isabelleTerm (mkAnd (traceAssumptions pf)) ^ "\" by auto\n" ^
indent ^ "      from fails have fails' : \" " ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure pf)))) ^ "\" by auto\n" ^
indent ^ "      from " ^ cons ^ " result have result' :  \"" ^
                isabelleTerm (traceResult pf) ^ "\" by auto\n" ^
indent ^ "      have \"" ^ isabelleTerm (inputTerm (traceInputs pf)) ^ "\" by (fact ok[OF assumptions',OF fails',OF result'] )\n" ^
% indent ^ "      from ok assumptions' fails' result' have \"" ^ isabelleTerm (inputTerm (traceInputs pf)) ^ "\" by simp\n" ^
indent ^ "      from " ^ cons ^ " assumptions result' have comb:\"" ^ isabelleTerm (inputTerm inputs) ^ "\" by auto\n" ^
indent ^ "      from comb show ?thesis  by (rule exI)"

      in

indent ^ "    show ?thesis\n" ^
indent ^ "    proof (cases \"" ^ isabelleTerm scrutinee ^ "\")\n" ^
unlinesPunctuateEnd(indent ^ "      next\n",indent ^ "   qed\n" ,map altPrf alts) ^
uindent ^ "   qed\n"


    | Contra (input, assumptions,vars) ->

indent ^ "assume assumptions : \"" ^ isabelleTerm (mkAnd (traceAssumptions t)) ^ "\"\n" ^
indent ^ "assume fails : \"" ^ isabelleTerm (mkNot (dnfToTerm (traceFailure t))) ^ "\"\n" ^
indent ^ "assume result : \"" ^ isabelleTerm (traceResult t) ^ "\"\n" ^   
indent ^ "from assumptions fails result show ?thesis by auto\n " ^
indent ^ "qed\n"

      
    | TFactoring (res,inps,assumps,factors,sub,fail,vars) ->

mkIsarProof spc isabelleTerm None sub indent ^
indent ^ "from result have factors: \"" ^ isabelleTerm (mkAnd factors) ^ "\" by auto \n" ^   
indent ^ "(* Assumptions for subterm *)\n" ^
indent ^ "from factors assumptions have assumptions' : \"" ^ (isabelleTerm (mkAnd (traceAssumptions sub))) ^ "\" by auto\n" ^
indent ^ "(* Failures for subterm *)\n" ^
indent ^ "from factors fails have fails' : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure sub)))) ^ "\" by auto\n" ^
indent ^ "from result factors  have result': \"" ^ (isabelleTerm (traceResult sub)) ^ "\" by simp\n"  ^   
indent ^ "have rfactor: \"" ^ (isabelleTerm (equant sub)) ^ "\" by (fact ok[OF assumptions', OF fails', OF result'])\n"  ^   
%indent ^ "from ok assumptions' fails'  have rfactor: \"" ^ (isabelleTerm (traceResult sub)) ^ "\" by simp\n"  ^
indent ^  "from factors assumptions rfactor show ?thesis by auto\n" ^
% indent ^ "show ?thesis sorry\n" ^   
uindent ^ "qed\n"


   | TLocal (res,inps,assumps,defvars,sub,fail,vars) ->
     % defvars: List (List (Var * Type) * MSTerm) associating lists of variables with their defs
     let evars = flatten (map (fn (x,_)->x) defvars) in % get all the bound vars
     let edefs = map (fn (_,y)->y) defvars in % get all the definitions for the vars
     % Definition terms
     let defns = (map (fn (vars, defn) ->
                         mkEquality (termType defn, mkTuple (map mkVar vars), defn)) defvars) in
     let defn_conj = mkAnd defns in
     let stpreds = mkAnd (getNonImpliedTypePredicates(evars, defns, false, spc)) in
     let inner = case res of
                   | Bind(Exists, vs, bod, _) -> bod
                   | _ -> res
     in
 (* Do this first, to fix the existentially quantified variable *)
% FIXME: The following step sometimes fails, but will succedd when the proof is replaced with '(rule conjE)'. WTF?
indent ^ "from result obtain " ^ flatten (intersperse " " (map (fn x -> IsaTermPrinter.ppIdStr (x.1)) evars)) ^ " where inner: \"
" ^ isabelleTerm inner ^ "\" and esubs: \"" ^ isabelleTerm stpreds ^ "\" by (auto)\n" ^

% indent ^ "(* SUBTYPES " ^ isabelleTerm stpreds ^ "*)\n" ^
mkIsarProof spc isabelleTerm (Some "ok_local") sub indent ^

% indent ^ "from inner have esubs: \"" ^ isabelleTerm stpreds ^ "\"\n" ^
indent ^ "from inner have defns : \"" ^ isabelleTerm defn_conj ^ "\" by auto\n" ^
indent ^ "from assumptions defns have assumptions': \"" ^ isabelleTerm (mkAnd (traceAssumptions sub)) ^ "\" by auto\n" ^
indent ^ "from fails have fails' : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure sub)))) ^ "\" by auto\n" ^
indent ^ "from inner have result' : \"" ^ isabelleTerm (traceResult sub) ^ "\" by (auto simp only:)\n" ^
indent ^ "have sub_done : \"" ^ isabelleTerm (equant sub) ^ "\" by (fact ok_local[OF assumptions', OF fails', OF result'])\n" ^
indent ^ "from sub_done defns esubs show ?thesis by blast\n" ^ 
%   indent ^ "show ?thesis sorry\n" ^
uindent ^ "qed\n"

    | Tauto (inps, assumps, vars) ->
indent ^ "show ?thesis by simp\n" ^
uindent ^ "qed\n"



    | _ ->
indent ^ "(* CATCHALL *)\n" ^
indent ^ "show ?thesis sorry\n" ^
uindent ^ "qed\n"
))


% Return the predicate (as an MSTerm) that is "proved" by a TraceTree.
% README: This assumes the TraceTree that is "top-level", i.e., that
% it is not a sub-tree of some larger TraceTree. Non-top-level
% TraceTrees can have traceAssumptions, which are not covered here.
% Also, a TraceTree does not actually contain the original
% post-condition of the op before the refinement, as mergeRules
% unfolds all of the variables first; thus we must include the
% original post-condition here.
op MergeRules.mergeRulesPredicate (t:TraceTree, orig_postCondn: MSTerm) : MSTerm =
  mkImplies (mkNot (dnfToTerm (traceFailure t)),
             mkImplies (traceResult t, orig_postCondn))

op MergeRules.printMergeRulesProof(spc:Spec)(isabelleTerm:MSTerm -> String)
                                  (boundVars:MSVars)(t:TraceTree)
                                  (unfolds:List QualifiedId)
                                  (smtArgs:List QualifiedId):String =
   let _ = writeLine "Generating MergeRulesProof (In MetaProgram)" in
   let indent =  "  " in
   let fun_defs = flatten (intersperse " " []) in
   let unfold_ids = flatten (intersperse " " (map (fn q -> mainId q ^ "_def") unfolds)) in
   let smtcall = case smtArgs of
                  | [] -> "fastforce"  % "smt2"
                  | _ -> "fastforce"   % "(smt2 " ^ flatten (intersperse " " (map (fn q -> mainId q) smtArgs)) ^ ")"
   in
   
% indent ^ "proof -\n" ^
mkIsarProof spc isabelleTerm None t (indent ^ "  ") ^
indent ^ "(* Final Refinement Step XXXX *)\n" ^

% indent ^ "(*\n" ^
indent ^ "assume result : \"" ^ isabelleTerm (traceResult t) ^ "\"\n" ^
indent ^ "have noassumptions : True by simp\n" ^
indent ^ "assume precondition : \"" ^ (isabelleTerm (mkNot (dnfToTerm (traceFailure t)))) ^ "\"\n" ^
indent ^ "have unfolded: \"" ^ isabelleTerm (equant t) ^ "\" by (fact ok[OF noassumptions, OF precondition, OF result])\n" ^
indent ^ "show \"?thesis" ^ (flatten (intersperse " " (map (fn (id,_) -> id) boundVars))) ^ "\"\n" ^
indent ^ "  apply (unfold " ^ unfold_ids ^ " )\n" ^
indent ^ "  apply (simp only:split_conv)\n" ^
indent ^ "  apply (cut_tac unfolded)\n" ^
indent ^ "  apply " ^ smtcall ^ "\n" ^
indent ^ "done"




op unlines(l:List String):String =
  case l of
    | [] -> ""
    | x::xs -> x ^ "\n" ^ unlines xs

op unlinesPunctuateEnd(p:String,e:String,l:List String):String =
  case l of
    | [] -> e
    | [x] ->  x ^ "\n" ^ e
    | x::xs -> x ^ "\n" ^ p ^ "\n" ^ unlinesPunctuateEnd(p,e,xs)
      
type Assumption =
  | DefAssumption MSTerm
  | BranchAssumption MSTerm

op branchAssumption(a:Assumption):Bool =
  case a of
    | BranchAssumption _ -> true
    | _ -> false

op branchAssumptions(assumps:List Assumption):List Assumption =
  filter branchAssumption assumps

op unAssumption(a:Assumption):MSTerm =
  case a of
    | BranchAssumption t -> t
    | DefAssumption t -> t

op noAssumptions(assumps:List Assumption):List MSTerm =
  map unAssumption assumps

      
% Package up the arguments to bt and auxillary functions.
% The spc, obs, and stateVar fields should be constant,
% but assumptions and vars will vary.
type BTArgs = { spc:Spec,
                obs:List Id,
                outputs : List Id,
                stateVar:Id,
                assumptions:List Assumption,
                vars:List (Id * MSType)
               }
op addAssumption(args:BTArgs)(a:Assumption):BTArgs =
  args << { assumptions = a::(args.assumptions) }
op addAssumptions(args:BTArgs)(a:List Assumption):BTArgs =
  args << { assumptions = a ++ (args.assumptions) }

op setVars(args:BTArgs)(vs:List (Id * MSType)):BTArgs =
  args << { vars = vs }


op varsNames(args:BTArgs):List Id =
   map (fn v -> v.1) args.vars

op diffVars(l1:List (Id*MSType))(l2:List(Id*MSType)):List(Id*MSType) =
   let ids = map (fn (v:Id*MSType) -> v.1) l2 in
    filter (fn (v1:Id*MSType) -> ~(v1.1 in? ids)) l1

op liveVars(vs:List(Id*MSType))(t:MSTerm):List(Id*MSType) =
   let live = map (fn v -> v.1) (freeVars t) 
   in filter (fn (v,ty) -> v in? live) vs


op bt2'(args:BTArgs)(inputs:List (List CClass)):(MSTerm * DNFRep * TraceTree) =
      let (res,fail,pf) = bt2' args inputs in
      let _ = writeLine "Call bt2 with" in
      let _ = writeLine ("assumptions:" ^ printTerm (mkAnd (noAssumptions args.assumptions))) in
      let _ = writeLine ("inputs: " ^ (printTerm (cdnfToTerm inputs))) in
      let _ = writeLine ("result: " ^ (printTerm res)) in
      let _ = writeLine ("failure: " ^ (printTerm (dnfToTerm fail))) in
      (res,fail,pf)

op bt2(args:BTArgs)(inputs:List (List CClass)):(MSTerm * DNFRep * TraceTree) =
   if empty? inputs
     % If the set of input clauses is empty, then we have a contradiction.
     then (mkFalse (),  [noAssumptions (branchAssumptions args.assumptions)], Contra (inputs, noAssumptions args.assumptions,args.vars))
     else
       if (exists? empty? inputs)
         then
         % 1. If any of the clauses lists are empty, then that corresponds
         %    to 'true'. What to do with that???
          (mkTrue (), [], Tauto (inputs, noAssumptions args.assumptions,[]))
       else
         % 2. If there are any global constraints on postState or
         % on return values.
         let gcs = globalConstraint args inputs
         in if ~(empty? gcs)
             then
               let terms = map classToTerm  gcs in               
               % let _ = writeLine "There are  global constraints" in
               % let _ = map (fn x -> writeLine (printTerm x)) terms in
               let next =
                  map (fn clause -> List.filter (fn atom -> ~(inClause? atom gcs)) clause) inputs in
               let (tm',pre,pf1) = bt2 (addAssumptions args (map DefAssumption terms)) next in
               let resTerm = mkAndMaybe (terms, tm', pf1) in
               let pf = TFactoring  (resTerm, inputs, noAssumptions args.assumptions,terms,pf1,pre, args.vars) in
               (resTerm, pre,pf) 
            else
              % let _ = writeLine "There are no global constraints" in
              % 3. If there are global definitions of local variables.
              let gds = nubBy (uncurry equalClass?) (globalDef args inputs) in
              if ~(empty? gds)
                then 

                  let terms : List MSTerm = map classToTerm  gds in
                  % let _ = writeLine "There are global definitions" in
                  % let _ = map (fn x -> writeLine (printTerm x)) terms in

                  % Sometimes we'll have (x,y) = f(1,3) && x = 0. Both
                  % of these will appear syntactically as a definiton
                  % of local variables. However, what we really want
                  % is to first define x and y, then constraint x to 0
                  % (that is, the `CDef x 0` should become CAtom (x = 0)

                  let next : List (List CClass) =
                    map (fn c -> List.filter (fn a -> ~(inClause? a gds)) c) inputs in
                  let defsToAtoms = defineLocals gds next in                    
                  let tvars : List (Id * MSType) = (flatten (map defVars gds)) in
                  % let dvars = map (fn v -> v.1) tvars in 
                  let newAssumptions =  (map classToTerm gds) in
                  let (t',p,pf1) =
                     % bt2 (setVars (addAssumptions args newAssumptions)
                     %        (diff (args.vars, tvars))) defsToAtoms in
                     bt2 (setVars (addAssumptions args
                                     (map DefAssumption newAssumptions))
                            (diffVars args.vars tvars)) defsToAtoms in

                  let resTerm = Bind (Exists, tvars, mkAndMaybe (newAssumptions, t', pf1),noPos) in
                  % FIXME!!! Supply the defs, instead of []
                  let defs = map (fn | CDef (vs,defn,_,_,_,_) -> (vs,defn)) gds in 
                  let pf = TLocal (resTerm, inputs,noAssumptions args.assumptions, defs, pf1, p, args.vars) in
                  (resTerm, p, pf)
              else
                % let _ = writeLine "There are no global definitions" in
                % 4. Choose an Atom or Case to split on.
                let splits = filter (isSplit args) (flatten inputs)
                in case splits of
                    | ((a as CAtom _)::_) ->
                      % let _ = writeLine ("Splitting on an atom " ^
                      %             printTerm (classToTerm a)) in
                      % The 'positive' branch.
                      let pos : List (List CClass) = simplifySplit a inputs in
                      % The 'negative' clashing branch.
                      let neg : List (List CClass) =
                         simplifySplit (negateClass a) inputs in
                      let (tb,tp,pf1) = bt2 (addAssumption args (BranchAssumption (classToTerm a))) pos in
                      let (eb,ep,pf2) =
                         bt2 (addAssumption args (BranchAssumption (classToTerm (negateClass a)))) neg in
                      let resTerm = IfThenElse (classToTerm a, tb, eb, noPos) in
                      let precondition = (tp ++ ep) in
                      let pf = TIf (resTerm, inputs, noAssumptions args.assumptions, classToTerm a,pf1,pf2, precondition,args.vars) in 
                      (resTerm, precondition, pf)

                    | ((a as CCase (_,scrutinee,_,_,ty))::_) ->
                      % let _ = writeLine ("Splitting on a construction  " ^
                      %                      printTerm (classToTerm a)) in
                      let (branchClauses,unhandled) = simplifyCaseSplit args a inputs in
                      % Branch construction
                      let def mkAlt (pat,clauses) =
                               let Some patTerm = patternToTerm pat in
                               let eq = mkEquality (ty,scrutinee,patTerm) in
                               let (tm',pres,pfAlt) = bt2 (setVars (addAssumption args (DefAssumption eq))
                                                       (removePatternVars args.vars (Some pat))) clauses in
                               ((pat,tm'),pres,pfAlt)
                      in
                      let branches =
                            let alts = map mkAlt branchClauses
                            in case unhandled of
                                | Some clauses -> let (tm',pres,pf) = bt2 args clauses in
                                                  let default = ((mkWildPat ty, tm'),pres,pf) in 
                                                  alts ++ [default]
                                 | _ -> alts
                      in
                      let pres : DNFRep = flatten (map (fn x -> x.2) branches) in
                      let pfAlts = map (fn x -> (x.1.1, x.3)) branches in
                      let resTerm = mkCaseExpr (scrutinee, (map (fn x -> x.1) branches)) in
                      let pf = TCase (resTerm, inputs, noAssumptions args.assumptions, scrutinee, pfAlts,  pres, args.vars) in
                      (resTerm, pres, pf)
                              
                    | _ ->
                      let _ = writeLine "ERROR: Mergerules is stuck." in
                      let _ = writeLine "Under assumptions:" in
                      let _ = writeLine (printTerm (mkAnd (noAssumptions args.assumptions))) in
                      let _ = writeLine "Merging clauses" in
                      let _ = writeLine (printDNF (map (map classToTerm) inputs)) in
                      % let _ = debugClauses inputs in
                      let _ = debugFailure args inputs in
                      (mkVar ("<<<Failure Here>>>",boolType), [], Unknown)
                      
  



%%%%%%%%%%%%%%%%%%%%%%
%%% Postconstraints
%%%%%%%%%%%%%%%%%%%%%%

%% Given a spec `spc` and a state type `s`, find the names of all of
%% the observers of the state, which are ops of the form::
%%
%%   `op obs_i : s -> a`
%%
%%  where `a` /= `s`, or where `a` is a tuple type, and `s` is not one
%%  of the field types.
op findObservers(spc:Spec)(s:MSType):List Id =
  let ois = opInfosAsList spc in
  let observerInfos = filter (isObserver? s) ois in
  let observerNames = map (fn oi -> mainId (primaryOpName oi)) observerInfos in
  % let _ = writeLine "Found Observers:" in
  % let _ = map writeLine observerNames in
  observerNames

  
%% Given a state type, return true if the op is a function from the
%% state type to a (different type).
%% Arguments:
%%  `s`: The state type.
%%  `o`: The OpInfo for an spec operation.
%% Returns:
%%  true if the type of the op is `{ s | P } -> {a | Q}`
%%    where the subtype constraints on the domain and range are
%%    optional, and `a` != `s` and, if `a` is a tuple, `s` does not appear as
%%    one of the types of the tuple.
%%  false otherwise.
op isObserver?(s:MSType)(o:OpInfo):Bool =
  let (tvs,ty,body) = unpackFirstTerm o.dfn in
  case isArrowType? ty of
   |Some (dom, ran) ->
         (equalTypeSubtype? (s, dom, true)) &&
         (if isTupleType? ran
          then ~ (inBy? (fn (x, y) -> equalTypeSubtype? (x, y, true))  s (tupleTypes ran))
          else ~ (equalTypeSubtype?(s, ran, true)))
   | None -> false                       

%% These functions have analogues in Languages/MetaSlang/Utilities, or
%% Languages/MetaSlang/Elaboration/Typechecker but those require a
%% spec as an argument, so that types can be unfolded, or are monadic. 
op isTupleType?(ty:MSType):Bool =
  case ty of
    | Product _ -> true
    | _ -> false

op tupleTypes(ty:MSType): MSTypes =
  case ty of
    | Product (fields,_) -> map (fn (_,t) -> t) fields
    | _ -> []

      
op isArrowType?(ty:MSType):Option (MSType * MSType) =
   case ty of
     | Arrow (dom,ran,_) -> Some (dom,ran)
     | _ -> None



%%%%%%%%%%%%%%%%%%%%%%
%%% Definitions
%%%%%%%%%%%%%%%%%%%%%%


op removePatternVars (vars:List (Id * MSType))(pat:Option MSPattern):List (Id * MSType) =
  case pat of
    | None -> vars
    | Some thePat -> 
       case patternToTerm thePat of
         | None -> vars
         | Some t -> let fvs = varNames (freeVars t)
                     in filter (fn (v,t) -> ~(v in? fvs)) vars


%%%%%%%%%%%%%%%%%%%%%%
%%% Utility functions.
%%%%%%%%%%%%%%%%%%%%%%


% Remove duplicate elements (inefficient, as is most stuff in this module ..)
op nub (l:MSTerms):MSTerms = nubBy equalTermAlpha? l

op [a] nubBy (p:a * a -> Bool)(l:List a):List a =
  case l of 
    | [] -> []
    | (x::xs) | exists? (fn y -> p (x,y)) xs -> nubBy p xs
    | (x::xs) -> x::(nubBy p xs)

op [a,b,c] uncurry (f: (a -> b -> c))((x,y):(a*b)):c =
  f x y
  
%% Set membership, over an arbitrary equivalence.
op [a] inBy? (p:(a*a)->Bool)(e:a)(l:List a):Bool =
   case l of 
     | [] -> false
     | (x::xs) -> p (e, x) || inBy? p e xs


% %%% Set membership, specialized to using the 'equalTerm?' relation.
op inTerm? (c:MSTerm) (l:MSTerms):Bool = inBy? equalTermAlpha? c l


op printIt ((vs,xs) : (ExVars * DNFRep)):() =

   let _ = map (fn d -> % let _ = writeLine "Conjunction:" in
                        % let _ = writeLine (anyToString vs ) in
                        map (fn c -> writeLine ("\t" ^ printTerm c)) d) xs
   in ()

%% Guard on a condition. Raise an exception with the given message if
%% the input condition is false.
op guard(p:Bool)(msg:String):Env () =
  if p then return () else raise (Fail msg)


%%% Classification of clauses
type CClass =
  | CAtom (MSTerm * (List Id) * Bool * MSType) % Term * Referenced existentials 
  | CDef (List (Id * MSType) * MSTerm * List Id * Bool * MSType * MSType) 
    % Defined variables * definition * referenced variables
  | CConstrain (MSTerm * MSTerm * List Id * Bool * MSType)
    % poststate/return value * definition * referenced variables
  | CCase (MSPattern * MSTerm * List Id * Bool * MSType)

% Recognizers for the various classes.
op isAtomClass(c:CClass):Bool =
  case c of
    | CAtom _ -> true
    | _ -> false


op isTrueAtom?(c:CClass):Bool =
  case c of
    | CAtom (t,_,_,_) -> trueTerm? t
    | _ -> false

op isFalseAtom?(c:CClass):Bool =
  case c of
    | CAtom (t,_,_,_) -> falseTerm? t
    | _ -> false

op isDefClass(c:CClass):Bool =
  case c of
    | CDef _ -> true
    | _ -> false

op isConstrainClass(c:CClass):Bool =
  case c of
    | CConstrain _ -> true
    | _ -> false

op isCaseClass(c:CClass):Bool =
  case c of
    | CCase _ -> true
    | _ -> false

op isSplit(args:BTArgs)(c:CClass):Bool =
  (isAtomClass c || isCaseClass c) && fullyDefined? args c

op casePattern (c:CClass):MSPattern =
  case c of
    | CCase (pat,_,_,_,_) -> pat

% Is a clause c in a list of clauses.
op inClause?(c:CClass)(l:List CClass):Bool =
  case l of
   | [] -> false
   | (x :: xs) -> equalClass? c x || inClause? c xs

% Are two atomic terms equal.
op equalClass?(c1:CClass)(c2:CClass):Bool =
  case (c1,c2) of
    | (CAtom (t,_,b1,ty1), CAtom (u,_,b2,ty2)) ->
        equalTermAlpha? (t,u) && (b1 = b2) && equalType? (ty1,ty2)
    | (CDef (d1,t1,_,b1,ty11,ty12), CDef (d2,t2,_,b2,ty21,ty22)) ->
        equalTermAlpha? (t1,t2) && (b1 = b2) && equalType? (ty11,ty21)
    | (CConstrain (d1,t1,_,b1,ty1), CConstrain (d2,t2,_,b2,ty2)) ->
        equalTermAlpha? (t1,t2) && (b1 = b2) && equalType? (ty1,ty2)
    | (CCase (p1,t1,_,b1,ty1), CCase (p2,t2,_,b2,ty2)) ->
        equalTermAlpha? (t1,t2) && equalType? (ty1,ty2)
    | _ -> false        


op classToTerm(c:CClass):MSTerm =
  let def n b t = if b then t else negateTerm t in
  case c of
    | CAtom (t,ids,b,_) -> n b t 
    | CDef ([v], t, deps,b,ty1,ty2) ->
        n b (mkEquality (ty1,mkVar v,t)) %  (TypedTerm (t,ty2,noPos))))
    | CDef (vs, t, deps,b,ty1,ty2) ->
        let vars = mkTuple (map MS.mkVar vs) in
        n b (mkEquality (ty1,vars, t)) %  (TypedTerm (t,ty2,noPos))))
    | CConstrain (v, t, deps,b,ty) ->
        n b (mkEquality (ty, v, t))
    | CCase (pat, t, deps,b,ty) ->
        let Some u = patternToTerm pat in
        n b (mkEquality (ty, u, t))

op cdnfToTerm(input:List (List CClass)):MSTerm =
    dnfToTerm (map (map classToTerm) input)
        
% Get all of the atoms satisfying a criteria.
op gatherAtoms(p:CClass -> Bool)(cs:(List (List CClass))):List CClass =
  nubBy (uncurry equalClass?) (flatten (map (filter p) cs))

% Remove all of the atoms satisfying a criteria
op removeAtoms(p:CClass -> Bool)(cs:(List (List CClass))):List (List CClass) =
   map (filter p) cs

        
% An atom is a global definition for a set of clauses if it is a def
% and it is fully defined and it occurs in each of the input clauses.
op globalAtom(args:BTArgs)(cpred:(CClass -> Bool))(clauses:List (List CClass)):(List CClass) =
   let atoms = gatherAtoms cpred clauses in
   let defined = filter (fullyDefined? args) atoms in
   let occurs = filter
      (fn d -> forall? (fn clause -> inClause? d clause) clauses) defined
   in occurs
  
op globalConstraint(args:BTArgs)(clauses:List (List CClass)):(List CClass) =
  globalAtom args isConstrainClass clauses

op globalDef(args:BTArgs)(clauses:List (List CClass)):(List CClass) =
  globalAtom args isDefClass clauses



  
op printClass(c:CClass):String =
  let def lead x = if x then "+" else "-" in
  case c of
    | CAtom (t,ids,b,_) -> lead b ^ "atom[" ^ printTerm t ^ "]"
    | CDef (vs, t, deps,b,_,_) ->
       let def vars start = foldr (fn ((v,ty), acc) -> v ^ " " ^ acc) start vs in  
       lead b ^ "def[" ^ vars "/" ^  printTerm t ^ "]"
    | CConstrain (v, t, deps,b,_) ->
         lead b ^  "cons[" ^ printTerm v ^ "/" ^ printTerm t  ^ "]"
    | CCase (pat, t, deps,b,_) ->
         lead b ^ "case[" ^ printPattern pat ^ "/" ^ printTerm t  ^ "]"

op debugClauses(l:List (List CClass)):() =
  case l of
    | [] -> ()
    | (c::cs) ->
      let _ = writeLine "Clause" in
      let _ = map (fn a -> writeLine (printClass a)) c in
      debugClauses cs
      
    

         
op negateClass(c:CClass):CClass =
  case c of
    | CAtom (t,ids,b,ty) -> CAtom (t,ids,~b,ty)
    | CDef ([v], t, deps,b,ty1,ty2) -> CDef ([v], t, deps,~b,ty1,ty2)
    | CConstrain (v, t, deps,b,ty) -> CConstrain (v, t, deps,~b,ty)
    | CCase (pat, t, deps,b,ty) -> CCase (pat, t, deps,~b,ty)


op simplifySplit(c:CClass)(l:List (List CClass)):List (List CClass) =
       let noNegs = filter (fn c' -> ~(inClause? (negateClass c) c')) l
       in map (fn clause -> filter (fn d -> ~(equalClass? c d)) clause) noNegs

% Return a list of (Pattern,clauses that don't conflict with that pattern), as well as a list of unhandled clauses.         
op simplifyCaseSplit(args:BTArgs)(c:CClass)(l:List (List CClass)):List (MSPattern * List (List CClass)) *(Option (List (List CClass))) =
  case c of
     | CCase (pat, s, vars,_,_) ->
       % Collect all of the terms constraining the same scrutinee
       let sameCases = flatten (map (fn clause -> filter (fn a -> equalClass? c a) clause) l) in
       % Eliminate duplicates., only get the patterns.
       let noDups : List MSPattern =
          nubBy equalPattern? (map casePattern sameCases) in
       % For each pattern, we want to filter out all of the clauses
       % that clash; that means that the clause either contains an
       % atom that constrains the scrutinee to a different pattern, or
       % else constrains the scrutinee to the same pattern but with a
       % different polarity.
       let def clauseClash (p:MSPattern) (clause:List CClass) =
               exists? (fn a -> equalClass? c a &&   % Do these constrain the same scrutinee. This is redundant in context.
                           (if equalPattern? (casePattern a, p)
                              then ~(atomPolarity a)
                              else (atomPolarity a))) clause in
                    
       % For each pattern pat, return pat paired with the clauses that don't clash.
       let matchingClauses : List (MSPattern * List (List CClass)) =
            map (fn p -> (p,filter (fn clause -> ~ (clauseClash p clause)) l)) noDups in
       % For each pattern pa, return pat paired with the matching
       % clause, with the constraint on the scrutinee removed.
       let def clauseMatch (p:MSPattern) (a:CClass) : Bool =
          case a of
            | CCase (p', s',_,_,_) -> equalPattern? (p,p') || ~(atomPolarity a)
            | _ -> false
       in
       let filteredClauses : List (MSPattern * List (List CClass)) =
       List.map (fn (p,clauses) -> (p,map (fn clause -> filter (fn a -> ~(clauseMatch p a)) clause) clauses))  matchingClauses in
       % A unhandled clause is one which clashes with every other pattern.
       let unhandled = filter (fn clause -> forall? (fn p -> clauseClash p clause) noDups) l in
       % Remove constraints on the scrutinee appearing in unhandled.
       let unhandled' = map (fn clause -> filter (fn a -> ~ (equalClass? a c)) clause) unhandled in
       if empty? unhandled'
         then if (exhaustivePatterns? (noDups, inferType(args.spc, s), args.spc))
                then (filteredClauses, None)
              else (filteredClauses, Some [])
       else
         (filteredClauses, Some unhandled')
     

      
% Get the variables an atom depends on.
op atomDeps(c:CClass):List Id =
   case c of
     | CAtom (_,deps,_,_) -> deps
     | CDef (_,_,deps,_,_,_) -> deps
     | CConstrain (_,_,deps,_,_) -> deps
     | CCase (_,_,deps,_,_) -> deps


% Get the variables an atom depends on.
op atomPolarity(c:CClass):Bool =
   case c of
     | CAtom (_,_,b,_) -> b
     | CDef (_,_,_,b,_,_) -> b
     | CConstrain (_,_,_,b,_) -> b
     | CCase (_,_,_,b,_) -> b
       

% An atom is fully defined if none of its dependencies occur
% in the list of args
op fullyDefined?(args:BTArgs)(c:CClass):Bool =
   forall? (fn v -> ~(v in? (map (fn x -> x.1) args.vars))) (atomDeps c)

% The variables defined by a def
op defVars(c:CClass):List (Id * MSType) =
  case c of
    | CDef(vars,_,_,_,_,_) -> vars
    | _ -> []


op classifyClause (args:BTArgs) (l:List MSTerm):List CClass =
  classifyClauseHelper args args.vars l

op classifyClauseHelper (args:BTArgs)(undefVars:List (Id * MSType))(l:List MSTerm):List CClass = 
 case l of
  | [] -> []
  | (t::ts) ->
    case classify args undefVars t of
      % When defining, we remove the set of defined vars from the set
      % of all variables -- this prevents some misclassification of
      % some terms as definitions, when the really should be CCase
      % (e.g. v1 = Some v2, where v1 and v2 are both ex. quant.
      % variables, or 'h1 = 1', when h1 is a variable defined by an
      % earlier clause. This does require an ordering on the clause,
      % where 'definitions' should come before usage.
      | c as CDef (dvars, defn, refs, b, t1, t2) ->
        let newVars = diffVars (args.vars) dvars in
        c::(classifyClauseHelper args newVars ts)
      | c as CCase (pat, _, _,_, _) ->
        let newVars = diffVars (args.vars) (patternVars pat) in
        c::(classifyClauseHelper args newVars ts)
      | c -> c::(classifyClauseHelper args undefVars ts)


op debugClassify? : Bool = false
op traceClassify(s:String):() =
  if debugClassify? then writeLine s else ()

% Given a term, classify it 
op classify(args:BTArgs)(undefVars:List (Id * MSType))(t:MSTerm):CClass =
  let _ = traceClassify ("Classifying " ^ printTerm t) in
  let t' = classifyAux args undefVars t in
  let _ = traceClassify (printClass t') in
  t'

op classifyAux(args:BTArgs) (undefVars:List (Id * MSType)) (t:MSTerm):CClass =

  let def theVars tm = map (fn x -> x.1) (filter (fn (i,_) -> i in? (map (fn v -> v.1) args.vars)) (freeVars tm)) in
  let def getTy (tm:MSTerm):MSType = inferType (args.spc,tm) in
  let def getEqTy (ty:MSType):MSType =
             case ty of
               | Arrow (Product(dom::doms,_),ran,_ ) -> dom.2
  in
  case t of
    % ~(expr)
    | Apply(Fun(Not,_,_), arg, appPos) -> negateClass (classifyAux args undefVars arg)
    
    % s' = expr
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
       | v = args.stateVar ->
      CConstrain (l,r,theVars r,true,getEqTy eqTy)

    % expr = s' 
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v = args.stateVar -> CConstrain (r,l,theVars l,true,getEqTy eqTy)

    % obs s' = expr        
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,
                       l as Apply (Fun (Op (Qualified (_,o),opFix),ftype,fPos),
                              (Var ((v,_),varPos)),
                              appPos)),
                       (_,r)], argPos), _)
      | o in? args.obs && v = args.stateVar -> CConstrain (l,r,theVars r,true,getEqTy eqTy)

    % expr = obs s'
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l),
                       (_,r as Apply (Fun (Op (Qualified (_,o),opFix),ftype,fPos),
                              (Var ((v,_),varPos)),
                              appPos)
                        )], argPos), _)
      | o in? args.obs && v = args.stateVar -> CConstrain (r,l,theVars l,true,getTy l)

    % result = expr
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
      | v in? args.outputs -> CConstrain (l,r,theVars r,true, getEqTy eqTy)

    % expr = result
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v in? args.outputs -> CConstrain (r,l,theVars l,true, getEqTy eqTy)

    % (v1,...,vn) = expr
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos)
      | let pvars = patternVars l in ~(empty? pvars) && forall?  (fn v -> v.1 in? (map (fn v -> v.1) undefVars)) pvars -> CDef (patternVars l,r,theVars r,true, getEqTy eqTy,getTy r)
        
    % v = expr
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
      | v in? (map (fn v -> v.1) undefVars) -> CDef ([(v,ty)],r,theVars r,true,getEqTy eqTy,getTy r)


    % expr = (v1,...,vn) 
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos)
      | let pvars = patternVars r in ~(empty? pvars) && forall?  (fn v -> v.1 in? (map (fn v -> v.1) undefVars)) pvars -> CDef (patternVars r,l,theVars l,true, getEqTy eqTy, getTy l)
        
    % expr = v
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v in? (map (fn v -> v.1) undefVars) -> CDef ([(v,ty)],l,theVars l,true, getEqTy eqTy, getTy l)

        
    | Apply (Fun (Equals,eqTy,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos) ->
        (case termToPattern r of
              | Some (pat as EmbedPat (con,vars,pty,_)) ->
                % expr = pat
                  CCase (pat, l, theVars l,true, getTy l)
              | _ ->  (case termToPattern l of
                           | Some (pat as EmbedPat (con,vars,pty,_)) ->
                             % pat = expr
                             CCase (pat, r, theVars r,true, getTy r)
                           | _ -> CAtom (t,theVars t,true, boolType)))

   % otherwise
   | _ -> CAtom (t,theVars t,true,boolType)


% If a term is of the form `x` or `(x1,x2,..., xn)`, where
% `xi` is a variable, then this will return the list of xs.
op patternVars(l:MSTerm):List (Id * MSType) =
   let ts = termToList l in
   let def unVar x = case x of | Var (v,_) -> v  in
   if (forall? isVar? ts)
     then map unVar ts
   else []


% Sometimes we'll have (x,y) = f(1,3) && x = 0. Both of these will
% appear syntactically as a definiton of local variables. However,
% what we really want is to first define x and y, then constraint x to
% 0 (that is, the `CDef x 0` should become CAtom (x = 0)
op defineLocals(defs:List CClass)(clauses:List (List CClass)):(List (List CClass)) =
   let vars : List (Id * MSType) = flatten (List.map defVars defs) in
   % let _ = writeLine "Updating locals" in
   % let _ = List.map (fn i -> writeLine i.1) vars in
   let def toPred atom =
           case atom of
             | CDef ([var as (v,ty)],t,deps,b,_,_) ->
                 if exists? (fn (v',ty') -> v' = v && equalType? (ty, ty')) vars
                   then % let _ = writeLine ("Updated" ^ printClass atom) in
                     case termToPattern t of
                       | Some pat -> % If the term is a construction, then we turn it into a CCase, not an Atom.
                          CCase (pat, mkVar var, [v],true, ty)
                       | None -> CAtom (mkEquality (ty,mkVar (v,ty),t), v::deps, b,boolType)
                 else % let _ = writeLine ("Skipping" ^ printClass atom) in
                      atom
             | _ -> atom
   in map (map toPred) clauses


op debugFailure(args:BTArgs)(clauses:List (List CClass)):() =
  let def debugClass c =
           let _ = writeLine ("Literal:\n\t " ^ (printClass c)) in
           let undef : List Id = filter (fn d -> d in? (map (fn v -> v.1) args.vars)) (atomDeps c) in
           let _ = if ~(empty? undef)
                      then let _ = writeLine "Depends on undefined vars: " in
                           let _ = map (fn i -> writeLine ("\t" ^ i)) undef in
                           ()
                   else writeLine "Fully defined."
           in
           case c of
            |  CConstrain (var,t, deps, b,_) ->
                let _ =
                   if (exists? (fn clause -> ~(exists? (fn a -> equalClass? a c) clause)) clauses)
                     then writeLine "Constraint does not appear globally."
                   else writeLine "Constraint appears globally."
                in writeLine ""

            |  CDef (vars,t,deps, b,_,_) ->
                let _ =
                   if (exists? (fn clause -> ~(exists? (fn a -> equalClass? a c) clause)) clauses)
                     then writeLine "Definition does not appear globally."
                   else writeLine "Definition appears globally."
                in writeLine ""
                
             | _ -> ()
  in
  let def debugClause clause =
     let _ = writeLine "Clause" in
     let _ = List.map debugClass clause in
     ()
  
  in
  let _ =  List.map debugClause clauses in
  ()
  

%%%%%%%%%%%%%%%
%%% Resolution
%%%%%%%%%%%%%%%


%% Code for converting a CNF representation to DNF.
op cnf2Dnf (i:List MSTerms):DNFRep =
   case i of
     | [] -> [[]]
     | c::cs -> let tl = cnf2Dnf cs 
                in flatten (map (fn l -> map (fn rest -> l::rest) tl) c)

%% Given two lists of atomic formulae, find all formula that
%% occur positively in on list and negatively in the other.
op complements (ps:MSTerms) (qs:MSTerms):MSTerms =
  filter (fn p -> inTerm? (negateTerm p) qs) ps

%% Perform one step multi-resolution between a pair of disjunctions of
%% formulas.
op resolution (ps:MSTerms) (qs:MSTerms):Option MSTerms =
    let cs = complements ps qs in
    let cs' = cs ++ map negateTerm cs in
    if empty? cs then None 
    else Some ( filter (fn x -> ~ (inTerm? x cs) ) (ps ++ qs))

%% Resolve one disjunction of formulas, ps,  with each of the disjunctions in qs.
op resolveOne (ps:MSTerms)(qs:List MSTerms) (changed?:Bool):List MSTerms =
  case qs of 
    | [] | changed? -> []
    | [] | ~ changed? -> [ps]
    | (q::qss) ->  
      case resolution ps q of
        | None -> q::(resolveOne ps qss changed?)
        | Some resolvant -> resolvant::(resolveOne ps qss true)

%% Given a ***CNF*** representation of formulas, perform resolution to
%% simplify them.
op resolveAll (ps:List MSTerms):List MSTerms =
  case ps of
    | [] -> ps
    | (p::pss) -> resolveOne p (resolveAll pss) false


%% Code for negating then simplifying DNF.
%% Input: 
%%    r, a DNF formula represented as a list of lists.
%% Returns:
%%   a DNF formula equivalent to the negation of r.
op negateDNF(r:DNFRep):DNFRep = 
  let cnf = map (fn c -> map negateTerm c) r in
  let r' = cnf2Dnf (resolveAll cnf) in
  r'

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Rewriting Utilities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Beta-Reduction
op betan_step (t:MSTerm):MSTerm =
  case t of
     | Apply(Lambda([(pat,_,body)],_),argument,pos) ->
         % let _ = writeLine ("Beta-reducing:\n " ^ printTerm t) in
         let def norestrict p = case p of | RestrictedPat (p',_,_) -> p' | _ -> p
         in
         let boundVars =
             case norestrict pat of
               | VarPat(v,_)            -> [v]
               | RecordPat(fields,_)    ->
                   List.map (fn (x,VarPat(v,_)) -> v) fields
         in
         let arguments = termToList argument in
         % let _ = writeLine "Lambda arguments" in
         % let _ = List.map (fn i -> writeLine i.1) boundVars in
         let zip = zipWith (fn x -> fn y -> (x,y)) in
         substitute(body,zip boundVars arguments)
     | Apply(fun,argument,_) ->
         let t' = betan_step fun in
         (case t' of
           | Lambda([(pat,_,body)],_) ->
                betan_step (mkApply (t', argument))
           | _ -> mkApply(t',argument))
     | _  ->
       % let _ = writeLine ("Can't reduce term") in
       % let _ = writeLine (printTerm t) in
       t


op isBetaRedex (t:MSTerm):Bool =
  case t of
     | Apply(Lambda([(pat,_,body)],_),argument,pos) -> true
     | _ -> false

op isUnfoldable? (tm:MSTerm)(spc:Spec)(noUnfolds:List QualifiedId):Bool =
  case tm of
      | Apply(Fun(Op(Qualified (_,qid),_),_,_), _, _)
          | qid in? (["<=", "<", ">="] : List Id) -> false
      | Apply(Fun(Op(qid,_),_,_), _, _)
          | qid in? noUnfolds -> false
      | _ -> unfoldable?(tm,spc)

op unfoldFunction(tm:MSTerm):QualifiedId =
  case tm of
      | Apply(Fun(Op(qid,_),_,_), _, _) -> qid


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Term construction and manipulation utlities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op mkMinimalExists(vs:List (Id * MSType))(body:MSTerm):MSTerm =
  let fvars = map (fn (v:(Id * MSType)) -> v.1) (freeVars body) in
  let live = filter (fn (v:(Id * MSType)) -> v.1 in? fvars) vs in
  case live of
    | [] -> body
    | _ -> Bind(Exists, live,body, noPos)

%% Conjunction of DNF forms.
op andDNF (p1:DNFRep) (p2:DNFRep):DNFRep =
  flatten (map (fn l -> map (fn r -> l ++ r) p2) p1)


% Construct an n-ary and. Assume t is nonempty.
op ands(t:MSTerms):MSTerm =
   case t of
     | [] -> mkFalse ()
     | [t] -> t
     | (x::xs) -> Apply (mkAndOp noPos , Record ([("1", x), ("2", ands xs)], noPos), noPos)

% Construct an n-ary or. Assume t is nonempty.
op ors(t:MSTerms):MSTerm =
   case t of
     | [t] -> t
     | (x::xs) -> Apply (mkOrOp noPos , Record ([("1", x), ("2", ors xs)], noPos), noPos)


op mkAnd(t:MSTerms):MSTerm =
   case t of
     | [] -> mkTrue ()
     | [p] -> p
     | _ -> ands t

% make an and if the trace tree is not Tauto
op mkAndMaybe(ts:MSTerms, t:MSTerm, tree:TraceTree):MSTerm =
  case tree of
    | Tauto _ -> mkAnd ts
    | _ -> mkAnd (ts ++ [t])


op mkOr(t:MSTerms):MSTerm =
   case t of
     | [] -> mkFalse ()
     | [p] -> p
     | _ -> ors t

op printDNF (x:DNFRep):String = printTerm (dnfToTerm x)

op dnfToTerm(x:DNFRep):MSTerm = mkOr (map mkAnd x)

op negateConjunction(conj:MSTerms):DNFRep =
    map (fn c -> [negateTerm c]) conj


op [a,b,c] zipWith(f:a -> b -> c)(xs:List a)(ys:List b):List c =
  case (xs,ys) of
    | ([],_) -> []
    | (_,[]) -> []
    | (x::xss,y::yss) -> (f x y) :: (zipWith f xss yss)


%% Equals
op isEquals?(t:MSTerm):Bool =
  case t of
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos) ->  true
    | _ -> false

op equalsLeft(t:MSTerm):MSTerm =
  case t of
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos) -> l
      
op equalsRight(t:MSTerm):MSTerm =
  case t of
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos) -> r


op isVar?(t:MSTerm):Bool =
  case t of
    | Var _ -> true
    | _ -> false

op varId(t:MSTerm):Id =
   case t of
     | (Var ((i,_),_)) -> i
      

op mkSimpleExists (vars : MSVars) (tm : MSTerm) : MSTerm = tm 

%% mkSimpleExists: Close the given term under the list of binders.
%% Push the quantification as deep as possible into the subterms.
%%
%% Arguments:
%%    vars, a list of AVars
%%    tm, a term
%% Returns:
%%   a new expression, closed w.r.t vars.
op mkSimpleExists' (vars : MSVars) (tm : MSTerm) : MSTerm =
   if empty? vars
     then tm
     else
       case tm of
        | Let (decls, M,  _) ->
          let defVars = foldr
             (fn ((pat, trm), acc) ->
                insertVars (freeVars trm, deleteVars (patVars pat, acc))) [] decls in
          let outer = filter (fn v -> v in? defVars) vars in
          let inner = filter (fn v -> ~(v in? defVars)) vars in
          let tm' = mkSimpleExists inner M in
          % let _ = writeLine ("mkSimpleExists on: " ^ printTerm tm) in          
          Bind (Exists,outer,tm',noPos)
        | LetRec (decls, M,  _) ->
          let defVars : MSVars = List.foldr
             (fn ((v : MSVar, trm: MSTerm), acc) ->
                insertVars (freeVars trm, deleteVars ([v], acc))) [] decls in
          let outer = filter (fn v -> v in? defVars) vars in
          let inner = filter (fn v -> ~(v in? defVars)) vars in
          let tm' = mkSimpleExists inner M in
          % let _ = writeLine ("mkSimpleExists on: " ^ printTerm tm) in          
          Bind (Exists,outer,tm',noPos)

          
        % Handle '&&' specially, for now.
        | (Apply (Fun (f as And,ty,fPos), Record (args,argsPos),appPos)) -> 
          let Some a1 = getField (args,"1") in
          let Some a2 = getField (args,"2") in
          let v1 = freeVars a1 in
          let v2 = freeVars a2 in
          % This needs special treatment, because of the
          % non-commutative nature of && in MetaSlang.
          let outer = filter (fn v -> v in? v1) vars in
          let inner1 = filter (fn v -> v in? v1 && ~ (v in? v2)) vars in
          let inner2 = filter (fn v -> v in? v2 && ~ (v in? v1)) vars in
          let a1' = mkSimpleExists inner1 a1 in
          let a2' = mkSimpleExists inner2 a2 in
          let tm' = Apply (Fun (f,ty,fPos),
                           Record ([("1",a1'),("2",a2')],argsPos),appPos) in
          if empty? outer
            then tm'
            else Bind(Exists,outer,tm',noPos)

         | IfThenElse (p,t,e,pos) ->
             let pvars = freeVars p in
             let tvars = freeVars t in
             let evars = freeVars e in
             let outer = filter (fn v -> v in? pvars || (v in? tvars && v in? evars)) vars in
             let tvars' = filter (fn v -> v in? tvars && ~(v in? outer)) vars in
             let evars' = filter (fn v -> v in? evars && ~(v in? outer)) vars in
             let t' = mkSimpleExists tvars' t in
             let e' = mkSimpleExists evars' e in
             let tm' = IfThenElse (p,t',e',pos) in
             if empty? outer
               then tm'
               else Bind(Exists,outer,tm',noPos)
        % Case expressions.
        | (Apply (Lambda (matches, lamPos),scrutinee,casePos)) ->
            let sVars = freeVars scrutinee in
            let altVars = map (fn m -> freeVarsMatch m false) matches in
            % If a variable appears in the scrutinee or in every branch, then
            % we quantify over it outside the case.
            let outer =
                filter (fn v -> v in? sVars)
                    vars in
            % Build new matches.
            let matches' =
                zipWith (fn (p,c,body) -> fn fvs ->
                           let vars' =
                             nubBy equalVar? (filter (fn v -> v in? fvs && ~(v in? outer)) vars) in
                           let c' = mkSimpleExists vars' c in
                           let body' = mkSimpleExists vars' body in
                           (p,c',body'))
                matches altVars in
            let tm' = Apply (Lambda (matches', lamPos), scrutinee,casePos) in
            if empty? outer
              then tm'
              else Bind (Exists,outer,tm',noPos)

        % FIXME: This is going to barf on shadowed bindings.
        | Bind (Exists,vs,tm',pos) -> mkSimpleExists (nubBy equalVar? (vs ++ vars)) tm'
          
        | _ -> % let _ = writeLine ("mkSimpleExists") in
               % let _ = List.map (fn v -> writeLine v.1) vars in
               % let _ = writeLine (printTerm tm) in
               let vars' = nubBy equalVar? (filter (fn v -> v in? (freeVars tm)) vars) in
               let newTerm = if empty? vars' then tm else Bind (Exists,vars',tm,noPos) in
               % let _ = writeLine ("Yields:\n" ^ printTerm newTerm) in
               tm


endspec
