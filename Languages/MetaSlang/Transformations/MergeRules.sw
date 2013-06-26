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
%% -> Boolean' which 's' can appear free in, and 'Post' is a
%% postcondition of type 'StateType -> StateType -> Boolean' in which
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
spec

import Script
import Coalgebraic
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

op SpecTransform.mergeRules(spc:Spec)(args:QualifiedIds)(theorems:Rewrites)(noUnfolds:QualifiedIds):Env Spec =

%% This transformation takes a list of "rules", defined as specware ops, and
%% combines them into a single op.
%% Arguments:
%%  spc: The specification to transform
%%  qids: The names of the ops defining the ruleset to transform.
%% Returns:
%%  An op with the pre (resp. post) conditions of the named input rules merged
%%  into a single pre (resp. post) condition.
% op SpecTransform.mergeRules(spc:Spec)(args:QualifiedIds):Env Spec =
  let _ = writeLine "MergeRules!" in
  let (fname::qids) = args in
  let _ = List.map (fn o -> writeLine ("Input Rule: "^(show o))) qids in
  { ruleSpecs as (rs1::_) <- mapM (fn o -> getOpPreAndPost(spc,o,theorems)) qids
  ; ps <- combineRuleSpecs spc ruleSpecs theorems noUnfolds
  ; let stateType = rs1.st_stateType in
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
            vars=(List.map (fn i -> i.1) vars') } in

    % Look at each clause, and each atomic expression in that clause, and
    % classify its syntactic form.
    let cclauses : List (List CClass) = map (List.map (classify args)) (flatten is) in
    %% Remove any atomic expressions representing true.
    let noTauto : List (List CClass) = map (fn clause -> filter (fn a -> ~ (isTrueAtom? a)) clause) cclauses in
    let noContra = filter (fn clause -> ~ (exists? (fn a ->  (isFalseAtom? a)) clause)) noTauto in    
    let _ = writeLine "About to begin merge" in    
    let (rterm,pred) = bt2 args noContra in
    let _ = writeLine "Done with merge" in
    let _ = writeLine (printTerm rterm) in
    let calculatedPostcondition = mkSimpleExists vars' rterm in    

    %% Use this representation, rather than DNF, since it's easier to read.
    let preAsConj = ands (map (fn conj -> mkNot (Bind (Exists,vars',ands conj,noPos))) pred) in
    let body = mkCombTerm ((preStateVar,stateType)::inputs) ((postStateVar,stateType)::outputs) preAsConj calculatedPostcondition in
    let spc' = addOpDef(spc,fname,Nonfix,body) in
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
    let body = mkLambda (mkTuplePat (map mkVarPat dom),Any noPos) in
    mkTypedTerm (body,mkArrow(domType, ranType))

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
op getOpPreAndPost(spc:Spec, qid:QualifiedId, theorems:Rewrites):Env STRule = 
   % let _ = writeLine ("Looking up op " ^ (show qid)) in
   let def printOthers(p:Id*MSType) = writeLine (p.1 ^ " " ^ printType p.2) in
   case getOpDef(spc,qid) of
     | None -> raise (Fail ("Could not get term pre and post conditions for op " ^ (show qid)))
       % The type should be of the form {x:StateType | Preconditions} -> {y:StateType | Postcondition}
     | Some (tm, ty as (Arrow (dom, codom,_))) ->
       % let _ = writeLine ("Arrow type is " ^ printType ty) in
       % let _ = writeLine ("Domain is " ^ (printType dom)) in
       % let _ = writeLine ("Codomain is " ^ (printType codom)) in
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
       ; let _ = writeLine "inputs" in
         let _ = map printOthers inputArgs in
         let _ = writeLine "outputs" in
         let _ = map printOthers outputVals in return ()          
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
op combineRuleSpecs(spc:Spec)(rules:List STRule)(theorems:Rewrites)(noUnfolds:List QualifiedId):Env (List (ExVars * DNFRep)) =
% op combineRuleSpecs(spc:Spec)(rules:List (MSType*Id*Option MSTerm*Id*Option MSTerm))(theorems:Rewrites):Env (List (ExVars * DNFRep)) =
  let types = map (fn r -> r.st_stateType) rules  in
  let preconditions = map (fn r -> case r.st_precondition of Some t -> t | None -> (mkTrue ())) rules in
  let postconditions = map (fn r -> case r.st_postcondition of Some t -> t | None -> (mkTrue ())) rules in
  { pres <- mapM (normalizeCondition spc theorems noUnfolds) preconditions 
  ; posts <- mapM (normalizeCondition spc theorems noUnfolds) postconditions
  ; let rels = zipWith (fn x -> fn y -> (nubBy equalVar?  (x.1 ++ y.1), andDNF x.2 y.2)) pres posts in 
    let _ = (writeLine (anyToString (List.length (List.flatten (List.map (fn i -> i.2) posts))) ^ " total postconditions.")) in
    % let _ = map printIt ps in
    % let _ = writeLine "Preconditions" in
    % let _ = List.map (fn p -> writeLine (printDNF (p.2))) pres in
    let _ = writeLine "Postconditions" in
    let _ = List.map (fn p -> writeLine (printDNF (p.2))) posts in
    return rels
  }
 
type ExVars = List (AVar Position)
type DNFRep = (List MSTerms)
%% Remove existential quantifers, flatten to DNF.
op normalizeCondition(spc:Spec)(theorems:Rewrites)(noUnfolds:List QualifiedId)(tm:MSTerm):Env(ExVars *  DNFRep) = 
  % let _ = writeLine ("Normalizing " ^ printTerm tm) in
  case tm of
    | Bind (Exists,vars,body,_) -> 
      { (vs',dnf) <- normalizeCondition spc theorems noUnfolds body 
      ; return (vs' ++ vars,dnf)
      }
   | (Apply (Fun (f as And,_,_), Record (args,_),_)) -> 
       let Some a1 = getField (args,"1") in
       let Some a2 = getField (args,"2") in
       { (v1,r1) <- normalizeCondition spc theorems noUnfolds a1
       ; (v2,r2) <- normalizeCondition spc theorems noUnfolds a2 
       ; return (v1 ++ v2, (flatten (map  (fn l -> map (fn r -> l ++ r) r2) r1)))
       }
    | (Apply (Fun (f as Or,_,_), Record (args,_),_)) ->
       % let _ = writeLine ("Splitting in " ^ printTerm tm) in
       let Some a1 = getField (args,"1") in
       let Some a2 = getField (args,"2") in
       { (v1,dnf1) <- normalizeCondition spc theorems noUnfolds a1;
         (v2,dnf2) <- normalizeCondition spc theorems noUnfolds a2;
         return (v1 ++ v2, dnf1 ++ dnf2)
       }
   | IfThenElse (p,t,e,_) -> 
     { (vp,rp) <- normalizeCondition spc theorems noUnfolds p;
       (vt,rt) <- normalizeCondition spc theorems noUnfolds t;
       (ve,re) <- normalizeCondition spc theorems noUnfolds e;
       let ut = andDNF rp rt in
       let ue = andDNF (negateDNF rp) re in
       return (vp ++ vt ++ ve, ut ++ ue)
      }
   | Apply(Fun(NotEquals,ty,a1),args,a2) ->
        return ([],[[mkNot (Apply(Fun(Equals,ty,a1),args,a2))]])

    | (Let ([(VarPat (var,varLoc), definition)],body,_)) ->
        normalizeCondition spc theorems noUnfolds (substitute (body, [(var,definition)]))

    | _ | isUnfoldable? tm spc noUnfolds  ->
            % let _ = writeLine ("Simplifying \n" ^ printTerm tm) in
            let tm' = betan_step (unfoldTerm (tm,spc)) in
            % let tm' = simplifyOne spc (unfoldTerm (tm,spc)) in
            % let _ = writeLine ("Simplified to \n"^ printTerm tm') in
            normalizeCondition spc theorems noUnfolds tm'
    | _ -> case rewriteTerm spc theorems tm of
            | Some tm' -> normalizeCondition spc theorems noUnfolds tm'
            | None -> return ([],[[tm]]) 





% Package up the arguments to bt and auxillary functions.
% The spc, obs, and stateVar fields should be constant,
% but assumptions and vars will vary.
type BTArgs = { spc:Spec,
                obs:List Id,
                outputs : List Id,
                stateVar:Id,
                assumptions:List MSTerm,
                vars:List Id
               }
op addAssumption(args:BTArgs)(a:MSTerm):BTArgs =
  args << { assumptions = a::(args.assumptions) }
op addAssumptions(args:BTArgs)(a:List MSTerm):BTArgs =
  args << { assumptions = a ++ (args.assumptions) }

op setVars(args:BTArgs)(vs:List Id):BTArgs =
  args << { vars = vs }
  
op bt2(args:BTArgs)(inputs:List (List CClass)):(MSTerm * DNFRep) =
   if empty? inputs
     % If the set of input clauses is empty, then we have a contradiction.
     then (mkFalse (), [args.assumptions])
     else
       if (exists? empty? inputs)
         then
         % 1. If any of the clauses lists are empty, then that corresponds
         %    to 'true'. What to do with that???
          (mkTrue (), []) % Should there be some assumptions???
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
               let (tm',pre) = bt2 args next in
                 (mkAnd (terms ++ [tm']), pre) 
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
                  % FIXME: The booltype stuff is bogus!
                  let dvars = map (fn v -> v.1) tvars in 
                  let newAssumptions = map classToTerm gds in
                  let (t',p) =
                     bt2 (setVars (addAssumptions args newAssumptions)
                            (diff (args.vars, dvars))) defsToAtoms
                  in (Bind (Exists, tvars, mkAnd (newAssumptions ++ [t']),noPos), p)
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
                      let (tb,tp) = bt2 (addAssumption args (classToTerm a)) pos in
                      let (eb,ep) =
                         bt2 (addAssumption args (classToTerm (negateClass a))) neg in
                              (IfThenElse (classToTerm a, tb, eb, noPos), tp ++ ep)

                    | ((a as CCase (_,scrutinee,_,_))::_) ->
                      % let _ = writeLine ("Splitting on a construction  " ^
                      %                      printTerm (classToTerm a)) in
                      let (branchClauses,unhandled) = simplifyCaseSplit args a inputs in
                      % Branch construction
                      let def mkAlt (pat,clauses) =
                               let Some patTerm = patternToTerm pat in
                               %% FIXME: The 'boolType' is bogus.
                               let eq = mkEquality (boolType,scrutinee,patTerm) in
                               let (tm',pres) = bt2 (setVars (addAssumption args eq)
                                                       (removePatternVars args.vars (Some pat))) clauses in
                               ((pat,tm'),pres)
                      in
                      let branches =
                            let alts = map mkAlt branchClauses
                            in case unhandled of
                                | Some clauses -> let (tm',pres) = bt2 args clauses in
                                                   %% FIXME: Bool type is bogus.
                                                  let default = ((mkWildPat boolType, tm'),pres) in 
                                                  alts ++ [default]
                                 | _ -> alts
                      in
                      let pres : DNFRep = flatten (map (fn x -> x.2) branches) in
                      (mkCaseExpr (scrutinee, (map (fn x -> x.1) branches)), pres)
                              
                    | _ ->
                      let _ = writeLine "Mergerules is stuck" in
                      let _ = writeLine (printDNF (map (map classToTerm) inputs)) in
                      let _ = debugClauses inputs in
                      (mkVar ("<<<Failure Here>>>",boolType), [])
                      
  



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


op removePatternVars (vars:List Id)(pat:Option MSPattern):List Id =
  case pat of
    | None -> vars
    | Some thePat -> 
       case patternToTerm thePat of
         | None -> vars
         | Some t -> diff (vars, (varNames (freeVars t)))


%%%%%%%%%%%%%%%%%%%%%%
%%% Utility functions.
%%%%%%%%%%%%%%%%%%%%%%


% Remove duplicate elements (inefficient, as is most stuff in this module ..)
op nub (l:MSTerms):MSTerms = nubBy equalTerm? l

op [a] nubBy (p:a * a -> Boolean)(l:List a):List a =
  case l of 
    | [] -> []
    | (x::xs) | exists? (fn y -> p (x,y)) xs -> nubBy p xs
    | (x::xs) -> x::(nubBy p xs)

op [a,b,c] uncurry (f: (a -> b -> c))((x,y):(a*b)):c =
  f x y
  
%% Set membership, over an arbitrary equivalence.
op [a] inBy? (p:(a*a)->Boolean)(e:a)(l:List a):Boolean =
   case l of 
     | [] -> false
     | (x::xs) -> p (e, x) || inBy? p e xs


% %%% Set membership, specialized to using the 'equalTerm?' relation.
op inTerm? (c:MSTerm) (l:MSTerms):Boolean = inBy? equalTerm? c l


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
  | CAtom (MSTerm * (List Id) * Boolean) % Term * Referenced existentials 
  | CDef (List (Id * MSType) * MSTerm * List Id * Boolean) 
    % Defined variables * definition * referenced variables
  | CConstrain (MSTerm * MSTerm * List Id * Boolean)
    % poststate/return value * definition * referenced variables
  | CCase (MSPattern * MSTerm * List Id * Boolean)

% Recognizers for the various classes.
op isAtomClass(c:CClass):Boolean =
  case c of
    | CAtom _ -> true
    | _ -> false


op isTrueAtom?(c:CClass):Boolean =
  case c of
    | CAtom (t,_,_) -> trueTerm? t
    | _ -> false

op isFalseAtom?(c:CClass):Boolean =
  case c of
    | CAtom (t,_,_) -> falseTerm? t
    | _ -> false

op isDefClass(c:CClass):Boolean =
  case c of
    | CDef _ -> true
    | _ -> false

op isConstrainClass(c:CClass):Boolean =
  case c of
    | CConstrain _ -> true
    | _ -> false

op isCaseClass(c:CClass):Boolean =
  case c of
    | CCase _ -> true
    | _ -> false

op isSplit(args:BTArgs)(c:CClass):Boolean =
  (isAtomClass c || isCaseClass c) && fullyDefined? args c

op casePattern (c:CClass):MSPattern =
  case c of
    | CCase (pat,_,_,_) -> pat

% Is a clause c in a list of clauses.
op inClause?(c:CClass)(l:List CClass):Boolean =
  case l of
   | [] -> false
   | (x :: xs) -> equalClass? c x || inClause? c xs

% Are two atomic terms equal.
op equalClass?(c1:CClass)(c2:CClass):Boolean =
  case (c1,c2) of
    | (CAtom (t,_,b1), CAtom (u,_,b2)) ->
        equalTerm? (t,u) && (b1 = b2)
    | (CDef (d1,t1,_,b1), CDef (d2,t2,_,b2)) ->
        equalTerm? (t1,t2) && (b1 = b2)
    | (CConstrain (d1,t1,_,b1), CConstrain (d2,t2,_,b2)) ->
        equalTerm? (t1,t2) && (b1 = b2)
    | (CCase (p1,t1,_,b1), CCase (p2,t2,_,b2)) ->
        equalTerm? (t1,t2)
    | _ -> false        


op classToTerm(c:CClass):MSTerm =
  let def n b t = if b then t else negateTerm t in
  let dummyType = boolType in
  case c of
    | CAtom (t,ids,b) -> n b t 
    | CDef ([v], t, deps,b) ->
        n b (mkEquality (dummyType,mkVar v, t))
    | CDef (vs, t, deps,b) ->
        let vars = mkTuple (map MS.mkVar vs) in
        n b (mkEquality (dummyType,vars, t))
    | CConstrain (v, t, deps,b) ->
        n b (mkEquality (dummyType, v, t))
    | CCase (pat, t, deps,b) ->
        let Some u = patternToTerm pat in
        n b (mkEquality (dummyType, u, t))

% Get all of the atoms satisfying a criteria.
op gatherAtoms(p:CClass -> Boolean)(cs:(List (List CClass))):List CClass =
  nubBy (uncurry equalClass?) (flatten (map (filter p) cs))

% Remove all of the atoms satisfying a criteria
op removeAtoms(p:CClass -> Boolean)(cs:(List (List CClass))):List (List CClass) =
   map (filter p) cs

        
% An atom is a global definition for a set of clauses if it is a def
% and it is fully defined and it occurs in each of the input clauses.
op globalAtom(args:BTArgs)(cpred:(CClass -> Boolean))(clauses:List (List CClass)):(List CClass) =
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
    | CAtom (t,ids,b) -> lead b ^ "atom[" ^ printTerm t ^ "]"
    | CDef (vs, t, deps,b) ->
       let def vars start = foldr (fn ((v,ty), acc) -> v ^ " " ^ acc) start vs in  
       lead b ^ "def[" ^ vars "/" ^  printTerm t ^ "]"
    | CConstrain (v, t, deps,b) ->
         lead b ^  "cons[" ^ printTerm v ^ "/" ^ printTerm t  ^ "]"
    | CCase (pat, t, deps,b) ->
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
    | CAtom (t,ids,b) -> CAtom (t,ids,~b)
    | CDef ([v], t, deps,b) -> CDef ([v], t, deps,~b)
    | CConstrain (v, t, deps,b) -> CConstrain (v, t, deps,~b)
    | CCase (pat, t, deps,b) -> CCase (pat, t, deps,~b)


op simplifySplit(c:CClass)(l:List (List CClass)):List (List CClass) =
       let noNegs = filter (fn c' -> ~(inClause? (negateClass c) c')) l
       in map (fn clause -> filter (fn d -> ~(equalClass? c d)) clause) noNegs

% Return a list of (Pattern,clauses that don't conflict with that pattern), as well as a list of unhandled clauses.         
op simplifyCaseSplit(args:BTArgs)(c:CClass)(l:List (List CClass)):List (MSPattern * List (List CClass)) *(Option (List (List CClass))) =
  case c of
     | CCase (pat, s, vars,_) ->
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
       let def clauseMatch (p:MSPattern) (a:CClass) : Boolean =
          case a of
            | CCase (p', s',_,_) -> equalPattern? (p,p') || ~(atomPolarity a)
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
     | CAtom (_,deps,_) -> deps
     | CDef (_,_,deps,_) -> deps
     | CConstrain (_,_,deps,_) -> deps
     | CCase (_,_,deps,_) -> deps


% Get the variables an atom depends on.
op atomPolarity(c:CClass):Boolean =
   case c of
     | CAtom (_,_,b) -> b
     | CDef (_,_,_,b) -> b
     | CConstrain (_,_,_,b) -> b
     | CCase (_,_,_,b) -> b
       

% An atom is fully defined if none of its dependencies occur
% in the list of args
op fullyDefined?(args:BTArgs)(c:CClass):Boolean =
   forall? (fn v -> ~(v in? args.vars)) (atomDeps c)

% The variables defined by a def
op defVars(c:CClass):List (Id * MSType) =
  case c of
    | CDef(vars,_,_,_) -> vars
    | _ -> []

op debugClassify? : Boolean = true      
op traceClassify(s:String):() =
  if debugClassify? then writeLine s else ()

% Given a term, classify it 
op classify(args:BTArgs)(t:MSTerm):CClass =
  let _ = traceClassify ("Classifying " ^ printTerm t) in
  let t' = classifyAux args t in
  let _ = traceClassify (printClass t') in
  t'

op classifyAux(args:BTArgs)(t:MSTerm):CClass =

  let def theVars tm = map (fn x -> x.1) (filter (fn (i,_) -> i in? args.vars) (freeVars tm)) in
  case t of
    % ~(expr)
    | Apply(Fun(Not,_,_), arg, appPos) -> negateClass (classifyAux args arg)
    
    % s' = expr
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
      | v = args.stateVar -> CConstrain (l,r,theVars r,true)

    % expr = s' 
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v = args.stateVar -> CConstrain (r,l,theVars l,true)

    % obs s' = expr        
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,
                       l as Apply (Fun (Op (Qualified (_,o),opFix),ftype,fPos),
                              (Var ((v,_),varPos)),
                              appPos)),
                       (_,r)], argPos), _)
      | o in? args.obs && v = args.stateVar -> CConstrain (l,r,theVars r,true)

    % expr = obs s'
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l),
                       (_,r as Apply (Fun (Op (Qualified (_,o),opFix),ftype,fPos),
                              (Var ((v,_),varPos)),
                              appPos)
                        )], argPos), _)
      | o in? args.obs && v = args.stateVar -> CConstrain (r,l,theVars l,true)

    % result = expr
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
      | v in? args.outputs -> CConstrain (l,r,theVars r,true)

    % expr = result
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v in? args.outputs -> CConstrain (r,l,theVars l,true)

    % (v1,...,vn) = expr
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos)
      | let pvars = patternVars l in ~(empty? pvars) && forall?  (fn v -> v.1 in? args.vars) pvars -> CDef (patternVars l,r,theVars r,true)
        
    % v = expr
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l as Var ((v,ty),_)), (_,r)], argPos), appPos)
      | v in? args.vars -> CDef ([(v,ty)],r,theVars r,true)


    % (v1,...,vn) = expr
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos)
      | let pvars = patternVars r in ~(empty? pvars) && forall?  (fn v -> v.1 in? args.vars) pvars -> CDef (patternVars r,l,theVars l,true)
        
    % expr = v
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r as Var ((v,ty),_))], argPos), appPos)
      | v in? args.vars -> CDef ([(v,ty)],l,theVars l,true)

        
    | Apply (Fun (Equals,_,eqPos), 
             Record ([(_,l), (_,r)], argPos), appPos) ->
        (case termToPattern r of
              | Some (pat as EmbedPat (con,vars,pty,_)) ->
     % expr = pat
                  CCase (pat, l, theVars l,true)
              | _ ->  (case termToPattern l of
                           | Some (pat as EmbedPat (con,vars,pty,_)) ->
     % pat = expr
                             CCase (pat, r, theVars r,true)
                           | _ -> CAtom (t,theVars t,true)))

   % otherwise
   | _ -> CAtom (t,theVars t,true)


% If a term is of the form `x` or `(x1,x2,..., xn)`, where
% `xi` is a variable, then this will return the list of xs.
op patternVars(l:MSTerm):List (Id * MSType) =
   let ts = termToList l in
   let def isVar x = case x of | Var _ -> true | _ -> false in
   let def unVar x = case x of | Var (v,_) -> v  in
   if (forall? isVar ts)
     then map unVar ts
   else []


% Sometimes we'll have (x,y) = f(1,3) && x = 0. Both of these will
% appear syntactically as a definiton of local variables. However,
% what we really want is to first define x and y, then constraint x to
% 0 (that is, the `CDef x 0` should become CAtom (x = 0)
op defineLocals(defs:List CClass)(clauses:List (List CClass)):(List (List CClass)) =
   let vars : List (Id * MSType) = flatten (List.map defVars defs) in
   let _ = writeLine "Updating locals" in
   let _ = List.map (fn i -> writeLine i.1) vars in
   let def toPred atom =
           case atom of
             | CDef ([var as (v,ty)],t,deps,b) ->
                 if exists? (fn (v',ty') -> v' = v && equalType? (ty, ty')) vars
                  then let _ = writeLine ("Updated" ^ printClass atom) in
                       CAtom (mkEquality (ty,mkVar (v,ty),t), v::deps, b)
                 else let _ = writeLine ("Skipping" ^ printClass atom) in
                      atom
             | _ -> atom
   in map (map toPred) clauses
     
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
op resolveOne (ps:MSTerms)(qs:List MSTerms) (changed?:Boolean):List MSTerms =
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

% Given a spec, a list of rewrite rule specs, and a term, return Some
% tm', where tm' is the first rewrite of tm, w.r.t the rules
% 'theorems.'
op rewriteTerm (spc:Spec)(theorems:Rewrites)(tm:MSTerm):Option MSTerm =
   let pterm = toPathTerm tm in
   let ctx = makeContext spc in
   let qid = mkUnQualifiedId "What???" in % This should be the name of
                                          % the op that the rewritten
                                          % term will ultimately
                                          % appear in.
   let hist = [] in
   let rules = flatten (map (fn rs -> makeRule(ctx,spc,rs)) theorems) in
   % let _ = writeLine (anyToString rules) in
   let (pterm',hist') = replaceSubTermH(rewrite(pterm, ctx, qid, rules, 1), pterm, hist) in
   let tm' = fromPathTerm pterm' in
   if equalTerm?(tm, tm')
     then None
     else % let _ = writeLine ("Term before rewriting: " ^ printTerm tm) in
          % let _ = writeLine ("Term after rewriting: " ^ printTerm tm') in
          (Some tm')


% Beta-Reduction
op betan_step (t:MSTerm):MSTerm =
  case t of
     | Apply(Lambda([(pat,_,body)],_),argument,pos) ->
         % let _ = writeLine ("Beta-reducing:\n " ^ printTerm t) in
         let boundVars =
             case pat of
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


op isBetaRedex (t:MSTerm):Boolean =
  case t of
     | Apply(Lambda([(pat,_,body)],_),argument,pos) -> true
     | _ -> false

op isUnfoldable? (tm:MSTerm)(spc:Spec)(noUnfolds:List QualifiedId):Boolean =
  case tm of
      | Apply(Fun(Op(Qualified (_,qid),_),_,_), _, _)
          | qid in? (["<=", "<"] : List Id) -> false
      | Apply(Fun(Op(qid,_),_,_), _, _)
          | qid in? noUnfolds -> false
      | _ -> unfoldable?(tm,spc)
          

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Term construction and manipulation utlities
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
      



%% mkSimpleExists: Close the given term under the list of binders.
%% Push the quantification as deep as possible into the subterms.
%%
%% Arguments:
%%    vars, a list of AVars
%%    tm, a term
%% Returns:
%%   a new expression, closed w.r.t vars.
op mkSimpleExists (vars : MSVars) (tm : MSTerm) : MSTerm =
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
            let altVars = map freeVarsMatch matches in
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
