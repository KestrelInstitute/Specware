\section{Partial Evaluator}
\begin{spec}
PE qualifying spec
  import /Languages/PSL/Semantics/Evaluate/Specs/Oscar
  import /Languages/PSL/Semantics/Evaluate/Specs/Subst
  import /Languages/PSL/Semantics/Evaluate/Specs/Compiler
  import Simplify

  (* We prematurely refine transition specs here. *)
  import /Languages/PSL/Semantics/Evaluate/Specs/TransSpec/Legacy

  (* The next import is so we have a monadic fold over edge sets. Could be that
     that graphs should import a monadic fold. *)
  % import /Languages/PSL/Semantics/Evaluate/Specs/EdgeSets

  % def EdgSetEnv.fold = EdgSetEnv.foldl

  % op MetaSlangRewriter.traceRewriting : Nat

  (* We are given an oscar spec (a collection of procedures) and a
  term. We expect the term to be an application that we assume to be a
  procedure call. Arguments that are unconstrained are specified by the
  name "any'. Thus, if exp (x,y) is a procedure, one might provide exp
  (any, 5) as a specialization term. The result of specialization is
  a new oscar spec plus a term representing the result of reducing the
  call term. The latter really isn't needed for anything.  At present,
  the generated Oscar spec is always an extension of the original
  spec. That is, it always includes, the original procedures.  *)

  op specializeOscar : Oscar.Spec -> MS.Term -> Env (Oscar.Spec * MS.Term)
  def specializeOscar oscSpec procCallTerm = {
    (procId,argList) <-
       case procCallTerm of
          | ApplyN ([Fun (OneName (id,_),_,_),Record (fields,_)],pos) -> return (makeId id, map (fn (x,y) -> y) fields)
          | ApplyN ([Fun (OneName (id,_),_,_),argTerm],pos) -> return (makeId id,[argTerm])
          | _ -> raise (SyntaxError "inappropriate term for specialization");

    case evalPartial (procedures oscSpec, procId) of
      | None ->
          raise (SpecError (noPos, "request to specialize non-existent procedure: " ^ (Id.show procId)))
      | Some procInfo -> {
          when (~((length (parameters procInfo)) = (length argList)))
            (raise (SpecError (noPos,
              "number of arguments provided does not match number of arguments to procedure: " ^ (Id.show procId))));

          (* Here we descend the term we have been supplied with and
          replace each occurrence of "any" with a fresh variable.  As we
          go, we keep track of the free variables that we generate and
          the index of the next variable. (We create more fresh variables
          later on. *)

          (newTerms,freeVars,nextVarIdx) <-
             let def anysToVars fields =
               case fields of
                 | [] -> ([],[],0)
                 | term :: terms ->
                     let (newTerms,vars,nextVarIdx) = anysToVars terms in
                     case term of
                       | Fun (OneName ("any",_),_,_) -> 
                            let type = freshMetaTyVar noPos in
                            let aVar = ("v%" ^ (Nat.toString nextVarIdx),type) in
                            let varTerm = Var (aVar,noPos) in
                              (cons (varTerm,newTerms),cons (aVar,vars),nextVarIdx + 1)
                       | _ -> (cons (term,newTerms),vars,nextVarIdx)
             in
               return (anysToVars argList);

          (* If the procedure we are calling returns something, then we
          create a new variable to receive the value. *)

          (returnTerm,freeVars,nextVarIdx) <-
             case returnInfo procInfo of
               | None -> return (mkRecord ([],noPos),freeVars,nextVarIdx)
               | Some _ -> 
                    let type = freshMetaTyVar noPos in
                    let aVar = ("v%" ^ (Nat.toString nextVarIdx) ^ "'",type) in
                    let varTerm = Var (aVar,noPos) in
                      return (varTerm, cons (aVar,freeVars),nextVarIdx + 1);

          (* The mode spec for the procedure being called records
          an ordered list of refs to the variables in scope when the
          procedure was declared. We walk the list and accummulate the
          "info" for each variable. Amongst other things, the info gives
          the type of the variable. *)

          storeList <- 
             let def toVarList varRefs =
               case varRefs of
                 | [] -> return []
                 | (varRef::varRefs) -> {
                     varList <- toVarList varRefs;
                     varInfo <- deref (specOf (modeSpec procInfo), varRef);
                     return (cons (varInfo,varList))
                   }
             in
               toVarList (varsInScope procInfo);

          (* Our goal here is to extend the original term with variables
          for the global variables in scope when the procedure is
          called. Recall that a call to a procedure is modelled by a
          transition labelled by a predicate. The predicate denotes
          a relation between the pair consisting of the the input
          arguments, the initial value of the global variables and the
          return value and the final values of the global variables. In
          the following we create fresh variables for the new and old
          global variables. *)

          (oldStoreList,newStoreList,freeVars,nextVarIdx) <-
             let
               def makeVars freeVars nextVarIdx varList =
                 case varList of
                   | [] -> ([],[],freeVars,nextVarIdx)
                   | (aVar::varList) ->
                       let (oldVarList,newVarList,freeVars,nextVarIdx) = makeVars freeVars nextVarIdx varList in
                       let type = freshMetaTyVar noPos in
                       let oldVar = ("v%" ^ (Nat.toString nextVarIdx),type) in
                       let oldVarTerm = (Var (oldVar,noPos)) : (ATerm Position) in
                       let newVar = ("v%" ^ (Nat.toString nextVarIdx) ^ "'",type) in
                       let newVarTerm = (Var (newVar,noPos)) : (ATerm Position) in
                         (cons (oldVarTerm,oldVarList),
                          cons (newVarTerm,newVarList),
                          cons (oldVar, cons (newVar, freeVars)),
                          nextVarIdx + 2)
             in
               return (makeVars freeVars nextVarIdx storeList);

          (* We construct the full term corresponding to the procedure
          call. Then we create a oscar variable (MetaSlang op)
          and bind it to the term. It is deposited in the mode spec
          representing the context for the procedures and the mode spec
          is elaborated. Amongst other things, this serves to type check
          the new term. *)

          argTerm <- mkTuple (newTerms, noPos);
          oldStore <- mkTuple (oldStoreList, noPos);
          newStore <- mkTuple (newStoreList, noPos);
          storePair <- mkTuple ([oldStore,newStore], noPos);
          totalTuple <- mkTuple ([argTerm,returnTerm,storePair], noPos);
          procOpRef <- mkFun (idToNameRef procId, freshMetaTyVar noPos, noPos);
          callTerm <- mkApplyN (procOpRef, totalTuple, noPos);
          formula <- return (Bind (Forall, freeVars, callTerm, noPos));
          tempOpName <- return (makeId ("var%" ^ (Nat.toString (nextVarIdx + 1))));
          tempOp <- makeOp (tempOpName, formula, freshMetaTyVar noPos);
          modeSpec <- addVariable (modeSpec oscSpec) tempOp noPos;
          print ("var to be specialized before elaboration: " ^ (show tempOp) ^ "\n");
          elabModeSpec <- elaborate modeSpec;
          varInfo <- findTheVariable elabModeSpec tempOpName;
          print ("var to be specialized after elaboration: " ^ (show varInfo) ^ "\n");

          (* The typechecked term is now used to specialize the designated
          procedure in the oscar spec *)

          (Some (Bind (Forall, _, newTerm, _))) <- return (term varInfo);
          (newOscSpec,newTerm,postcondition) <- specializeProcedure oscSpec (oscSpec, newTerm);
          % (newOscSpec,newTerm,postcondition) <- specializeProcedure oscSpec (empty, newTerm);
          print ("specialize procedure gives " ^ (printTerm newTerm) ^ "\n");
          return (newOscSpec,newTerm)
        }
    }
          
  op makeProcId : Id.Id -> Subst.Subst -> Env Id.Id
  def makeProcId (Qualified (qual,id)) subst = return (Qualified (qual,id ^ "_" ^ (show subst)))

           def mkEquality t0 t1 ty =
             let 
               def prodToBoolType t1 t2 position =
                 mkArrow (mkProduct ([t1, t2], position), boolType position, position)
               def mkEquals ty =
                 % let t1 = freshMetaTyVar noPos in
                 % let t2 = freshMetaTyVar noPos in
                 let type = prodToBoolType ty ty noPos in
                 MSlang.mkFun (Equals, type, noPos)
             in
               MSlang.mkApply (mkEquals ty, MSlang.mkTuple ([t0,t1], noPos),noPos)


  op specializeProcedure : Oscar.Spec -> (Oscar.Spec * MS.Term) -> Env (Oscar.Spec * MS.Term * Subst.Subst)
  def specializeProcedure oldOscSpec (newOscSpec, callTerm) = {
    (procId,procSort,procInfo,callArg) <-
      case callTerm of
        | Apply (Fun (Op (procId,fxty),procSort,pos),callArg,_) ->
             (case evalPartial (procedures newOscSpec, procId) of
                | None -> raise (SpecError (noPos, "application is not a procedure call" ^ (printTerm callTerm)))
                | Some procInfo -> return (procId,procSort,procInfo,callArg))
        | _ -> raise (SpecError (noPos, "Term to be specialized: " ^ (System.anyToString callTerm) ^ " is not an application"));
    if traceRewriting > 0 then
      print ("specializing " ^ (Id.show procId) ^ " with term " ^ (printTerm callTerm) ^ "\n") else return ();
    (argTerm,returnTerm,storeTerm) <-
      case callArg of
        | (Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)) -> return (argTerm,returnTerm,storeTerm)
        | _ -> raise (SpecError (noPos, "Argument is not record"));
    callReturnOpRef <-
      case returnTerm of
        | Fun (Op (id,fxty),srt,pos) -> return (Some (removePrime id))
        | Var _ -> return None
        | Record ([],_) -> return None
        | _ -> raise (SpecError (noPos, "Return term is invalid: " ^ (anyToString returnTerm)));
    argList <-
      case argTerm of
        | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [argTerm]; % there is only one.
    (paramSort,returnSort,storeSort) <-
      case procSort of
        | Base (qid, [paramSort,returnSort,storeSort],_) -> return (paramSort,returnSort,storeSort)
        | _ -> raise (SpecError (noPos, "Argument is not record"));
    paramSortList <-
      case paramSort of
        | Product (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [paramSort];
    (oldStore,newStore) <-
      case storeTerm of
        | Record ([(_,oldStore),(_,newStore)],_) -> return (oldStore,newStore)
        | _ -> raise (SpecError (noPos, "Store is not a pair"));
    storeList <-
      case oldStore of
        | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [oldStore];
    (subst,residParams,residArgs,residSorts) <-
       let
         def partitionArgs (params,args,sorts) =
           case (params,args,sorts) of
             | ([],[],[]) -> return ([],[],[],[])
             | (param::params,arg::args,srt::sorts) -> {
                    (subst,residParams,residArgs,residSorts) <- partitionArgs (params,args,sorts);
                    if (groundTerm? arg) then {
                      varInfo <- deref (specOf (Mode.modeSpec (initial (bSpec procInfo))), param);
                      return (cons (varInfo withTerm arg,subst), residParams,residArgs,residSorts)
                    } else 
                      return (subst, cons (param,residParams), cons (arg, residArgs), cons (srt,residSorts))
                 }
             | _ -> fail ("mismatched lists in partitionArgs: "
                    ^ "\n  parameters=" ^ (anyToString procInfo.parameters) 
                    ^ "\n  argList=" ^ (anyToString argList) 
                    ^ "\n  paramSortList=" ^ (anyToString paramSortList) 
                    ^ "\n")
       in
         partitionArgs (procInfo.parameters,argList,paramSortList);

    (extendedSubst,residStateVars,residStateArgs,residStateSorts) <-
       let
         def partitionState subst stateVars stateArgs =
           case (stateVars,stateArgs) of
             | ([],[]) -> return (subst,[],[],[])
             | (stateVar::stateVars,stateArg::stateArgs) -> {
                    (subst,residStateVars,residStateArgs,residStateSorts) <- partitionState subst stateVars stateArgs;
                    varInfo <- deref (specOf procInfo.modeSpec, stateVar);
                    if (groundTerm? stateArg) then
                      return (cons (varInfo withTerm stateArg,subst),residStateVars,residStateArgs,residStateSorts)
                    else 
                      return (subst, cons (stateVar,residStateVars),cons (stateArg,residStateArgs), cons (type varInfo, residStateSorts))
                 }
             | _ -> fail ("mismatched lists in partitionState"
                    ^ "\n  varsInScope=" ^ (anyToString (varsInScope procInfo))
                    ^ "\n  storeList=" ^ (anyToString storeList)
                    ^ "\n") 
        in
          partitionState subst (varsInScope procInfo) storeList;

     if extendedSubst = [] then {
       if traceRewriting > 0 then
         print ("omitting specialization of bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n") else return ();
       return (newOscSpec,callTerm,[])
     }
     else {
       if traceRewriting > 0 then
         print ("specializing bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n") else return ();
       (newOscSpec,newBSpec) <- specializeBSpec oldOscSpec (bSpec procInfo) extendedSubst newOscSpec;
       newProcId <- makeProcId procId extendedSubst;
       newBSpec <- removeNilTransitions newBSpec;
       if traceRewriting > 0 then
         print ("Creating new procedure: " ^ (Id.show newProcId) ^ "\n") else return ();
       (newReturnInfo : ReturnInfo, newReturnTerm, newReturnSort,postcondition,bindingTerm) <-
         let
           def andOp () = MSlang.mkFun (Op (Qualified ("Boolean","&"),Infix (Right,15)), binaryBoolType noPos, noPos)
           def mkAnd t0 t1 = MSlang.mkApply (andOp (), MSlang.mkTuple ([t0,t1], noPos), noPos)
           def projectSub subIn subOut termOut varRef =
             case subIn of
               | [] -> return (subOut,termOut)
               | (varInfo::subst) ->
                    if (Op.refOf varInfo) = varRef then {
                        opTerm <- return (mkFun (Op (makePrimedId (Op.idOf varInfo),Nonfix), type varInfo, noPos));
                        varTerm <-
                           case (term varInfo) of
                             | None -> raise (SpecError (noPos, "projectSubst failed with no binding term"))
                             | Some trm -> return trm;
                        eqTerm <- return (mkEquality opTerm varTerm (type varInfo)); 
                        return (cons (varInfo, subOut), mkAnd termOut eqTerm)
                      }
                    else
                      projectSub subst subOut termOut varRef
          in {
            if traceRewriting > 0 then {
              print ("number of final states = " ^ (Nat.show (length (final newBSpec))) ^ "\n");
              print ("final states = " ^ (ppFormat (ModeList.pp (final newBSpec))) ^ "\n") } else return ();
%             when ((size (final newBSpec)) = 0) 
%               (raise (SpecError (noPos, "specialization of " ^ (Id.show procId) ^ " by " ^ (show subst) ^ " has no final states.")));
%             when ((length (final newBSpec)) > 1) 
%               (raise (SpecError (noPos, "specialization of " ^ (Id.show procId)
%                                       ^ " by " ^ (show subst)
%                                       ^ " has multiple final states: " ^ (ppFormat (pp (final newBSpec))))));
            if ((length (final newBSpec)) = 0) then
              (raise (SpecError (noPos, "specialization of " ^ (Id.show procId) ^ " by " ^ (show subst) ^ " has no final states.")))
            else
              if ((length (final newBSpec)) > 1)  then
                (raise (SpecError (noPos, "specialization of " ^ (Id.show procId)
                                      ^ " by " ^ (show subst)
                                      % ^ " has multiple final states: " ^ (anyToString (final newBSpec)))))
                                      ^ " has multiple final states: " ^ (ppFormat (ModeList.pp (final newBSpec))))))
              else {

            [newFinal] <- return (final newBSpec);
            postcondition <- return (substOf newFinal);

            (* It may be that one of the global variables in scope is also the variable receiving the return value. We do
             not want to propagte the global variable value .. and we assume no name clashes .. with local variables and those
             in the enclosing scope *)
            (postSubst,bindingTerm) <-
              (foldM (fn (subst,term) -> fn varRef ->
                projectSub postcondition subst term varRef) ([], MSlang.mkTrue noPos)
                        (filter (fn ref -> ~(Some ref = callReturnOpRef)) (varsInScope procInfo)));

              (* We want to retrieve the return information for the new
              procedure.  So we look up the procedure info and there
              are two cases. Either the variable has disappeared as a
              result of partial evaluation in which case there is no
              return information, or it persists in which case the return
              information is the same as it was before. Note that the
              we might return a value assigned to a map. In this case it
              makes no sense to return a varInfo *)

            case returnInfo procInfo of
              | None -> return (None, mkTuple ([], noPos), mkProduct ([],noPos),postSubst,bindingTerm)
              | Some returnRef -> 
                  let
                    def projectReturn subst subOut termOut varRef =
                      case subst of
                        | [] -> return (subOut,termOut)
                        | (varInfo::subst) ->
                             if (Op.refOf varInfo) = varRef then {
                                 varTerm <-
                                    case (term varInfo) of
                                      | None -> raise (SpecError (noPos, "projectReturn failed with no binding term"))
                                      | Some trm -> return trm;
                                 eqTerm <- return (mkEquality returnTerm varTerm (type varInfo)); 
                                 return (cons (varInfo, subOut), mkAnd termOut eqTerm)
                               }
                             else
                               projectReturn subst subOut termOut varRef
                    def handler except = {
                        (postSubst,bindingTerm) <- projectReturn postcondition postSubst bindingTerm returnRef;
                        return (None, mkTuple ([], noPos), mkProduct ([],noPos),postSubst,bindingTerm)
                      }
                    def prog () = {
                        returnVar <- OpEnv.deref (specOf (modeSpec newFinal), returnRef);
                        return (Some returnRef, returnTerm, type returnVar,postSubst,bindingTerm)   % Shameful shit!
                      } in
                      catch (prog ()) handler
          }};

       residProd <- mkProduct (map toType residSorts,noPos);
       residStore <- mkProduct (residStateSorts,noPos);
       newProcType <- mkBase (makeId "Proc", [residProd,newReturnSort,residStore], noPos);
       newProcOp <- makeOp (newProcId,newProcType);
       newModeSpec <- addOp (modeSpec newOscSpec) newProcOp noPos;
       paramTerm <- mkTuple (residArgs,noPos);
       residCallStoreTerm <- mkTuple (residStateArgs,noPos);
       residRtnStoreTerm <-
          mkTuple (map (fn | (Fun (Op (qid,fxty),srt,pos)) -> Fun (Op (makePrimedId qid,fxty),srt,pos)
                           | x -> x) residStateArgs,noPos);
       residStoreTerm <- mkTuple ([residCallStoreTerm,residRtnStoreTerm],noPos);
       totalTuple <- mkTuple ([paramTerm,newReturnTerm,residStoreTerm],noPos);
       newProcRef <- mkFun (Op (newProcId,Nonfix), newProcType, noPos);
       newTerm <- MSlangEnv.mkApply (newProcRef, totalTuple, noPos);
       rhs <- return (MS.mkAnd (newTerm,bindingTerm));
       % equalTerm <- MSlangEnv.mkApply (mkEquals (freshMetaTyVar noPos,noPos), mkTuple ([callTerm,rhs], noPos),noPos);
       equalTerm <- return (mkEquality callTerm rhs (boolType noPos));
       newOscSpec <- newOscSpec Env.withModeSpec newModeSpec;
       newProc <- return (Proc.makeProcedure residParams residStateVars
                                 newReturnInfo
                                 (modeSpec procInfo)
                                 newBSpec);
       newOscSpec <- addProcedure newOscSpec newProcId newProc;
       return (newOscSpec,equalTerm,postcondition)
     }
   }

  op specialProc :
           Oscar.Spec
       -> (Oscar.Spec * MS.Term)
       -> Env (Option (Oscar.Spec * BSpec * Option Op.Ref * Procedure))
  def specialProc oldOscSpec (newOscSpec, callTerm) = {
    (procId,procSort,procInfo,callArg) <-
      case callTerm of
        | Apply (Fun (Op (procId,fxty),procSort,pos),callArg,_) ->
             (case evalPartial (procedures newOscSpec, procId) of
                | None -> raise (SpecError (noPos, "application is not a procedure call" ^ (printTerm callTerm)))
                | Some procInfo -> return (procId,procSort,procInfo,callArg))
        | _ -> raise (SpecError (noPos, "Term to be specialized: " ^ (System.anyToString callTerm) ^ " is not an application"));
    if traceRewriting > 0 then
      print ("specializing " ^ (Id.show procId) ^ " with term " ^ (printTerm callTerm) ^ "\n") else return ();
    (argTerm,returnTerm,storeTerm) <-
      case callArg of
        | (Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)) -> return (argTerm,returnTerm,storeTerm)
        | _ -> raise (SpecError (noPos, "Argument is not record"));
    callReturnOpRef <-
      case returnTerm of
        | Fun (Op (id,fxty),srt,pos) -> return (Some (removePrime id))
        | Var _ -> return None
        | Record ([],_) -> return None
        | _ -> raise (SpecError (noPos, "Return term is invalid: " ^ (anyToString returnTerm)));
    argList <-
      case argTerm of
        | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [argTerm]; % there is only one.
    (paramSort,returnSort,storeSort) <-
      case procSort of
        | Base (qid, [paramSort,returnSort,storeSort],_) -> return (paramSort,returnSort,storeSort)
        | _ -> raise (SpecError (noPos, "Argument is not record"));
    paramSortList <-
      case paramSort of
        | Product (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [paramSort];
    (oldStore,newStore) <-
      case storeTerm of
        | Record ([(_,oldStore),(_,newStore)],_) -> return (oldStore,newStore)
        | _ -> raise (SpecError (noPos, "Store is not a pair"));
    storeList <-
      case oldStore of
        | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
        | _ -> return [oldStore];
    (subst,residParams,residArgs,residSorts) <-
       let
         def partitionArgs (params,args,sorts) =
           case (params,args,sorts) of
             | ([],[],[]) -> return ([],[],[],[])
             | (param::params,arg::args,srt::sorts) -> {
                    (subst,residParams,residArgs,residSorts) <- partitionArgs (params,args,sorts);
                    if (groundTerm? arg) then {
                      varInfo <- deref (specOf (Mode.modeSpec (initial (bSpec procInfo))), param);
                      return (cons (varInfo withTerm arg,subst), residParams,residArgs,residSorts)
                    } else 
                      return (subst, cons (param,residParams), cons (arg, residArgs), cons (srt,residSorts))
                 }
             | _ -> fail ("mismatched lists in partitionArgs: "
                    ^ "\n  parameters=" ^ (anyToString procInfo.parameters) 
                    ^ "\n  argList=" ^ (anyToString argList) 
                    ^ "\n  paramSortList=" ^ (anyToString paramSortList) 
                    ^ "\n")
       in
         partitionArgs (procInfo.parameters,argList,paramSortList);

    (extendedSubst,residStateVars,residStateArgs,residStateSorts) <-
       let
         def partitionState subst stateVars stateArgs =
           case (stateVars,stateArgs) of
             | ([],[]) -> return (subst,[],[],[])
             | (stateVar::stateVars,stateArg::stateArgs) -> {
                    (subst,residStateVars,residStateArgs,residStateSorts) <- partitionState subst stateVars stateArgs;
                    varInfo <- deref (specOf procInfo.modeSpec, stateVar);
                    if (groundTerm? stateArg) then
                      return (cons (varInfo withTerm stateArg,subst),residStateVars,residStateArgs,residStateSorts)
                    else 
                      return (subst, cons (stateVar,residStateVars),cons (stateArg,residStateArgs), cons (type varInfo, residStateSorts))
                 }
             | _ -> fail ("mismatched lists in partitionState"
                    ^ "\n  varsInScope=" ^ (anyToString (varsInScope procInfo))
                    ^ "\n  storeList=" ^ (anyToString storeList)
                    ^ "\n") 
        in
          partitionState subst (varsInScope procInfo) storeList;

     if extendedSubst = [] then {
       if traceRewriting > 0 then
         print ("omitting specialization of bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n") else return ();
       % return (newOscSpec,newBSpec,callReturnOpRef,procInfo)
       return None
     }
     else {
       newProcId <- makeProcId procId extendedSubst;
       case evalPartial (procedures newOscSpec, newProcId) of
         | Some procInfo -> return (Some (newOscSpec, bSpec procInfo, callReturnOpRef, procInfo))
         | None -> {
             if traceRewriting > 0 then
                print ("specializing bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n") else return ();
             (newOscSpec,newBSpec) <- specializeBSpec oldOscSpec (bSpec procInfo) extendedSubst newOscSpec;
             newBSpec <- removeNilTransitions newBSpec;
             if traceRewriting > 0 then
               print ("Creating new procedure: " ^ (Id.show newProcId) ^ "\n") else return ();
             newProc <- return (Proc.makeProcedure residParams residStateVars
                               None
                               (modeSpec procInfo)
                               newBSpec);
             newOscSpec <- addProcedure newOscSpec newProcId newProc;
             return (Some (newOscSpec,newBSpec,callReturnOpRef,procInfo))
          }
     }
   }
\end{spec}

\begin{spec}
  op specializeBSpec :
        Oscar.Spec
     -> BSpec
     -> Subst.Subst
     -> Oscar.Spec
     -> Env (Oscar.Spec * BSpec)
  def specializeBSpec oldOscSpec oldBSpec precondition newOscSpec = {
      %% coAlg <- return (succCoalgebra oldBSpec);
      %% first <- makeNewVertex (initial oldBSpec) precondition;
      initialSpec <- hideVariables (modeSpec (initial oldBSpec)) precondition;
      (newBSpec,newMode) <- return (deriveBSpec oldBSpec precondition initialSpec);
      %% newBSpec <- return (BSpec.make first initialSpec);
      fold (specialTrans oldBSpec oldOscSpec newMode precondition) (newOscSpec,newBSpec) (outTrans oldBSpec (initial oldBSpec))
      % fold (specializeTransition oldBSpec oldOscSpec newMode precondition) (newOscSpec,newBSpec) (outTrans oldBSpec (initial oldBSpec))
    }
\end{spec}

\begin{spec}
  op processProcCall : Oscar.Spec -> TransSpec -> Oscar.Spec -> Env (Oscar.Spec * TransSpec)
  def processProcCall oscSpec transSpec newOscSpec =
    let def procInv (newOscSpec,transSpec) claim =
       case (claimType claim, idOf claim) of
         | (Axiom, "call") -> {
             (newOscSpec,newTerm,postcondition) <- specializeProcedure oscSpec (newOscSpec,term claim);
             if traceRewriting > 0 then
               print ("specialize procedure gives " ^ (printTerm newTerm) ^ "\n") else return ();
             if newTerm = (term claim) then
               return (newOscSpec,transSpec)
             else {
               newInvariant <- abstractVars (variables (modeSpec transSpec)) newTerm;
               if traceRewriting > 0 then
                 print ("specialize procedure gives inv " ^ (printTerm newInvariant) ^ "\n") else return ();
               claim <- makeAxiom (makeId (printTerm newTerm)) [] newInvariant;
               newOscSpec <- addClaim newOscSpec claim noPos;
               newRules <- return (axiomRules (context (modeSpec newOscSpec)) claim); 
               newRules <- return (addUnconditionalRules(newRules,rewriteRules (modeSpec newOscSpec)));
               newOscSpec <- return (newOscSpec Oscar.withModeSpec ((modeSpec newOscSpec) withRewriteRules newRules));

               if traceRewriting > 0 then
                 print "about to simplify (after procedure call)\n" else return ();
               % printRules (modeSpec newOscSpec);
               % print ((show (modeSpec newOscSpec)) ^ "\n");
               newTransSpec <- simplifyVariants (modeSpec newOscSpec) transSpec;
               % newTransSpec <- return (hideVariables transSpec preCondition postCondition);
               % newTransSpec <- return (transSpec TransSpec.withClaim (claim withTerm newTerm));
               % transSpec <- applySubst (transSpec, postcondition);
               return (newOscSpec,newTransSpec)
             }
           }
         | _ -> return (newOscSpec,transSpec)
    in
      foldVariants procInv (newOscSpec,transSpec) (modeSpec transSpec)


  op filterReturn : Mode -> ReturnInfo -> Option Op.Ref -> Subst.Subst
  def filterReturn {vertex,modeSpec} optReturnId optCallReturnId =
    case vertex of
      | Pair (vrtx,subst) ->
          (case (optReturnId,optCallReturnId) of
            | (Some returnId,Some callReturnId) ->
                 let
                   def findReturn subst =
                     case subst of
                       | [] -> []
                       | opInfo::rest ->
                          if (idOf opInfo) = returnId then
                            [opInfo withId callReturnId]
                          else
                            findReturn rest
                 in
                   findReturn subst
            | _ -> [])
      | _ -> []

  op renameReturn : Mode -> ReturnInfo -> Option Op.Ref -> Mode
  def renameReturn (mode as {vertex,modeSpec}) optReturnId optCallReturnId =
    case vertex of
      | Pair (vrtx,subst) ->
          (case (optReturnId,optCallReturnId) of
            | (Some returnId,Some callReturnId) ->
                 let newSubst = map (fn opInfo ->
                   if (idOf opInfo) = returnId then
                     opInfo withId callReturnId
                   else
                     opInfo) subst
                 in
                   {vertex=Pair (vrtx,newSubst),modeSpec=modeSpec}
            | _ -> mode)
      | _ -> mode

  op findVertex : List (Mode * Mode) -> Mode -> Option Mode
  def findVertex pairs mode =
    case pairs of
      | [] -> None
      | (old,new)::rest ->
           if Mode.eq? (old,mode) then
             Some new
           else
             findVertex rest mode

  op specialProcCall : 
        BSpec
     -> Oscar.Spec
     -> Mode
     -> (Oscar.Spec * BSpec)
     -> Transition
     -> Env (Option (Oscar.Spec * BSpec))
  def specialProcCall oldBSpec oldOscSpec newSourceMode (newOscSpec,newBSpec) transition =
    let
      def procInv (newOscSpec,newBSpec,found) claim =
       case (claimType claim, idOf claim) of
         | (Axiom, "call") -> {
             result <- specialProc oldOscSpec (newOscSpec,term claim);
             case result of
               | None -> return (newOscSpec,newBSpec,found)
               | Some (newOscSpec,procBSpec,optCallReturnRef,procInfo) ->
                   let
                     def inlineTransition src (newBSpec,visited,finals) transition = {
                         dst <- return (target transition);
                         (newDst,successors,newBSpec,visited,newFinals) <-
                            case findVertex visited dst of
                              | None ->
                                   let (newBSpec,newDst) = copyMode newBSpec dst in
                                   let newFinals =
                                     if Mode.member? (final oldBSpec) dst then
                                       Cons (newDst,finals)
                                     else
                                       finals
                                   in
                                     return (newDst, outTrans oldBSpec dst, newBSpec, Cons ((dst,newDst),visited),newFinals)
                              | Some newDst -> return (newDst,[],newBSpec,visited,finals);
                          (newBSpec,newTrans) <- return (newTrans newBSpec src newDst (transSpec transition));
                          foldM (inlineTransition newDst) (newBSpec,visited,newFinals) successors
                        }
                     def tryFinal oldOscSpec oldBSpec (newOscSpec,newBSpec) mode =
                       let subst = filterReturn mode procInfo.returnInfo optCallReturnRef in
                       foldM (specialTrans oldBSpec oldOscSpec mode subst) (newOscSpec,newBSpec) (outTrans oldBSpec (target transition))
                       %% foldM (specializeTransition oldBSpec oldOscSpec mode subst) (newOscSpec,newBSpec) (outTrans oldBSpec (target transition))
                   in {
                     (newBSpec,visited,finals) <- foldM (inlineTransition newSourceMode) (newBSpec,[],[]) (outTrans procBSpec (initial procBSpec));
                     (newOscSpec,newBSpec) <- foldM (tryFinal oldOscSpec oldBSpec) (newOscSpec,newBSpec) finals;
                     return (newOscSpec,newBSpec,true)
                   }
            }
         | _ -> return (newOscSpec,newBSpec,found)
    in {
      (newOscSpec,newBSpec,found) <- foldVariants procInv (newOscSpec,newBSpec,false) (modeSpec (Transition.transSpec transition));
      if found then
        return (Some (newOscSpec,newBSpec))
      else
        return None
    }
\end{spec}

Now we look at the transition in the procedure being inline. If it is a procedure call,
then we want to recurse and inline the called procedure.

When we inline a bspec, we make a fresh copy of it using reindexBSpec.

We make provision (to be implemented later) to introduce a transition that
copies fills in the calling arguments.

The next is function is where the specialization of edges is done. This is where
the propagation is done.

We are given an edge and a precondition on the edge. The precondition
is a collection of ground bindings for some of the variables in scope
at the initial state of the edge.

We apply the precondition (as a "substitution") to the transtion spec
associated with the edge.

\begin{spec}
  op specializeTransition :
        BSpec
     -> Oscar.Spec
     -> Mode
     -> Subst.Subst
     -> (Oscar.Spec * BSpec)
     -> Transition
     -> Env (Oscar.Spec * BSpec)
  def specializeTransition oldBSpec oldOscSpec newSourceMode precondition (newOscSpec,newBSpec) transition = {
      if traceRewriting > 1 then
        print ("specializing transition " ^ (Edg.show (edge transition)) ^ " precondition " ^ (show precondition) ^ "\n") else return ();
      %% oldTargetVertex <- return (GraphMap.eval (target (shape (system oldBSpec)), edge));
      oldTargetSpec <- return (modeSpec (target transition));
      transSpec <- return (Transition.transSpec transition);
      transSpec <- applySubst (Transition.transSpec transition, precondition);
      if traceRewriting > 1 then
        print "about to simplify\n" else return ();
      transSpec <- simplifyVariants (modeSpec newOscSpec) transSpec;
      (newOscSpec,transSpec) <- processProcCall oldOscSpec transSpec newOscSpec; 
      if provablyInconsistent? transSpec then
        return (newOscSpec,newBSpec)
      else {
        postcondition <- projectPostSubst transSpec;
        if traceRewriting > 1 then
          print ("specializing edge " ^ (Edg.show (edge transition)) ^ " postcondition " ^ (show postcondition) ^ "\n") else return ();

        %% newTargetVertex <- makeNewVertex oldTargetVertex postcondition;

        %%% postcondition may include bindings for variables not appearing in the target spec (eg because
        %%% of "let" construct). When calculating the new target spec and new mode, we should restrict
        %%% the postcondition to only the variables appearing in the target. Note, however, that when
        %%% calculating the new transition we need the whole postcondition.
        targetConstraint <- return (Subst.filter (fn varInfo -> member? (variables (modeSpec (Transition.target transition)), Op.idOf varInfo)) postcondition);
        newTargetSpec <- hideVariables (modeSpec (Transition.target transition)) targetConstraint;
        (newBSpec,newTargetMode,targetIsNew?) <- return (deriveMode oldBSpec (Transition.target transition) newBSpec targetConstraint newTargetSpec);

        newTransSpec <- hideVariables transSpec precondition postcondition;
        % newEdge <- makeNewEdge edge precondition postcondition;

        (newBSpec,newTransition) <- return (deriveTransition transition newBSpec newSourceMode newTargetMode precondition postcondition newTransSpec);

        % if traceRewriting > 1 then
          % print ("newEdge: " ^ (Edg.show (edge newTransition)) ^ "\n") else return ();

        %% newTargetSpec <- hideVariables oldTargetSpec postcondition;
        %% targetIsNew? <- return (~(VrtxSet.member? (vertices (shape (system newBSpec)), newTargetVertex)));

%%        if traceRewriting > 1 then
%%          print ("target: " ^ (Vrtx.show newTargetVertex) ^ " is new? " ^ (show targetIsNew?) ^ "\n") else return ();
%%
%%        newBSpec <-
%%          if targetIsNew? then
%%            if Mode.member? (final oldBSpec) (target transition) then
%%              return (addFinalMode newBSpec newTargetVertex newTargetSpec)
%%            else
%%              return (addMode newBSpec newTargetVertex newTargetSpec)
%%          else
%%            return newBSpec;
        %% newBSpec <- connect newBSpec newSrcVertex newTargetVertex newEdge newTransSpec;       
        if targetIsNew? then
          foldM (specializeTransition oldBSpec oldOscSpec newTargetMode postcondition) (newOscSpec,newBSpec) (outTrans oldBSpec (target transition))
        else
          return (newOscSpec,newBSpec)
      }
    }

  op specialTrans :
        BSpec
     -> Oscar.Spec
     -> Mode
     -> Subst.Subst
     -> (Oscar.Spec * BSpec)
     -> Transition
     -> Env (Oscar.Spec * BSpec)
  def specialTrans oldBSpec oldOscSpec newSourceMode precondition (newOscSpec,newBSpec) transition = {
      if traceRewriting > 1 then
        print ("specializing transition " ^ (Edg.show (edge transition)) ^ " precondition " ^ (show precondition) ^ "\n") else return ();
      %% oldTargetVertex <- return (GraphMap.eval (target (shape (system oldBSpec)), edge));
      oldTargetSpec <- return (modeSpec (target transition));
      transSpec <- return (Transition.transSpec transition);
      transSpec <- applySubst (Transition.transSpec transition, precondition);
      if traceRewriting > 1 then
        print "about to simplify\n" else return ();
      transSpec <- simplifyVariants (modeSpec newOscSpec) transSpec;
      if provablyInconsistent? transSpec then
        return (newOscSpec,newBSpec)
      else {
        result <- specialProcCall oldBSpec oldOscSpec newSourceMode (newOscSpec,newBSpec) transition;
        case result of
          | Some (newOscSpec,newBSpec) -> return (newOscSpec,newBSpec)
          | None -> {
              postcondition <- projectPostSubst transSpec;
              if traceRewriting > 1 then
                print ("specializing edge " ^ (Edg.show (edge transition)) ^ " postcondition " ^ (show postcondition) ^ "\n") else return ();
      
              %% newTargetVertex <- makeNewVertex oldTargetVertex postcondition;
      
              %%% postcondition may include bindings for variables not appearing in the target spec (eg because
              %%% of "let" construct). When calculating the new target spec and new mode, we should restrict
              %%% the postcondition to only the variables appearing in the target. Note, however, that when
              %%% calculating the new transition we need the whole postcondition.
              targetConstraint <- return (Subst.filter (fn varInfo -> member? (variables (modeSpec (Transition.target transition)), Op.idOf varInfo)) postcondition);
              newTargetSpec <- hideVariables (modeSpec (Transition.target transition)) targetConstraint;
              (newBSpec,newTargetMode,targetIsNew?) <- return (deriveMode oldBSpec (Transition.target transition) newBSpec targetConstraint newTargetSpec);
      
              newTransSpec <- hideVariables transSpec precondition postcondition;
              % newEdge <- makeNewEdge edge precondition postcondition;
      
              (newBSpec,newTransition) <- return (deriveTransition transition newBSpec newSourceMode newTargetMode precondition postcondition newTransSpec);
      
              % if traceRewriting > 1 then
                % print ("newEdge: " ^ (Edg.show (edge newTransition)) ^ "\n") else return ();
      
              %% newTargetSpec <- hideVariables oldTargetSpec postcondition;
              %% targetIsNew? <- return (~(VrtxSet.member? (vertices (shape (system newBSpec)), newTargetVertex)));
      
      %%        if traceRewriting > 1 then
      %%          print ("target: " ^ (Vrtx.show newTargetVertex) ^ " is new? " ^ (show targetIsNew?) ^ "\n") else return ();
      %%
      %%        newBSpec <-
      %%          if targetIsNew? then
      %%            if Mode.member? (final oldBSpec) (target transition) then
      %%              return (addFinalMode newBSpec newTargetVertex newTargetSpec)
      %%            else
      %%              return (addMode newBSpec newTargetVertex newTargetSpec)
      %%          else
      %%            return newBSpec;
              %% newBSpec <- connect newBSpec newSrcVertex newTargetVertex newEdge newTransSpec;       
              if targetIsNew? then
                foldM (specialTrans oldBSpec oldOscSpec newTargetMode postcondition) (newOscSpec,newBSpec) (outTrans oldBSpec (target transition))
              else
                return (newOscSpec,newBSpec)
        }
      }
    }

  import /Library/Legacy/DataStructures/ListUtilities % for removeDublicates

  op abstractVars : OpRefSet.Set -> MSlang.Term -> Env MSlang.Term
  def abstractVars variables term = {
      (usedVars,newTerm) <- return (convertOpsToVars variables [] term);
      return (Bind (Forall, removeDuplicates usedVars, newTerm, noPos))
    }

  op convertOpsToVars : OpRefSet.Set -> List (AVar Position) -> MSlang.Term -> (List (AVar Position) * MSlang.Term)
  def convertOpsToVars variables usedVars term =
    case term of
      | Var v -> (usedVars,term)
      | ApplyN (terms,a) -> 
          let (usedVars,newTerms) =
            List.foldr (fn (term,(usedVars,newTerms)) -> 
              let (newUsedVars,newTerm) = convertOpsToVars variables usedVars term in
                (newUsedVars,cons (newTerm,newTerms))) (usedVars,[]) terms
          in
            (usedVars, ApplyN (newTerms, a))
      | Apply (t1,t2,a) -> 
          let (usedVars,newT1) = convertOpsToVars variables usedVars t1 in
          let (usedVars,newT2) = convertOpsToVars variables usedVars t2 in
            (usedVars,Apply (newT1,newT2, a))
      | Record (fields,a) -> 
          let (usedVars,newFields) =
            List.foldr (fn ((name,term),(usedVars,newPairs)) -> 
              let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
                (usedVars, cons ((name,newTerm),newPairs))) (usedVars,[]) fields
          in
            (usedVars, Record (newFields, a))
      | Fun (Op (qid as Qualified (qual,id),fixity),srt,pos) ->
          if member? (variables, qid) or member? (variables, removePrime qid) then
            let varId =
               if qual = UnQualified then
                  ("*" ^ id,srt)
               else
                  (qual ^ "*" ^ id,srt) in
              (cons (varId, usedVars), Var (varId, pos))
          else
            (usedVars,term)
      | Fun _ -> (usedVars,term) 
      | Lambda (rules,a) ->
         let (usedVars,newRules) = 
           foldr (fn ((pat,cond,term),(usedVars,newRules)) -> 
             let (usedVars,newCond) = convertOpsToVars variables usedVars cond in
             let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
               (usedVars,cons ((pat,newCond,newTerm),newRules))) (usedVars,[]) rules in
           (usedVars, Lambda (newRules, a))
      | Let (decls,term,a) -> 
          let (usedVars,newDecls) =
            foldr (fn ((pat,term),(usedVars,newDecls)) -> 
              let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
                (usedVars,cons ((pat,newTerm),newDecls))) (usedVars,[]) decls in
          let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
            (usedVars, Let (newDecls,newTerm,a))
      | LetRec (decls,term,a) -> 
          let (usedVars,newDecls) =
            foldr (fn ((name,term),(usedVars,newDecls)) -> 
              let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
                (usedVars,cons ((name,newTerm),newDecls))) (usedVars,[]) decls in
          let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
            (usedVars, LetRec (newDecls,newTerm,a))
      | Bind (b,vars,term,a) ->
          let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
            (usedVars, Bind (b, vars, newTerm, a))
      | IfThenElse (t1,t2,t3,a) ->
          let (usedVars,newT1) = convertOpsToVars variables usedVars t1 in
          let (usedVars,newT2) = convertOpsToVars variables usedVars t2 in
          let (usedVars,newT3) = convertOpsToVars variables usedVars t3 in
            (usedVars, IfThenElse (newT1, newT2, newT3, a))
      | Seq (terms,a) -> 
          let (usedVars,newTerms) =
            foldr (fn (term,(usedVars,newTerms)) -> 
              let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
                (usedVars,cons (newTerm,newTerms))) (usedVars,[]) terms in
            (usedVars, Seq (newTerms, a))
      | SortedTerm (term,srt,a) ->
          let (usedVars,newTerm) = convertOpsToVars variables usedVars term in
            (usedVars, SortedTerm (newTerm, srt, a))
endspec
\end{spec}
