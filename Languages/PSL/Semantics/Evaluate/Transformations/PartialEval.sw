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
  import /Languages/PSL/Semantics/Evaluate/Specs/EdgeSets

  def EdgSetEnv.fold = EdgSetEnv.foldl

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
          
  op makeNewProcId : Id.Id -> Subst.Subst -> Env Id.Id
  def makeNewProcId (Qualified (qual,id)) subst = return (Qualified (qual,id ^ "_" ^ (show subst)))

  op specializeProcedure : Oscar.Spec -> (Oscar.Spec * MS.Term) -> Env (Oscar.Spec * MS.Term * Subst)
  def specializeProcedure oldOscSpec (newOscSpec, callTerm) = {
    (procId,procSort,procInfo,callArg) <-
      case callTerm of
        | Apply (Fun (Op (procId,fxty),procSort,pos),callArg,_) ->
             (case evalPartial (procedures newOscSpec, procId) of
                | None -> raise (SpecError (noPos, "application is not a procedure call" ^ (printTerm callTerm)))
                | Some procInfo -> return (procId,procSort,procInfo,callArg))
        | _ -> raise (SpecError (noPos, "Term to be specialized: " ^ (printTerm callTerm) ^ " is not an application"));
    print ("specializing " ^ (Id.show procId) ^ " with term " ^ (printTerm callTerm) ^ "\n");
    (argTerm,returnTerm,storeTerm) <-
      case callArg of
        | (Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)) -> return (argTerm,returnTerm,storeTerm)
        | _ -> raise (SpecError (noPos, "Argument is not record"));
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
                      varInfo <- deref (specOf (modeSpec (bSpec procInfo) (initial (bSpec procInfo))), param);
                      return (cons (varInfo withTerm arg,subst), residParams,residArgs,residSorts)
                    } else 
                      return (subst, cons (param,residParams), cons (arg, residArgs), cons (srt,residSorts))
                 }
             | _ -> fail "mismatched lists in partitionArgs"
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
             | _ -> fail "mismatched lists in partitionState"
        in
          partitionState subst (varsInScope procInfo) storeList;

     if extendedSubst = [] then {
       print ("omitting specialization of bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n");
       return (newOscSpec,callTerm,[])
     }
     else {
       print ("specializing bSpec for " ^ (Id.show procId) ^ " with " ^ (show extendedSubst) ^ "\n");
       (newOscSpec,newBSpec) <- specializeBSpec oldOscSpec (bSpec procInfo) extendedSubst newOscSpec;
       newBSpec <- removeNilTransitions newBSpec;
       newProcId <- makeNewProcId procId subst;
       print ("Creating new procedure: " ^ (Id.show newProcId) ^ "\n");
       (newReturnInfo : ReturnInfo, newReturnTerm, newReturnSort,postcondition,bindingTerm) <-
         let
           def andOp () = MSlang.mkFun (Op (Qualified ("Boolean","&"),Infix (Right,15)), binaryBoolType noPos, noPos)
           def mkAnd t0 t1 = MSlang.mkApply (andOp (), MSlang.mkTuple ([t0,t1], noPos), noPos)
           def prodToBoolType t1 t2 position = mkArrow (mkProduct ([t1, t2], position), boolType position, position)
           def mkEquals () =
             let t1 = freshMetaTyVar noPos in
             let t2 = freshMetaTyVar noPos in
             let type = prodToBoolType t1 t2 noPos in
             MSlang.mkFun (Equals, type, noPos)
           def mkEquality t0 t1 =
             MSlang.mkApply (mkEquals (), MSlang.mkTuple ([t0,t1], noPos),noPos)

           def projectSub subIn subOut termOut varRef =
             case subIn of
               | [] -> return (subOut,termOut)
               | (varInfo::subst) ->
                    if (Op.refOf varInfo) = varRef then {
                        opTerm <- return (mkFun (Op (makePrimedId (idOf varInfo),Nonfix), type varInfo, noPos));
                        varTerm <-
                           case (term varInfo) of
                             | None -> raise (SpecError (noPos, "projectSubst failed with no binding term"))
                             | Some trm -> return trm;
                        eqTerm <- return (mkEquality opTerm varTerm); 
                        return (cons (varInfo, subOut), mkAnd termOut eqTerm)
                      }
                    else
                      projectSub subst subOut termOut varRef
          in {
            print ("number of final states = " ^ (Nat.show (size (final newBSpec))) ^ "\n");
            print ("final states = " ^ (ppFormat (pp (final newBSpec))) ^ "\n");
%             when ((size (final newBSpec)) = 0) 
%               (raise (SpecError (noPos, "specialization of " ^ (Id.show procId) ^ " by " ^ (show subst) ^ " has no final states.")));
%             when ((size (final newBSpec)) > 1) 
%               (raise (SpecError (noPos, "specialization of " ^ (Id.show procId)
%                                       ^ " by " ^ (show subst)
%                                       ^ " has multiple final states: " ^ (ppFormat (pp (final newBSpec))))));
            if ((size (final newBSpec)) = 0) then
              (raise (SpecError (noPos, "specialization of " ^ (Id.show procId) ^ " by " ^ (show subst) ^ " has no final states.")))
            else
              if ((size (final newBSpec)) > 1)  then
                (raise (SpecError (noPos, "specialization of " ^ (Id.show procId)
                                      ^ " by " ^ (show subst)
                                      ^ " has multiple final states: " ^ (System.toString (final newBSpec)))))
                                      % ^ " has multiple final states: " ^ (ppFormat (pp (final newBSpec))))))
              else {
            newFinal <- return (theSingleton (final newBSpec));
            postcondition <-
              case newFinal of
                | Nat _ -> return []
                | Pair (vrtx,subst) -> return subst;
            (postSubst,bindingTerm) <-
              (foldM (fn (subst,term) -> fn varRef ->
                projectSub postcondition subst term varRef) ([], MSlang.mkTrue noPos) (varsInScope procInfo));

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
                                 eqTerm <- return (mkEquality returnTerm varTerm); 
                                 return (cons (varInfo, subOut), mkAnd termOut eqTerm)
                               }
                             else
                               projectReturn subst subOut termOut varRef
                    def handler except = {
                        (postSubst,bindingTerm) <- projectReturn postcondition postSubst bindingTerm returnRef;
                        return (None, mkTuple ([], noPos), mkProduct ([],noPos),postSubst,bindingTerm)
                      }
                    def prog () = {
                        returnVar <- OpEnv.deref (specOf (modeSpec newBSpec newFinal), returnRef);
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
       residRtnStoreTerm <- mkTuple (map (fn | (Fun (Op (qid,fxty),srt,pos)) -> Fun (Op (makePrimedId qid,fxty),srt,pos) | x -> x) residStateArgs,noPos);
       residStoreTerm <- mkTuple ([residCallStoreTerm,residRtnStoreTerm],noPos);
       totalTuple <- mkTuple ([paramTerm,newReturnTerm,residStoreTerm],noPos);
       newProcRef <- mkFun (Op (newProcId,Nonfix), newProcType, noPos);
       newTerm <- MSlangEnv.mkApply (newProcRef, totalTuple, noPos);
       rhs <- return (mkAnd (newTerm,bindingTerm));
       equalTerm <- MSlangEnv.mkApply (mkEquals (freshMetaTyVar noPos,noPos), mkTuple ([callTerm,rhs], noPos),noPos);
       newOscSpec <- newOscSpec Env.withModeSpec newModeSpec;
       newProc <- return (Proc.makeProcedure residParams (varsInScope procInfo)
                                 newReturnInfo
                                 (modeSpec procInfo)
                                 newBSpec);
       newOscSpec <- addProcedure newOscSpec newProcId newProc;
       return (newOscSpec,equalTerm,postcondition)
     }
   }
\end{spec}

\begin{spec}
  op makeNewVertex : Vrtx.Vertex -> Subst.Subst -> Env Vrtx.Vertex
  def makeNewVertex vertex sub = return (Pair (vertex,sub))

  op makeNewEdge : Edg.Edge -> Subst.Subst -> Subst.Subst -> Env Edg.Edge
  def makeNewEdge edge pre post = return (Triple (edge,pre,post))

  op connect : BSpec -> Vrtx.Vertex -> Vrtx.Vertex -> Edg.Edge -> TransSpec -> Env BSpec
  def connect bSpec first last edge transSpec =
    return (addTrans bSpec first last edge (modeSpec transSpec) (forwMorph transSpec) (backMorph transSpec))

  op specializeBSpec :
        Oscar.Spec
     -> BSpec
     -> Subst.Subst
     -> Oscar.Spec
     -> Env (Oscar.Spec * BSpec)
  def specializeBSpec oldOscSpec oldBSpec precondition newOscSpec = {
      coAlg <- return (succCoalgebra oldBSpec);
      first <- makeNewVertex (initial oldBSpec) precondition;
      initialSpec <- hideVariables (modeSpec oldBSpec (initial oldBSpec)) precondition;
      newBSpec <- return (BSpec.make first initialSpec);
      fold (specializeEdge coAlg oldBSpec oldOscSpec first precondition) (newOscSpec,newBSpec) (coAlg (initial oldBSpec))
    }
\end{spec}

\begin{spec}
  op processProcCall : Oscar.Spec -> TransSpec -> Oscar.Spec -> Env (Oscar.Spec * TransSpec)
  def processProcCall oscSpec transSpec newOscSpec =
    let def procInv (newOscSpec,transSpec) claim =
       case (claimType claim, idOf claim) of
         | (Axiom, "call") -> {
             (newOscSpec,newTerm,postcondition) <- specializeProcedure oscSpec (newOscSpec,term claim);
             print ("specialize procedure gives " ^ (printTerm newTerm) ^ "\n");
             if newTerm = (term claim) then
               return (newOscSpec,transSpec)
             else {
               newInvariant <- abstractVars (variables (modeSpec transSpec)) newTerm;
               print ("specialize procedure gives inv " ^ (printTerm newInvariant) ^ "\n");
               claim <- makeAxiom (makeId (printTerm newTerm)) [] newInvariant;
               newOscSpec <- addClaim newOscSpec claim noPos;
               print "about to simplify (after procedure call)\n";
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
\end{spec}

The next is function is where the specialization of edges is done. This is where
the propagation is done.

We are given an edge and a precondition on the edge. The precondition
is a collection of ground bindings for some of the variables in scope
at the initial state of the edge.

We apply the precondition (as a "substitution") to the transtion spec
associated with the edge.

\begin{spec}
  op specializeEdge :
        Coalgebra
     -> BSpec
     -> Oscar.Spec
     -> Vrtx.Vertex
     -> Subst.Subst
     -> (Oscar.Spec * BSpec)
     -> Edg.Edge
     -> Env (Oscar.Spec * BSpec)
  def specializeEdge coAlg oldBSpec oldOscSpec newSrcVertex precondition (newOscSpec,newBSpec) edge = {
      print ("specializing edge " ^ (Edg.show edge) ^ " precondition " ^ (show precondition) ^ "\n");
      oldTargetVertex <- return (GraphMap.eval (target (shape (system oldBSpec)), edge));
      oldTargetSpec <- return (modeSpec oldBSpec oldTargetVertex);
      transSpec <- return (edgeLabel (system oldBSpec) edge);
      transSpec <- applySubst (transSpec, precondition);
      print "about to simplify\n";
      transSpec <- simplifyVariants (modeSpec newOscSpec) transSpec;
      (newOscSpec,transSpec) <- processProcCall oldOscSpec transSpec newOscSpec; 
      if provablyInconsistent? transSpec then
        return (newOscSpec,newBSpec)
      else {
        postcondition <- projectPostSubst transSpec oldTargetSpec;
        print ("specializing edge " ^ (Edg.show edge) ^ " postcondition " ^ (show postcondition) ^ "\n");
        newTargetVertex <- makeNewVertex oldTargetVertex postcondition;
        newEdge <- makeNewEdge edge precondition postcondition;
        print ("newEdge: " ^ (Edg.show newEdge) ^ "\n");
        newTargetSpec <- hideVariables oldTargetSpec postcondition;
        targetIsNew? <- return (~(VrtxSet.member? (vertices (shape (system newBSpec)), newTargetVertex)));
        print ("target: " ^ (Vrtx.show newTargetVertex) ^ " is new? " ^ (show targetIsNew?) ^ "\n");
        newBSpec <-
          if targetIsNew? then
            if VrtxSet.member? (final oldBSpec, oldTargetVertex) then
              return (addFinalMode newBSpec newTargetVertex newTargetSpec)
            else
              return (addMode newBSpec newTargetVertex newTargetSpec)
          else
            return newBSpec;
        newTransSpec <- hideVariables transSpec precondition postcondition;
        newBSpec <- connect newBSpec newSrcVertex newTargetVertex newEdge newTransSpec;       
        if targetIsNew? then
          fold (specializeEdge coAlg oldBSpec oldOscSpec newTargetVertex postcondition) (newOscSpec,newBSpec) (coAlg oldTargetVertex)
        else
          return (newOscSpec,newBSpec)
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
