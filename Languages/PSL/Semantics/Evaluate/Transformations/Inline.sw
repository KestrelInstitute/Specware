\section{Procedure Inlining}
This aggressively inlines all procedures starting from the root.

Some issues in inlining.

We must keep track of the local variables. The procedure
may introduce new variables. (For now all variables are named apart
at compile time .. but there may be multiple copies via recursion
so it remains an issue.)

Not all parameters will necessarily have disappeared. And the
parameters may be updated. If the parameter persist ..
then it must become a local variable. If it disappears as
a parameter .. then it is ground .. then we would like to conclude
that any place where it appeared on the left will also have been ground.
But this is not true. One may use the parameter just as a local
variable to receive any sort of local binding.. hence it might not always
be bound. Hence .. for correctness .. we must walk through the bspec
and see what identifiers are updated. But then presumably, if the
partial evaluation was done right, then the right things should already
be in the specs .. and everything else tossed.

Must be careful there isn't a local variable with the same name.

If parameters remain, and if they are never assigned to then they can be
removed and the assignment done by rewriting .. this to happen later.

For now we assume that there are no parameters left. so we don't
need to do any rewriting or transitions to bind parameters.
We can have the call transition .. it will be true and tossed.

What about return values? we can introduce an extra transition to 
do the assignment. If there is no return, then forget it. On the
other hand, if there is a return and it appears only on the left
side. Then the return term can be substituted for the return name.

we have the calling points (start and end)
 if there are parameters, add a new start point and connect
 otherwise keep the exisiting start point.
 if there is a return value create a new vertex and
 add a transition to to the assignment to the return term
 copy the bspec within the limits.

do we create the end points .. the point is that we have already
the endpoints of the caller.

\begin{spec}
Inline qualifying spec
  import /Languages/PSL/AbstractSyntax/Types
  import /Languages/SpecCalculus/Semantics/Monad
  import ../Specs/Oscar
  import ../Specs/MetaSlang
  import ../Specs/MetaSlang/Legacy
  import ../Specs/Subst/AsOpInfo
  import Simplify
  % import ../../../CodeGen/Convert % This is for FinitePolyMap.fold .. def below doesn't work
  % import translate /Library/Structures/Data/Maps/Finite/Polymorphic/AsAssocList by
     % {Map._ +-> FinitePolyMap._}

  % Doesn't belong here. Really need to fix up this curry / uncurry mess.
  % def FinitePolyMap.fold f unit map =
    % foldM (fn x -> fn (dom,cod) -> f x dom cod) unit map

  op BSpec.reindex : BSpec -> BSpec

  % op MetaSlangRewriter.traceRewriting : Nat

  op remove : ProcMap.Map * Id.Id -> ProcMap.Map

  op inlineProc : Oscar.Spec -> Id.Id -> Env Oscar.Spec 
  def inlineProc oscSpec procId = {
      (newOscSpec,proc) <-
        case evalPartial (procedures oscSpec, procId) of
          | None -> raise (SpecError (noPos, "inlineProc: procedure " ^ (Id.show procId) ^ " is not defined"))
          % | Some proc -> return (oscSpec withProcedures (remove (procedures oscSpec, procId)), proc);
          | Some proc -> return (oscSpec,proc);
  
      oldBSpec <- return (bSpec proc);
      (newBSpec,newInitial) <- return (BSpec.make procId (modeSpec (initial oldBSpec)));
      (newBSpec,newFinal) <- return (newFinalMode newBSpec (modeSpec (hd (final oldBSpec))));
      (newBSpec,visited) <-
        foldM (inlineTransition (procedures oscSpec) newInitial newFinal oldBSpec None None)
          (newBSpec,[]) (outTrans oldBSpec (initial oldBSpec));
      newBSpec <- removeNilTransitions newBSpec;
      newProc <- makeProcedure (parameters proc)
                               (varsInScope proc)
                               (returnInfo proc)
                               (modeSpec proc)
                               newBSpec;
      addProcedure newOscSpec procId newProc
    }
\end{spec}

  need to be careful that the procedure edge we are inlining is
  maybe another procedure call.

we are inlining a procedure. that procedure maintains an id for its return variable.
we have a procedure call on an edge in has a return term .. the term if any to receive
the assignment for the result .. that variable becomes the new Lhs if it exists
if the lhs variable is the return variable then the lhs variable remains the same.

\begin{spec}
  op findVertex : List (Mode * Mode) -> Mode -> Option Mode
  def findVertex pairs mode =
    case pairs of
      | [] -> None
      | (old,new)::rest ->
           if Mode.eq? (old,mode) then
             Some new
           else
             findVertex rest mode

  op inlineTransition :
        ProcMap.Map
     -> Mode
     -> Mode
     -> BSpec
     -> ReturnInfo
     -> Option Op.Ref
     -> BSpec * List (Mode * Mode)
     -> Transition
     -> Env (BSpec * List (Mode * Mode))
\end{spec}

We are in the process of copying a procedure into the new bspec. We are
filling the gap in the new bspec between src end endPoint and we are
examining the edge in the procedure being inlined. When we reach an edge
whose whose destination is the final vertex, then rather than copy the
vertex, we connect the edge to the endPoint.

\begin{spec}
  def inlineTransition procs src endPoint oldBSpec optReturnRef optLHSRef (newBSpec,visited) transition = {
    dst <- return (target transition);
    (newDst,successors,newBSpec,visited) <-
       if Mode.member? (final oldBSpec) dst then
         return (endPoint,[],newBSpec,visited)
       else
         case findVertex visited dst of
           | None -> {
                (newBSpec,newDst) <- return (newMode newBSpec (modeSpec dst));
                return (newDst, outTrans oldBSpec dst, newBSpec, Cons ((dst,newDst),visited))
              }
           | Some newDst -> return (newDst,[],newBSpec,visited);
\end{spec}

Now we look at the transition in the procedure being inline. If it is a procedure call,
then we want to recurse and inline the called procedure.

When we inline a bspec, we make a fresh copy of it using reindexBSpec.

We make provision (to be implemented later) to introduce a transition that
copies fills in the calling arguments.

\begin{spec}
    transSpec <- return (Transition.transSpec transition); 
    called <- procCalled transSpec;
    (newBSpec,visited) <-
      case (called, optReturnRef, optLHSRef) of
        | (None, None, _) ->
            let (newBSpec,newTrans) = newTrans newBSpec src newDst transSpec in
              return (newBSpec,visited)
            %% connect newBSpec src newDst edge transSpec
        | (None, Some returnRef, Some lhsRef) -> {
              transSpec <- catch {
                varInfo <- findTheVariable (modeSpec transSpec) returnRef;
                transSpec <- TransSpec.hideVariables transSpec [varInfo] [];
                transSpec <- addVariable transSpec (varInfo withId lhsRef) noPos;
                catch {
                  varInfo <- findTheVariable (modeSpec transSpec) (makePrimedId returnRef);
                  transSpec <- hideVariables transSpec [] [varInfo];
                  addVariable transSpec (varInfo withId (makePrimedId lhsRef)) noPos
                } (fn except -> return transSpec)
              } (fn except -> return transSpec);
              (newBSpec,newTransition) <- return (newTrans newBSpec src newDst transSpec);
              return (newBSpec,visited)
            }
        | (Some procInfo, None, _) -> {   % if well formed then no return value returnTerm = ().
              % when (~(procInfo.argList = []))
              %   (raise (SpecError (noPos, "inlineTransition: cannot inline procedures with parameters: " ^ (show procInfo.procId))));
              when (~(procInfo.argList = []))
                (print ("inlineTransition: cannot inline procedures with parameters: " ^ (Id.show procInfo.procId) ^ "\n"));
              newLHSRef <-
                case procInfo.returnTerm of
                  | (Fun (Op(qid,fxty),_,_)) -> return (Some qid)
                  | _ -> return None; % raise (SpecError (noPos, "bad return term: " ^ (show procInfo.returnTerm)));
              proc <-
                case evalPartial (procs, procInfo.procId) of
                  | None -> raise (SpecError (noPos, "inlineTransition: procedure " ^ (Id.show procInfo.procId) ^ " is not defined"))
                  | Some proc -> return proc;
              when (traceRewriting > 0)
                (print ("Inlining: " ^ (Id.show procInfo.procId) ^ "\n"));
              (newBSpec,procVisited) <- foldM (inlineTransition procs src newDst (bSpec proc) (returnInfo proc) newLHSRef)
                (newBSpec,[]) (outTrans (bSpec proc) (initial (bSpec proc)));
              return (newBSpec,visited)
            }
        | (Some procInfo, Some returnRef, Some lhsRef) -> {
              newLHSRef <-
                case procInfo.returnTerm of
                  | (Fun (Op(qid,fxty),_,_)) -> return (Some qid)
                  | _ -> return None; % raise (SpecError (noPos, "bad return term: " ^ (show procInfo.returnTerm)));
              proc <-
                case evalPartial (procs, procInfo.procId) of
                  | None -> raise (SpecError (noPos, "inlineTransition: procedure " ^ (Id.show procInfo.procId) ^ " is not defined"))
                  | Some proc -> return proc;
              when (traceRewriting > 0)
                (print ("Inlining: " ^ (Id.show procInfo.procId) ^ "\n"));
              print ("Inlining: " ^ (Id.show procInfo.procId) ^ "\n");
              (newBSpec,procVisited) <- foldM (inlineTransition procs src newDst (bSpec proc) (returnInfo proc) newLHSRef)
                  (newBSpec,[]) (outTrans (bSpec proc) (initial (bSpec proc)));
              return (newBSpec,visited)
            }
        | _ -> fail ("inlineTransition: called=" ^ (anyToString called)
                                           ^ "\noptReturnRef=" ^ (anyToString optReturnRef)
                                           ^ "\noptLHSRef=" ^ (anyToString optLHSRef));
    foldM (inlineTransition procs newDst endPoint oldBSpec optReturnRef optLHSRef) (newBSpec,visited) successors
  }

  op procCalled : TransSpec -> Env (Option CallInfo)
  def procCalled transSpec = {
     inVars <- foldVariants (fn inVars -> fn claim -> return (cons (claim,inVars))) [] (modeSpec transSpec);
     case inVars of
       | [] -> return None
       | [claim] -> procCalled claim
       | _ -> return None
    }
     
  sort CallInfo = {
    procId : Id.Id,
    argList : List MSlang.Term,
    returnTerm : MSlang.Term,
    inStore : List MSlang.Term,
    outStore : List MSlang.Term
  }

  op B.procCalled : Claim.Claim -> Env (Option CallInfo)
  def B.procCalled claim =
    case (claimType claim, idOf claim) of
      | (Axiom, Qualified(_,"call")) -> {
  	    (procId,callArg) <-
              case (term claim) of
                | Apply (Fun (Op (procId,fxty),procSort,pos),callArg,_) -> return (procId,callArg)
                | _ -> raise (SpecError (noPos, "Call term: " ^ (printTerm (term claim)) ^ " is not an application"));
            (argTerm,returnTerm,storeTerm) <-
              case callArg of
                | (Record ([(_,argTerm),(_,returnTerm),(_,storeTerm)],_)) -> return (argTerm,returnTerm,storeTerm)
                | _ -> raise (SpecError (noPos, "Argument is not record"));
            argList <-
              case argTerm of
                | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
                | _ -> return [argTerm]; % there is only one.
           (inStore,outStore) <-
             case storeTerm of
               | Record ([(_,inStore),(_,outStore)],_) -> return (inStore,outStore)
               | _ -> raise (SpecError (noPos, "Store is not a pair"));
           inStoreList <-
             case inStore of
               | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
               | _ -> return [inStore];
           outStoreList <-
             case outStore of
               | Record (fields,_) -> return (map (fn (x,y) -> y) fields)
               | _ -> return [outStore];
           return (Some {
               procId = procId,
               argList = argList,
               returnTerm = returnTerm,
               inStore = inStoreList,
               outStore = outStoreList
              })
         }
      | _ -> return None

  % op connect : BSpec -> Vrtx.Vertex -> Vrtx.Vertex -> Edg.Edge -> TransSpec -> Env BSpec
  % def connect bSpec first last edge transSpec =
    % return (addTrans bSpec first last edge (modeSpec transSpec) (forwMorph transSpec) (backMorph transSpec))
endspec
\end{spec}

A procedure with no edges is one that has been declared but not defined. Such a procedure
is assumed external. Nothing can be inlined.
