Convert qualifying spec
  import /Languages/PSL/AbstractSyntax/Types
  import /Languages/SpecCalculus/Semantics/Monad
  import Struct qualifying GraphAnalysis
  import ../../Semantics/Evaluate/Specs/Oscar
  import ../../Semantics/Evaluate/Specs/MetaSlang
  import ../../Semantics/Evaluate/Specs/MetaSlang/Legacy
  import ../../../MetaSlang/CodeGen/C/CG
  import translate /Library/Structures/Data/Maps/Finite/Polymorphic/AsAssocList by
     {Map._ +-> FinitePolyMap._}

  % Doesn't belong here. Really need to fix up this curry / uncurry mess.
  def FinitePolyMap.fold f unit map =
    foldM (fn x -> fn (dom,cod) -> f x dom cod) unit map

  op OscarStruct.show : StructOscarSpec -> ModeSpec -> String
  def OscarStruct.show oscarSpec ms =
    let procStrings =
       map (fn (id,prc) -> (Id.show id) ^ " = " ^ (ppFormat (StructProcedure.pp prc)))
         (mapToList oscarSpec.procedures) in
    let procs = List.show "\n\n" procStrings in
    let modeSpecString = ppFormat (ModeSpec.pp (subtract oscarSpec.modeSpec ms)) in
      ("modeSpec=\n" ^ modeSpecString ^ "\nprocedures=\n" ^ procs)

  sort StructOscarSpec = {
    modeSpec : ModeSpec,
    procedures : FinitePolyMap.Map (QualifiedId,StructProcedure)
  }

  (* Convert the BSpecs in an Oscar spec to graphs ready for subsequent structing *)
  op convertOscarSpec : Oscar.Spec -> Env StructOscarSpec
  def convertOscarSpec oscSpec =
    let def handler id _(*procedure*) except =
      case except of
        | SpecError (pos, msg) -> {
             print ("convertOscarSpec exception: procId=" ^ (Id.show id) ^ "\n");
             print (msg ^ "\n");
             % print (ppFormat (pp proc));
             % print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      procedures <- ProcMapEnv.fold (fn procMap -> fn procId -> fn procedure -> {
          print ("convertOscarSpec: procId=" ^ (Id.show procId) ^ "\n");
          structProc <- catch (convertProcedure procedure) (handler procId procedure);
          return (FinitePolyMap.update (procMap,procId,structProc))
         }) FinitePolyMap.empty (procedures oscSpec);
      return {
        modeSpec = modeSpec oscSpec,
        procedures = procedures
      }
  }

  (* Structure the graphs in an oscar spec *)
  op structOscarSpec : StructOscarSpec -> Env StructOscarSpec
  def structOscarSpec structSpec =
    let def handler id _(*procedure*) except =
      case except of
        | SpecError (pos, msg) -> {
             print ("structOscarSpec exception: procId=" ^ (Id.show id) ^ "\n");
             print (msg ^ "\n");
             % print (ppFormat (pp procedure));
             % print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      procedures <- FinitePolyMap.fold (fn procMap -> fn procId -> fn procedure -> {
          print ("structOscarSpec: procId=" ^ (Id.show procId) ^ "\n");
          structProc <- catch (structProcedure procedure) (handler procId procedure);
          return (FinitePolyMap.update (procMap,procId,structProc))
         }) FinitePolyMap.empty structSpec.procedures;
      return {
        modeSpec = structSpec.modeSpec,
        procedures = procedures
      }
  }

  sort StructProcedure = {
    parameters : List Op.Ref,
    varsInScope : List Op.Ref,
    return : Option Op.Ref,
    modeSpec : ModeSpec,
    code : Struct.Graph
  }

  op StructProcedure.pp : StructProcedure -> Doc
  def StructProcedure.pp prc =
    ppConcat [
      ppString "params=(",
      ppSep (ppString ",") (map OpRef.pp prc.parameters),
      case prc.return of
        | None -> ppString ") return=()"
        | Some name -> ppString (") return " ^ (OpRef.show name)),
      ppString "  ",
      ppIndent (ppString (printGraph prc.code))
    ]
  
  op convertProcedure : Procedure -> Env StructProcedure
  def convertProcedure procedure = {
    code <- convertBSpec (bSpec procedure);
    return {
        parameters = procedure.parameters,
        return = procedure.returnInfo,
        varsInScope = procedure.varsInScope,
        modeSpec = procedure.modeSpec,
        code = code
      }
  }

  op structProcedure : StructProcedure -> Env StructProcedure
  def structProcedure procedure = {
    code <- structGraph procedure.code;
    return {
        parameters = procedure.parameters,
        return = procedure.return,
        varsInScope = procedure.varsInScope,
        modeSpec = procedure.modeSpec,
        code = code
      }
  }

  op sortGraph : fa (a) (a * a -> Boolean) -> List a -> List a
  def sortGraph cmp l =
    let def partitionList x l =
      case l of
       | [] -> ([],[])
       | hd::tl ->
           let (l1,l2) = partitionList x tl in
            if (cmp (hd,x)) then
              (Cons(hd,l1),l2)
            else
              (l1,Cons(hd,l2)) in
    case l of
      | [] -> []
      | hd::tl ->
          let (l1,l2) = partitionList hd tl in
             (sortGraph cmp l1) ++ [hd] ++ (sortGraph cmp l2)

  op printVList : List (String * Index) -> String
  % op printVList : List (Vrtx.Vertex * Index) -> String
  def printVList l = show "\n" (map (fn (vrtx,idx) ->
                        "("
                      % ^ (Vrtx.show vrtx)
                      ^ vrtx
                      ^ "|->"
                      ^ (Nat.show idx)
                      ^ ")") l) 

  op printNCList : List (Nat * NodeContent) -> String
  def printNCList l = show "\n" (map (fn (dom,cod) ->
                        "("
                      ^ (Nat.toString dom)
                      ^ "|->"
                      ^ (printNodeContent cod)
                      ^ ")") l) 

  op mapToList : fa (a,b) FinitePolyMap.Map (a,b) -> List (a * b)

  op structGraph : Graph -> Env Graph
  def structGraph graph =
      % return (graphToStructuredGraph (addPredecessors (map (fn (x,y) -> y) graph)))
      return (graphToStructuredGraph graph)

  op convertBSpec : BSpec -> Env Graph
  def convertBSpec bSpec =
    if bSpec.transitions = [] then
      return []
    else {
        (graph,n,visited) <- convertBSpecAux bSpec (final bSpec) FinitePolyMap.empty 0 (initial bSpec) FinitePolyMap.empty;
        % print "convertBSpec VList =\n";
        % print (printVList (mapToList visited));
        g <- return (sortGraph (fn ((n,_),(m,_)) -> n < m) (mapToList graph));
        g <- return (addPredecessors (map (fn (x,y) -> y) g));
        % print "\nconvertBSpec NCList after sort\n";
        % print (printNCList g);
        % print "\n\n";
        % g <- return (graphToStructuredGraph (addPredecessors (map (fn (x,y) -> y) g)));
        % print (printGraph g);
        return g
    }

  op convertBSpecAux :
        BSpec
     -> List Mode
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> Mode
     -> FinitePolyMap.Map (String,Index)
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index))

(* The first test to see if the vertex is a final one is needed since the BSpec might be a loop in which case
there is branching from a state and one of the branches takes you to a final state. Perhaps the other tests
are no longer needed. *)

  def convertBSpecAux bSpec final graph n mode visited =
    case evalPartial (visited,show (vertex mode)) of
      | Some index -> return (graph,n,visited)
      | None ->
         (case (outTrans bSpec mode) of
            | [] -> 
                 if Mode.member? final mode then
                   return (graph,n,visited)
                 else
                   raise (SpecError (noPos, "convertBSpecAux: reached empty set of successors to vertex: " ^ (show (vertex mode))))

            (* A single edge leaving the node means that the edge is labelled with a statement.  *)
            | [transition] -> 
		let spc = specOf (Transition.modeSpec transition) in
		%let spc = transformSpecForCodeGen base spc in
		{
                 visited <- return (update (visited,show (vertex mode),n));
                 newTerm <- getTransitionAction transition;
                 (graph,next,visited) <-
                   if Mode.member? final (target transition) then
                     return (graph,n+1,visited)
                   else
                     convertBSpecAux bSpec final graph (n+1) (target transition) visited;
                 let graph =
                    if Mode.member? final (target transition) then
                      update (graph,n,Return (spc,newTerm))
                    else
                      let index = vertexToIndex visited (vertex (target transition)) in
                      update (graph,n,Block {statements=[Assign (spc,newTerm)],next=index}) in
                 return (graph,next,visited)
               }

            (*
              If there are two edges leaving the node, then we we are dealing with a conditional.
              At present we do not handle the case where there are more than two branches. Nor
              do we make any effort to prove that the guard on one branch is equivalent to the
              negation of the other branch. This should be done. More generally, we need to
              prove, or have the user provide a proof, that the branches are disjoint or adopt
              a different semantics where the order of the guards is significant.
             *)

            | [leftTrans,rightTrans] -> 
               let leftspc = specOf (Transition.modeSpec leftTrans) in
	       %let leftspc = transformSpecForCodeGen base leftspc in
               {
                 visited <- return (update(visited,show (vertex mode),n)); 
                 leftTerm <- getTransitionAction leftTrans;
                 %rightTerm <- getTransitionAction rightTrans;
                 (graph,next1,visited) <- convertBSpecAux bSpec final graph (n+1) (target leftTrans) visited; 
                 (graph,next2,visited) <- convertBSpecAux bSpec final graph next1 (target rightTrans) visited;
                 let graph =
                   let leftIndex = vertexToIndex visited (vertex (target leftTrans)) in
                   let rightIndex = vertexToIndex visited (vertex (target rightTrans)) in
                   update (graph,n,Branch {condition=(leftspc,leftTerm),trueBranch=leftIndex,falseBranch=rightIndex}) in
                 return (graph,next2,visited)
               }
            | transitions -> {
                  visited <- return (update(visited,show (vertex mode),n)); 
                  (graph,next,visited,idx) <- makeBranches bSpec final graph n transitions visited;
                  return (graph,next,visited)
                })
                
%             | succs -> {               % raise (SpecError (noPos, "more than two successors?")))
%                  print "convertBSpecAux: more than two successors: {";
%                  print (ppFormat (ppSep (ppString ",") (map Edg.pp succs)));
%                  print "}\n";
%                  return (graph,n,visited)
%                })

  op makeBranches :
        BSpec
     -> List Mode
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> List Transition
     -> FinitePolyMap.Map (String,Index)
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index) * Index)
  def makeBranches bSpec final graph n transitions visited =
    case transitions of
      | [] -> raise (SpecError (noPos, "makeBranches: empty list in make branches"))
      | [x] -> raise (SpecError (noPos, "makeBranches: singleton list in make branches"))
      | [leftTrans,rightTrans] -> 
         let leftspc = specOf (Transition.modeSpec leftTrans) in
	 %let leftspc = transformSpecForCodeGen base leftspc in
         {
           leftTerm <- getTransitionAction leftTrans;
           %rightTerm <- getTransitionAction rightTrans;
           (graph,next1,visited) <- convertBSpecAux bSpec final graph (n+1) (target leftTrans) visited; 
           (graph,next2,visited) <- convertBSpecAux bSpec final graph next1 (target rightTrans) visited;
           let graph =
             let leftIndex = vertexToIndex visited (vertex (target leftTrans)) in
             let rightIndex = vertexToIndex visited (vertex (target rightTrans)) in
             update (graph,n,Branch {condition=(leftspc,leftTerm),trueBranch=leftIndex,falseBranch=rightIndex}) in
           return (graph,next2,visited,n)
         }
      | leftTrans::transitions ->
         let leftspc = specOf (Transition.modeSpec leftTrans) in
	 %let leftspc = transformSpecForCodeGen base leftspc in
         {
           leftTerm <- getTransitionAction leftTrans;
           (graph,next1,visited,rightIndex) <- makeBranches bSpec final graph (n+1) transitions visited;
           (graph,next2,visited) <- convertBSpecAux bSpec final graph next1 (target leftTrans) visited; 
           let graph =
             let leftIndex = vertexToIndex visited (vertex (target leftTrans)) in
             update (graph,n,Branch {condition=(leftspc,leftTerm),trueBranch=leftIndex,falseBranch=rightIndex}) in
           return (graph,next2,visited,n)
         }

  (* This shouldn't be needed. We should always visit the target and we should never get None. *)
  % op vertexToIndex : FinitePolyMap.Map (Vrtx.Vertex,Index) -> Vrtx.Vertex -> Index
  op vertexToIndex : FinitePolyMap.Map (String,Index) -> Vrtx.Vertex -> Index
  def vertexToIndex visited vrtx =
    case evalPartial (visited,show vrtx) of
      | None -> ~1
      | Some index -> index

  op getTransitionAction : Transition -> Env MSlang.Term
  def getTransitionAction transition = {
      invars <- foldVariants (fn l -> fn claim -> return (cons (term claim,l))) [] (modeSpec (transSpec transition));
      invars <- foldVariables infoToBindings invars (modeSpec (transSpec transition));
      term <- case invars of
        | [] -> %{
             % print ("convertBSpecAux: no axiom for edge" ^ (Edg.show (edge transition)) ^ "\n");
             MSlangEnv.mkTuple ([],noPos)
           %}
        | [term] -> return term
        | _ -> raise (SpecError (noPos, ppFormat (ppConcat [
                        ppString ("Something wrong with spec properties for edge " ^ (Edg.show (edge transition)) ^ "\n"),
                        ppBreak,
                        ppSep ppBreak (map pp invars)
                      ])));
      return term
    }

  op infoToBindings : List MSlang.Term -> Op.OpInfo -> Env (List MSlang.Term)
  def infoToBindings bindings varInfo =
    let
      def mkEquals () =
        let type = MSlang.freshMetaTyVar noPos in
        MSlang.mkFun (Equals, type, noPos)
      def mkEquality t0 t1 =
        MSlang.mkApply (mkEquals (), MSlang.mkTuple ([t0,t1], noPos),noPos)
    in
      let opTerm = mkFun (Op (idOf varInfo,Nonfix), type varInfo, noPos) in
      if isPrimedName? (idOf varInfo) then
        case (term varInfo) of
          | None -> return bindings
          | Some trm -> return (cons (mkEquality opTerm trm, bindings))
      else
        return bindings

  op isPrimedName? : QualifiedId -> Boolean
  def isPrimedName? (qualId as (Qualified (qual,id))) = hd (rev (explode id)) = #'
endspec
