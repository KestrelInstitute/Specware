Convert qualifying spec
  import /Languages/PSL/AbstractSyntax/Types
  import /Languages/SpecCalculus/Semantics/Monad
  import Struct qualifying GraphAnalysis
  import ../Semantics/Evaluate/Specs/Oscar
  import ../Semantics/Evaluate/Specs/MetaSlang
  import ../Semantics/Evaluate/Specs/MetaSlang/Legacy
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
    let def handler id proc except =
      case except of
        | SpecError (pos, msg) -> {
             print ("convertOscarSpec exception: procId=" ^ (Id.show id) ^ "\n");
             print (msg ^ "\n");
             print (ppFormat (pp proc));
             print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      procedures <- ProcMapEnv.fold (fn procMap -> fn procId -> fn proc -> {
          print ("convertOscarSpec: procId=" ^ (Id.show procId) ^ "\n");
          structProc <- catch (convertProcedure proc) (handler procId proc);
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
    let def handler id proc except =
      case except of
        | SpecError (pos, msg) -> {
             print ("structOscarSpec exception: procId=" ^ (Id.show id) ^ "\n");
             print (msg ^ "\n");
             print (ppFormat (pp proc));
             print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      procedures <- FinitePolyMap.fold (fn procMap -> fn procId -> fn proc -> {
          print ("structOscarSpec: procId=" ^ (Id.show procId) ^ "\n");
          structProc <- catch (structProcedure proc) (handler procId proc);
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
  def convertProcedure proc = {
    code <- convertBSpec (bSpec proc);
    return {
        parameters = proc.parameters,
        return = proc.returnInfo,
        varsInScope = proc.varsInScope,
        modeSpec = proc.modeSpec,
        code = code
      }
  }

  op structProcedure : StructProcedure -> Env StructProcedure
  def structProcedure proc = {
    code <- structGraph proc.code;
    return {
        parameters = proc.parameters,
        return = proc.return,
        varsInScope = proc.varsInScope,
        modeSpec = proc.modeSpec,
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
  op toList : EdgSet.Set -> List Edg.Edge

  op structGraph : Graph -> Env Graph
  def structGraph graph =
      % return (graphToStructuredGraph (addPredecessors (map (fn (x,y) -> y) graph)))
      return (graphToStructuredGraph graph)

  op convertBSpec : BSpec -> Env Graph
  def convertBSpec bSpec = {
      coAlg <- return (succCoalgebra bSpec);
      (graph,n,visited) <- convertBSpecAux bSpec coAlg (final bSpec) FinitePolyMap.empty 0 (initial bSpec) FinitePolyMap.empty;
      print "convertBSpec VList =\n";
      print (printVList (mapToList visited));
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
     -> Coalgebra
     -> VrtxSet.Set
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> Vrtx.Vertex
     % -> FinitePolyMap.Map (Vrtx.Vertex,Index)
     -> FinitePolyMap.Map (String,Index)
     % -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (Vrtx.Vertex,Index))
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index))

(* The first test to see if the vertex is a final one is needed since the BSpec might be a loop in which case
there is branching from a state and one of the branches takes you to a final state. Perhaps the other tests
are no longer needed. *)

  def convertBSpecAux bSpec coAlg final graph n vertex visited =
    case evalPartial (visited,show vertex) of
      | Some index -> return (graph,n,visited)
      | None ->
         (case (toList (coAlg vertex)) of
            | [] -> 
                 if member? (final,vertex) then
                   return (graph,n,visited)
                 else
                   raise (SpecError (noPos, "convertBSpecAux: reached empty set of successors to vertex: " ^ (show vertex)))

            (* A single edge leaving the node means that the edge is labelled with a statement.  *)
            | [edge] -> {
                 visited <- return (update (visited,show vertex,n));
                 (node,newTerm) <- getEdgeTargetAndAction bSpec edge;
                 (graph,next,visited) <-
                   if member? (final,node) then
                     return (graph,n+1,visited)
                   else
                     convertBSpecAux bSpec coAlg final graph (n+1) node visited;
                 let graph =
                    if member? (final,node) then
                      update (graph,n,Return newTerm)
                    else
                      let index = vertexToIndex visited node in
                      update (graph,n,Block {statements=[Assign newTerm],next=index}) in
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

            | [leftEdge,rightEdge] -> {
                 visited <- return (update(visited,show vertex,n)); 
                 (leftNode,leftTerm) <- getEdgeTargetAndAction bSpec leftEdge;
                 (rightNode,rightTerm) <- getEdgeTargetAndAction bSpec rightEdge;
                 (graph,next1,visited) <- convertBSpecAux bSpec coAlg final graph (n+1) leftNode visited; 
                 (graph,next2,visited) <- convertBSpecAux bSpec coAlg final graph next1 rightNode visited;
                 let graph =
                   let leftIndex = vertexToIndex visited leftNode in
                   let rightIndex = vertexToIndex visited rightNode in
                   update (graph,n,Branch {condition=leftTerm,trueBranch=leftIndex,falseBranch=rightIndex}) in
                 return (graph,next2,visited)
               }
            | edges -> {
                  visited <- return (update(visited,show vertex,n)); 
                  (graph,next,visited,idx) <- makeBranches bSpec coAlg final graph n edges visited;
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
     -> Coalgebra
     -> VrtxSet.Set
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> List Edg.Edge
     -> FinitePolyMap.Map (String,Index)
     % -> FinitePolyMap.Map (Vrtx.Vertex,Index)
     % -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (Vrtx.Vertex,Index) * Index)
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index) * Index)
  def makeBranches bSpec coAlg final graph n edges visited =
    case edges of
      | [] -> raise (SpecError (noPos, "makeBranches: empty list in make branches"))
      | [x] -> raise (SpecError (noPos, "makeBranches: singleton list in make branches"))
      | [leftEdge,rightEdge] -> {
           (leftNode,leftTerm) <- getEdgeTargetAndAction bSpec leftEdge;
           (rightNode,rightTerm) <- getEdgeTargetAndAction bSpec rightEdge;
           (graph,next1,visited) <- convertBSpecAux bSpec coAlg final graph (n+1) leftNode visited; 
           (graph,next2,visited) <- convertBSpecAux bSpec coAlg final graph next1 rightNode visited;
           let graph =
             let leftIndex = vertexToIndex visited leftNode in
             let rightIndex = vertexToIndex visited rightNode in
             update (graph,n,Branch {condition=leftTerm,trueBranch=leftIndex,falseBranch=rightIndex}) in
           return (graph,next2,visited,n)
         }
      | leftEdge::edges -> {
           (leftNode,leftTerm) <- getEdgeTargetAndAction bSpec leftEdge;
           (graph,next1,visited,rightIndex) <- makeBranches bSpec coAlg final graph (n+1) edges visited;
           (graph,next2,visited) <- convertBSpecAux bSpec coAlg final graph next1 leftNode visited; 
           let graph =
             let leftIndex = vertexToIndex visited leftNode in
             update (graph,n,Branch {condition=leftTerm,trueBranch=leftIndex,falseBranch=rightIndex}) in
           return (graph,next2,visited,n)
         }

  (* This shouldn't be needed. We should always visit the target and we should never get None. *)
  % op vertexToIndex : FinitePolyMap.Map (Vrtx.Vertex,Index) -> Vrtx.Vertex -> Index
  op vertexToIndex : FinitePolyMap.Map (String,Index) -> Vrtx.Vertex -> Index
  def vertexToIndex visited vrtx =
    case evalPartial (visited,show vrtx) of
      | None -> ~1
      | Some index -> index

  op getEdgeTargetAndAction : BSpec -> Edg.Edge -> Env (Vrtx.Vertex * MSlang.Term)
  def getEdgeTargetAndAction bSpec edge = {
      node <- return (GraphMap.eval (target (shape (system bSpec)), edge));
      spc <- return (edgeLabel (system bSpec) edge);
      invars <- foldVariants (fn l -> fn claim -> return (cons (term claim,l))) [] (modeSpec spc);
      invars <- foldVariables infoToBindings invars (modeSpec spc);
      term <- case invars of
        | [] -> {
             print ("convertBSpecAux: no axiom for edge" ^ (Edg.show edge) ^ "\n");
             MSlangEnv.mkTuple ([],noPos)
           }
        | [term] -> return term
        | _ -> raise (SpecError (noPos, ppFormat (ppConcat [
                        ppString ("Something wrong with spec properties for edge " ^ (Edg.show edge) ^ "\n"),
                        ppBreak,
                        ppSep ppBreak (map pp invars)
                      ])));
      return (node,term)
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
