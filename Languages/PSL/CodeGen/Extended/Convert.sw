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
	      print "\n----------\n";
	      visited <- return (update (visited,show (vertex mode),n));
	      (opt_guard_term, actions) <- getTransitionGuardAndActions transition;
	      print (case opt_guard_term of
		       | None    -> "No guard\n"
		       | Some tm -> "     guard: " ^ (printTerm tm) ^ "\n");
	      mapM (fn action -> print ("    action: " ^ (printTerm action) ^ "\n")) actions;
	      (graph,next,visited) <-
	        if Mode.member? final (target transition) then
		  return (graph, n+1, visited)
		else
		  let _ = toScreen ("recursion...\n") in
		  convertBSpecAux bSpec final graph (n+1) (target transition) visited;
	     let graph =
	         if Mode.member? final (target transition) then
		   case rev actions of
		     | [one_action] ->
		       let _ = toScreen ("one_action: " ^ (printTerm one_action) ^ "\n") in
		       update (graph, n, Return (spc, one_action))
		     | last_action :: rev_first_actions ->
		       let index = vertexToIndex visited (vertex (target transition)) in
		       let _ = toScreen ("Block:\n") in
		       update (graph, n, 
			       Block {statements = (map (fn action -> Assign (spc,action)) 
						        (rev rev_first_actions))
						    ++ 
						    [Return (spc,last_action)],
				      next       = index}) 
		       
		 else
		   let index = vertexToIndex visited (vertex (target transition)) in
		   let _ = map (fn action -> toScreen ("Assignment: " ^ (printTerm action) ^ "\n")) actions in
		   update (graph, n, 
			   Block {statements = map (fn action -> Assign (spc, action)) 
				                   actions,
				  next       = index}) 
	     in
		   {print "----------\n";
		    return (graph,next,visited)}
               }

           (*
	    If there are two edges leaving the node, then we we are dealing with a conditional.
	    At present we do not handle the case where there are more than two branches. Nor
	    do we make any effort to prove that the guard on one branch is equivalent to the
	    negation of the other branch. This should be done. More generally, we need to
	    prove, or have the user provide a proof, that the branches are disjoint or adopt
	    a different semantics where the order of the guards is significant.
	    *)

           | [left_trans,right_trans] -> 
	     let left_spec = specOf (Transition.modeSpec left_trans)  in
	     let right_spec= specOf (Transition.modeSpec right_trans) in
	    %let left_spec = transformSpecForCodeGen base left_spec in
	     {
	      visited <- return (update(visited,show (vertex mode),n)); 
	      (Some left_guard,  left_actions)  <- getTransitionGuardAndActions left_trans;
	      (Some right_guard, right_actions) <- getTransitionGuardAndActions right_trans;
	      print ("     guard(1): " ^ (printTerm left_guard) ^ "\n");
	      print ("     guard(R): " ^ (printTerm right_guard) ^ "\n");
	      mapM (fn action -> print (" left:  " ^ (printTerm action) ^ "\n")) left_actions;
	      mapM (fn action -> print (" right: " ^ (printTerm action) ^ "\n")) right_actions;
	     %(Some right_guard, right_actions) <- getTransitionGuardAndActions right_trans;
	      (g1, n1, visited) <- convertBSpecAux bSpec final graph (n+1) (target left_trans) visited; 
	      (g2, n2, visited) <- convertBSpecAux bSpec final g1    n1    (target right_trans) visited;
	      let left_index  = vertexToIndex visited (vertex (target left_trans))  in
	      let right_index = vertexToIndex visited (vertex (target right_trans)) in

	      let (g3, left_index, n3) = 
	          case left_actions of 
		    | [] -> (g2, left_index, n2)
		    | _ ->
		      (update (g2, n2, 
			       Block 
			       {statements = map (fn action -> Assign (left_spec, action)) left_actions,
				next       = left_index}),
		       n2,
		       n2 + 1)
	      in
	      let (g4, right_index, n4) = 
	          case right_actions of 
		    | [] -> (g3, right_index, n3)
		    | _ ->
		      (update (g3, n3,
			       Block 
			       {statements = map (fn action -> Assign (right_spec, action)) right_actions,
				next       = right_index}),
		       n3,
		       n3 + 1)
	      in
	      let g5 =
	          update (g4, n, 
			  Branch {condition   = (left_spec, left_guard),
				  trueBranch  = left_index,
				  falseBranch = right_index
				  })
	      in
		return (g5, n4, visited)
               }
	   | transitions -> 
	     {
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
      | []  -> raise (SpecError (noPos, "makeBranches: empty list in make branches"))
      | [x] -> raise (SpecError (noPos, "makeBranches: singleton list in make branches"))
      | [left_trans,right_trans] -> 
         let left_spec  = specOf (Transition.modeSpec left_trans)  in
	 let right_spec = specOf (Transition.modeSpec right_trans) in
	 %let left_spec = transformSpecForCodeGen base left_spec in
         {
	  (Some left_guard, left_actions)  <- getTransitionGuardAndActions left_trans;
	  (opt_right_guard, right_actions) <- getTransitionGuardAndActions right_trans;
	  print ("     guard(2): " ^ (printTerm left_guard)  ^ "\n");
	  print ("     guard(R): " ^ (case opt_right_guard of
					| Some tm -> (printTerm tm)
					| _ -> "No guard")
		 ^ "\n");
	  mapM (fn action -> print (" left:  " ^ (printTerm action) ^ "\n")) left_actions;
	  mapM (fn action -> print (" right: " ^ (printTerm action) ^ "\n")) right_actions;
	  (g1, n1, visited) <- convertBSpecAux bSpec final graph (n+1) (target left_trans)  visited; 
	  (g2, n2, visited) <- convertBSpecAux bSpec final g1    n1    (target right_trans) visited;
	  let left_index  = vertexToIndex visited (vertex (target left_trans))  in
	  let right_index = vertexToIndex visited (vertex (target right_trans)) in

	  let (g3, left_index, n3) = 
	      case left_actions of 
		| [] -> (g2, left_index, n2)
		| _ ->
		  (update (g2, n2, 
			   Block 
			   {statements = map (fn action -> Assign (left_spec, action)) left_actions,
			    next       = left_index}),
		   n2,
		   n2 + 1)
	  in
	  let (g4, right_index, n4) = 
	      case right_actions of 
		| [] -> (g3, right_index, n3)
		| _ ->
		  (update (g3, n3,
			   Block 
			   {statements = map (fn action -> Assign (right_spec, action)) right_actions,
			    next       = right_index}),
		   n3,
		   n3 + 1)
	  in
	  let g5 = 
	      update (g4, n, 
		      Branch {condition   = (left_spec, left_guard),
			      trueBranch  = left_index,
			      falseBranch = right_index
			     })
	  in
	    return (g5, n4, visited, n)
         }

      | left_trans::transitions ->
         let left_spec = specOf (Transition.modeSpec left_trans) in
	%let left_spec = transformSpecForCodeGen base left_spec  in
         {
	  (Some left_guard,  left_actions)  <- getTransitionGuardAndActions left_trans;
	  print ("     guard(3): " ^ (printTerm left_guard) ^ "\n");
	  print ("     guard(R): <others>\n");
	  mapM (fn action -> print ("left:  " ^ (printTerm action) ^ "\n")) left_actions;
	  (g1, n1, visited, right_index) <- makeBranches    bSpec final graph (n+1) transitions visited;
	  (g2, n2, visited)              <- convertBSpecAux bSpec final g1    n1    (target left_trans) visited; 
	  let left_index = vertexToIndex visited (vertex (target left_trans)) in
	  let (g3, left_index, n3) = 
	      case left_actions of 
		| [] -> (g2, left_index, n2)
		| _ ->
		  (update (g2, n2, 
			   Block 
			   {statements = map (fn action -> Assign (left_spec, action)) left_actions,
			    next       = left_index}),
		   n2,
		   n2 + 1)
	  in
	  let g4 =
	      update (g3, n,
		      Branch {condition   = (left_spec, left_guard),
			      trueBranch  = left_index,
			      falseBranch = right_index})
	  in
	    return (g4, n3, visited, n)
	   }

  (* This shouldn't be needed. We should always visit the target and we should never get None. *)
  % op vertexToIndex : FinitePolyMap.Map (Vrtx.Vertex,Index) -> Vrtx.Vertex -> Index
  op vertexToIndex : FinitePolyMap.Map (String,Index) -> Vrtx.Vertex -> Index
  def vertexToIndex visited vrtx =
    case evalPartial (visited,show vrtx) of
      | None -> ~1
      | Some index -> index

  op getTransitionGuardAndActions : Transition -> Env (Option MSlang.Term * List MSlang.Term)
  def getTransitionGuardAndActions transition = 
    {
     guard_terms  <- foldVariants (fn l -> fn claim -> return (cons (term claim,l))) [] (modeSpec (transSpec transition));
     action_terms <- foldVariables infoToBindings                                    [] (modeSpec (transSpec transition));
     case guard_terms of
       | [] ->
         return (None, action_terms)
       | [guard_term] ->
	 return (Some guard_term, action_terms)
       | _ -> 
	 raise (SpecError (noPos, 
			   ppFormat (ppConcat 
				     [
				      ppString ("Multiple guard terms for edge " ^ (Edg.show (edge transition)) ^ "\n"),
				      ppBreak,
				      ppSep ppBreak (map pp guard_terms),
				      case action_terms of							    
					| [] -> ppBreak
					| _ -> ppConcat [ppBreak,
							 ppString ("Action_terms:\n"),
							 ppSep ppBreak (map pp action_terms),
							 ppBreak,
							 ppString ("---------\n")]])))
	  }

  op infoToBindings : List MSlang.Term -> Op.OpInfo -> Env (List MSlang.Term)
  def infoToBindings bindings varInfo =
    let
      def mkEquals () =
        % let type = MSlang.freshMetaTyVar noPos in % this will fail -- need a fully elaborated type 
	let var_type = type varInfo in
        let var_equality_type = MSlang.mkArrow (MSlang.mkProduct ([var_type, var_type], noPos), 
						MSlang.boolType noPos,
						noPos)
	in
        MSlang.mkFun (Equals, var_equality_type, noPos)
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
