Convert qualifying spec
  import XTypes
  % import /Languages/PSL/AbstractSyntax/Types
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
        g0 <- return (mapToList graph);
        % print "\n\ngraph=\n";
        % print (printNCList g0);
        % print "\n";
        g <- return (sortGraph (fn ((n,_),(m,_)) -> n < m) g0);
        g <- return (addPredecessors (map (fn (x,y) -> y) g));
        % print "\nconvertBSpec NCList after sort\n";
        % print (printGraph g);
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

  def convertBSpecAux bSpec final_modes graph n mode visited =
    %% Depth first search, using visited to limit cycles...
    case evalPartial (visited,show (vertex mode)) of
      | Some index -> 
        return (graph,n,visited)
      | None ->
	let visited = update (visited,show (vertex mode),n) in
        case (outTrans bSpec mode) of
	  | [] -> 
	    if Mode.member? final_modes mode then
	      return (graph, n, visited)
	    else
	      raise (SpecError (noPos,
				"convertBSpecAux: reached empty set of successors to vertex: " 
				^ (show (vertex mode))))

	  | [transition] -> 
	    (* A single edge leaving the node means that the edge is labelled with a statement. *)
	    { 
	     (g, next, v) <- convertBSpecAux_1 bSpec final_modes graph n visited transition;
	     return (g, next, v)
	     }

	  | [left_trans,right_trans] -> 
	    (*
	     If there are two edges leaving the node, then we we are dealing with a conditional.
	     At present we do not handle the case where there are more than two branches. Nor
	     do we make any effort to prove that the guard on one branch is equivalent to the
	     negation of the other branch. This should be done. More generally, we need to
	     prove, or have the user provide a proof, that the branches are disjoint or adopt
	     a different semantics where the order of the guards is significant.
	     *)
	     {
	      (g, next, v) <- convertBSpecAux_2 bSpec final_modes graph n visited left_trans right_trans;
	      return (g, next, v)
	      }

	  | transitions -> 
	    {
	     (g, next, v, _) <- convertBSpecAux_N bSpec final_modes graph n transitions visited;
	     return (g, next, v)
	    }

  def my_update (msg, g : FinitePolyMap.Map (Index,NodeContent), n, v) =
    % let _ = toScreen ("\n " ^ msg ^ "\n") in
    % let _ = toScreen (" " ^ (toString n) ^ " : " ^ (anyToString v) ^ "\n") in
    update (g, n, v)

  def convertBSpecAux_1 bSpec final_modes graph n visited transition =
    let spc = specOf (Transition.modeSpec transition) in
    %let spc = transformSpecForCodeGen base spc in
    {
     (opt_guard_term, actions) <- getTransitionGuardAndActions transition;
     (graph,next,visited) <- 
       if Mode.member? final_modes (target transition) then
	 return (graph, n + 1, visited)
       else
	 convertBSpecAux bSpec final_modes graph (n + 1) (target transition) visited;
     %% At this point, we've processed everything reachable from here (with frontier at next).
     %% Now we need to attach some semantics to this node (at n).
     let target_index = vertexToIndex visited (vertex (target transition)) in
     let (graph, next, visited) =
         if Mode.member? final_modes (target transition) then
	   case rev actions of
	     | [] ->
	       (my_update ("1-F0",
			   graph, n, 
			   Block {statements = [],
				  next       = target_index}),
		next,
		visited)
	       
	     | [one_action] ->
	       (my_update ("1-F1",
			   graph, n, 
			   Return (spc, one_action)),
		next,
		visited)
	       
	     | last_action :: rev_first_actions ->
	       %% Put the first actions at n, 
	       %%  then branch to new node at frontier for a return of the last action.
	       let statements = 
	           foldl (fn (action, statements) -> 
			  cons (Assign (spc, action), statements))
		         []
			 rev_first_actions
	       in
	       let g2 = my_update ("1-FN",
				   graph, n,
				   Block {statements = statements,
					  next       = next})
	       in
	       (my_update ("1-FR",
			   g2, next, 
			   Return (spc, last_action)),
		next + 1,
		visited)
		   
	 else
	   (my_update ("1--N",
		       graph, n, 
		       Block {statements = map (fn action -> Assign (spc, action)) actions,
			      next       = target_index}),
	    next,
	    visited)
     in
       return (graph,next,visited)
      }

  op convertBSpecAux_2 :
        BSpec
     -> List Mode
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> FinitePolyMap.Map (String,Index)
     -> Transition
     -> Transition
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index))

  def convertBSpecAux_2 bSpec final_modes graph n visited left_trans right_trans =
    let left_spec = specOf (Transition.modeSpec left_trans)  in
    let right_spec= specOf (Transition.modeSpec right_trans) in
    %let left_spec = transformSpecForCodeGen base left_spec in
    {

     (opt_left_guard, left_actions) <- getTransitionGuardAndActions left_trans;
     (opt_right_guard, right_actions) <- getTransitionGuardAndActions right_trans;
     (g1, n1, visited) <- convertBSpecAux bSpec final_modes graph (n+1) (target left_trans)  visited; 
     (g2, n2, visited) <- convertBSpecAux bSpec final_modes g1    n1    (target right_trans) visited;
     %% At this point, we've processed everything reachable from here (with frontier at next).
     %% Now we need to attach some semantics to this node (at n).
     let original_left_index  = vertexToIndex visited (vertex (target left_trans))  in
     let original_right_index = vertexToIndex visited (vertex (target right_trans)) in
     let (g3, n3, revised_left_index) =
         case left_actions of 
	   | [] -> 
	     (g2, n2, original_left_index)
	   | _ ->
	     %% Interpolate left actions at frontier (n2) before branch to original left_index
	     (my_update ("2-L",
			 g2, n2,
			 Block 
			 {statements = map (fn action -> Assign (left_spec, action)) left_actions,
			  next       = original_left_index}),
	      n2 + 1,
	      n2)
     in
     let (g4, n4, revised_right_index) =
         case right_actions of 
	   | [] -> 
	     (g3, n3, original_right_index)
	   | _ ->
	     %% Interpolate right actions at frontier (n3) before branch to original right_index
	     (my_update ("2-R",
			 g3, n3,
			 Block 
			 {statements = map (fn action -> Assign (right_spec, action)) right_actions,
			  next       = original_right_index}),
	      n3 + 1,
	      n3)
     in
     let Some left_guard = opt_left_guard in
     let g5 =
         my_update ("2-B",
		    g4, n, 
		    Branch {condition   = (left_spec, left_guard),
			    trueBranch  = revised_left_index,
			    falseBranch = revised_right_index
			   })
     in
       return (g5, n4, visited)
      }

  op convertBSpecAux_N :
        BSpec
     -> List Mode
     -> FinitePolyMap.Map (Index,NodeContent)
     -> Index
     -> List Transition
     -> FinitePolyMap.Map (String,Index)
     -> Env (FinitePolyMap.Map (Index, NodeContent) * Index * FinitePolyMap.Map (String,Index) * Index)

  def convertBSpecAux_N bSpec final_modes graph n transitions visited =
    case transitions of
      | []  -> raise (SpecError (noPos, "convertBSpecAux_N: empty list of branches"))
      | [x] -> raise (SpecError (noPos, "convertBSpecAux_N: singleton list of branches"))

      | [left_trans, right_trans] -> 
        {
	 (graph, next, visited) <- convertBSpecAux_2 bSpec final_modes graph n visited left_trans right_trans;
	 return (graph, next, visited, n)
	}

      | left_trans :: right_transitions ->
	%% TODO: Find equality branch, don't just use left_trans...
        let left_spec = specOf (Transition.modeSpec left_trans) in
	%let left_spec = transformSpecForCodeGen base left_spec  in
        {
	 (opt_left_guard, left_actions) <- getTransitionGuardAndActions left_trans;
	 (g1, n1, visited, right_index) <- convertBSpecAux_N bSpec final_modes graph (n+1) right_transitions   visited;
	 (g2, n2, visited)              <- convertBSpecAux   bSpec final_modes g1    n1    (target left_trans) visited; 
	 original_left_index            <- return (vertexToIndex visited (vertex (target left_trans)));
	 (g3, n3, revised_left_index) <-
	     case left_actions of 
	       | [] -> 
	         return (g2, n2, original_left_index)
	       | _ ->
                 {(g, next, v) <- convertBSpecAux_1 bSpec final_modes g2 n2 visited left_trans;
		  return (g, next, n2)};
	 let Some left_guard = opt_left_guard in
	 let g4 =
	     my_update ("N-B",
			g3, n,
			Branch {condition   = (left_spec, left_guard),
				trueBranch  = revised_left_index,
				falseBranch = right_index})
	 in
	   %% This node will become the right index of the caller (if there is one).
	   return (g4, n3, visited, n)
	  }

  (* This shouldn't be needed. We should always visit the target and we should never get None. *)
  % op vertexToIndex : FinitePolyMap.Map (Vrtx.Vertex,Index) -> Vrtx.Vertex -> Index
  op vertexToIndex : FinitePolyMap.Map (String,Index) -> Vrtx.Vertex -> Index
  def vertexToIndex visited vrtx =
    case evalPartial (visited,show vrtx) of
      | None -> ~1
      | Some index -> index

  op ppTerms : String -> List MS.Term -> String
  def ppTerms prefix terms =
    ppFormat (ppConcat [ppString prefix,
			ppNest (length prefix) (ppSep ppNewline (map ppATerm terms))])

  op getTransitionGuardAndActions : Transition -> Env (Option MSlang.Term * List MSlang.Term)
  def getTransitionGuardAndActions transition = 
    let ms = modeSpec (transSpec transition) in
    {

     %% foldVariants  maps over spec properties (i.e. axioms, theorems, etc.) 
     %%   looking for those listed as invariants in the modespec

     %% foldVariables maps over spec ops
     %%     print (case (edge transition) of
     %%	      | Nat (_, qid) -> "\n------\nStep: " ^ (printQualifiedId qid) ^ "\n\n"
     %%	      | _ -> print ("\n ?? \n\n"));
     %%     print ("  Invariants: " ^ (anyToString (invariants ms)) ^ "\n");
     %%     print ("   Variables: " ^ 
     %%	    (foldVariables (fn s -> 
     %%			    fn (qid :: _, _, _, _) -> 
     %%			    s ^ (printQualifiedId qid) ^ "  ")
     %%	                   "" 
     %%			   ms) ^ 
     %%	    "\n");

     %% Note: The variants of the transition are invariants of the modespec, so
     %%       foldVariants is implemended to map over the invariants of the modespec.
     (guard_terms, aux_action_terms)  <- foldVariants (fn (guards, actions) -> fn claim -> 
						       if claim.2 = "Guard" then
							 return (cons (term claim,guards),
								 actions)
						       else
							 return (guards,
								 cons (term claim, actions)))
                                                      ([], [])
						      ms;
     action_terms <- foldVariables infoToBindings [] ms;

     % print ((ppTerms "Aux    terms: " aux_action_terms) ^ "\n");
     % print ((ppTerms "Action terms: " action_terms)     ^ "\n");
     % print ((ppTerms "Guard  terms: " guard_terms)      ^ "\n");

     action_terms <- return (aux_action_terms ++ (rev action_terms));
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
      if isPrimedName? (idOf varInfo) then
        case (term varInfo) of
          | None -> return bindings
          | Some trm -> 
	    let opTerm = mkFun (Op (idOf varInfo,Nonfix), type varInfo, noPos) in
	    return (cons (mkEquality opTerm trm, bindings))
      else
        return bindings

  op isPrimedName? : QualifiedId -> Boolean
  def isPrimedName? (qualId as (Qualified (qual,id))) = hd (rev (explode id)) = #'
endspec
