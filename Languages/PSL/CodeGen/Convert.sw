spec {
  import SpecCalc qualifying /Languages/BSpecs/Predicative/Coalgebra
  import Struct qualifying GraphAnalysis
  import ../Semantics/PSpec
  % import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

  sort StructPSpec = {
    staticSpec : Spec,
    dynamicSpec : Spec,
    procedures : PolyMap.Map (QualifiedId,StructProcedure)
  }

  op convertPSpec : PSpec -> StructPSpec
  def convertPSpec pSpec = {
    staticSpec = pSpec.staticSpec,
    dynamicSpec = pSpec.dynamicSpec,
    procedures = mapMap convertProcedure pSpec.procedures
  }

  sort StructProcedure = {
    parameters : List String,
    return : Option String,
    staticSpec : Spec,
    dynamicSpec : Spec,
    code : Struct.Graph
  }

  op convertProcedure : Procedure -> StructProcedure
  def convertProcedure proc = {
    parameters = proc.parameters,
    return = proc.return,
    staticSpec = proc.staticSpec,
    dynamicSpec = proc.dynamicSpec,
    code = convertBSpec proc.code
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

  op printNodeContent : NodeContent -> String
  op printStructuredGraph : Struct.Graph -> String
  op addPredecessors : List NodeContent -> Graph

  op convertBSpec : BSpec -> Graph
  def convertBSpec bSpec =
    let coAlg = succCoalgebra bSpec in
    let (graph,n,visited) = convertBSpecAux bSpec coAlg emptyMap 0 bSpec.initial emptyMap in
    let g = sortGraph (fn ((n,_),(m,_)) -> n < m) graph in
    let _ = writeLine (show " " (map (fn (x,y) ->
                                      "("
                                    ^ (Nat.toString x)
                                    ^ ","
                                    ^ (printNodeContent y)
                                    ^ ")") g)) in
    let g = graphToStructuredGraph (addPredecessors (map (fn (x,y) -> y) graph)) in
    let _ = writeLine (printStructuredGraph g) in
    g

  op convertBSpecAux :
        BSpec
     -> Coalgebra
     -> PolyMap.Map (Index,NodeContent)
     -> Index
     -> V.Elem
     -> PolyMap.Map (V.Elem,Index)
     -> (PolyMap.Map (Index, NodeContent) * Index * PolyMap.Map (V.Elem,Index))

  def convertBSpecAux bSpec coAlg graph n vertex visited =
    case (evalPartial visited vertex) of
      | Some index -> (graph,n,visited)
      | None ->
         (case (toList (coAlg vertex)) of
            | [] -> (graph,n,visited)

            | [(edge,node)] ->
               let visited = update visited vertex n in
               let (graph,n,visited) = convertBSpecAux bSpec coAlg graph (n+1) node visited in 
               let trans = transitionSpec bSpec edge in
               (case trans.properties of
                 | [] -> fail "no axiom"
                 | [(Axiom,name,tyVars,term)] ->
                     let index = eval visited node in
                     let graph = update graph n (Block {statements=[Assign term],next=index}) in
                     (graph,n,visited)
                 | _ -> fail "bad property")

            | [(leftEdge,leftNode),(rightEdge,rightNode)] ->
               let visited = update visited vertex n in
               let (graph,n,visited) = convertBSpecAux bSpec coAlg graph (n+1) leftNode visited in
               let (graph,n,visited) = convertBSpecAux bSpec coAlg graph n rightNode visited in
               let leftTrans = transitionSpec bSpec leftEdge in
               let rightTrans = transitionSpec bSpec rightEdge in
               (case (leftTrans.properties,rightTrans.properties) of
                 | ([],_) -> fail "no left axiom"
                 | (_,[]) -> fail "no right axiom"
                 | ([(Axiom,leftName,leftTyVars,leftTerm)], [(Axiom,rightName,rightTyVars,rightTerm)]) ->
                     let leftIndex = eval visited leftNode in
                     let rightIndex = eval visited rightNode in
                     let graph = update graph n (Branch {condition=leftTerm,trueBranch=leftIndex,falseBranch=rightIndex}) in
                     (graph,n,visited)
                 | _ -> fail "bad property")
            | _ -> fail "more than two successors?")
}
