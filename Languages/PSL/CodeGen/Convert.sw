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
    code = convertBSpec proc.code proc.dynamicSpec
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

  def printVList l = ppFormat (ppMap V.ppElem (fn n -> ppString (Nat.toString n)) l)
  def printNCList l = show "\n" (map (fn (dom,cod) ->
                        "("
                      ^ (Nat.toString dom)
                      ^ ","
                      ^ (printNodeContent cod)
                      ^ ")") l) 

  op convertBSpec : BSpec -> Spec -> Graph
  def convertBSpec bSpec spc =
    let coAlg = succCoalgebra bSpec in
    let (graph,n,visited) = convertBSpecAux bSpec spc coAlg bSpec.final emptyMap 0 bSpec.initial emptyMap in
    let _ = writeLine (printVList visited) in
    let _ = writeLine (printNCList (mapToList graph)) in
    let g = sortGraph (fn ((n,_),(m,_)) -> n < m) (mapToList graph) in
    let _ = writeLine (printNCList g) in
    let g = graphToStructuredGraph (addPredecessors (map (fn (x,y) -> y) g)) in
    let _ = writeLine (printGraph g) in
    g

  op convertBSpecAux :
        BSpec
     -> Spec
     -> Coalgebra
     -> V.Set
     -> PolyMap.Map (Index,NodeContent)
     -> Index
     -> V.Elem
     -> PolyMap.Map (V.Elem,Index)
     -> (PolyMap.Map (Index, NodeContent) * Index * PolyMap.Map (V.Elem,Index))

  def convertBSpecAux bSpec spc coAlg final graph n vertex visited =
    case (evalPartial visited vertex) of
      | Some index -> (graph,n,visited)
      | None ->
         (case (toList (coAlg vertex)) of
            | [] -> fail "reached empty set of successors"

            | [(edge,node)] ->
               let visited = update visited vertex n in
               let (graph,next,visited) =
                 if V.member? final node then
                   (graph,n+1,visited)
                 else
                   convertBSpecAux bSpec spc coAlg final graph (n+1) node visited in 
               let trans = subtractSpec (transitionSpec bSpec edge) spc in
               (case trans.properties of
                 | [] -> fail "no axiom"
                 | [(Axiom,name,tyVars,term)] ->
                     let graph =
                       if V.member? final node then
                         update graph n (Return term)
                       else
                         let index = eval visited node in
                         update graph n (Block {statements=[Assign term],next=index}) in
                     (graph,next,visited)
                 | _ -> fail (ppFormat (ppConcat [
                            ppString "Something wrong with spec properties",
                            ppBreak,
                            ppSep ppBreak (map ppAProperty trans.properties)
                          ])))

            | [(leftEdge,leftNode),(rightEdge,rightNode)] ->
               let visited = update visited vertex n in
               let (graph,next1,visited) = convertBSpecAux bSpec spc coAlg final graph (n+1) leftNode visited in
               let (graph,next2,visited) = convertBSpecAux bSpec spc coAlg final graph next1 rightNode visited in
               let leftTrans = subtractSpec (transitionSpec bSpec leftEdge) spc in
               let rightTrans = subtractSpec (transitionSpec bSpec rightEdge) spc in
               (case (leftTrans.properties,rightTrans.properties) of
                 | ([],_) -> fail "no left axiom"
                 | (_,[]) -> fail "no right axiom"
                 | ([(Axiom,leftName,leftTyVars,leftTerm)], [(Axiom,rightName,rightTyVars,rightTerm)]) ->
                     let leftIndex = eval visited leftNode in
                     let rightIndex = eval visited rightNode in
                     let graph = update graph n (Branch {condition=leftTerm,trueBranch=leftIndex,falseBranch=rightIndex}) in
                     (graph,next2,visited)
                 | _ -> fail (ppFormat (ppConcat [
                            ppString "Something wrong with spec properties",
                            ppBreak,
                            ppString "left = ",
                            ppSep ppBreak (map ppAProperty leftTrans.properties),
                            ppBreak,
                            ppString "right = ",
                            ppSep ppBreak (map ppAProperty rightTrans.properties)
                          ])))
            | _ -> fail "more than two successors?")
}
