
\begin{spec}
let Utils = USI(/Languages/PSL/Transformations/Utils) in
spec {
  import Coalgebra
  import Utils
\end{spec}

We define a structure to hold abstract code. We are assuming, of course,
that the program can be structured in this way. We need to classify the
types of graphs we are dealing with and prove the invariance.  One is
tempted to use a well-bracketing condition, but this will not hold if
we have return, break and continue statements.  And what if the language
has exceptions?

Seems a shame that we have to discover the structure having had it
before but lost in the translation to BSpecs.

In a more general setting, the pairs of things below would be lists. But
perhaps the transformation that takes arbitrary branching to if-then-else
cascading should be done in at the BSpec level. Needs thought.

  op structProcedure : Procedure -> AbstCode
  def structProcedure proc =

The reach set here is classified as follows.
for a vertex v, x \in reach v iff there is a path from x to v.

Actually it doesn't look like it matters if we do the reachability
forward or bacward .. we just reverse the termination test.

\begin{spec}
%   sort AbstStmt =
%       | Loop AbstCode * (List AbstCode)
%       | If (List AbstCode)
%       | Step PTerm
%       | Return
%       | Continue
%       | Break
%       | Nil

  sort AbstCode = List AbstStmt
  sort AbstStmt =
      | If AbstCode * AbstCode
      | Assign PTerm
      | Guard PTerm
      | Call PTerm

  op ppReachMap : PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem) -> Pretty
  def ppReachMap reachMap =
    ppConcat [
      ppString "reachMap = ",
      PolyMap.ppMap Vertex.ppElem (PolySet.ppSet Vertex.ppElem) reachMap,
      ppNewline
    ]

  op structPSpec : PSpec -> String
  def structPSpec pSpec = PolyMap.foldMap structProc "" pSpec.procedures

  op structProc : String -> String -> Procedure -> String
  def structProc str name proc =
    let pp =
      ppConcat [
        ppString ("name=" ^ name),
        ppNewline,
        ppAbstCode (structBSpec proc.code)
      ] in
    str ^ "\n" ^ (ppFormat pp)

  op structBSpec : BSpec -> AbstCode
  def structBSpec bSpec =
    if empty?_e bSpec.system.shape.edges then
      []
    else
      let reachMap = reachBackward bSpec in
      % let _ = writeLine (ppFormat (ppReachMap reachMap)) in
      let coAlg = succCoalgebra bSpec in
      let (code,dst) = structFrom coAlg bSpec reachMap bSpec.initial2 empty [] in
      code
\end{spec}

This structures a graph from a given \verb+src+ vertex. No support for loops at this stage.

This works as follows. We look at the successors of the given node. If
there are none, then we are done. If there is only one, then we handle
that edge on its own. If there are two, then we assume that we are dealing
with a conditional branch. So we process each side.  Processing side
'A' of the condional is ended when we reach a vertex for which there is
a backwards path back to a vertex in side 'B'.

\begin{spec}
  op structFrom :
       Coalgebra
    -> BSpec
    -> PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem)
    -> Vertex.Elem
    -> PolySet.Set Vertex.Elem
    -> AbstCode
    -> (AbstCode * Vertex.Elem)
  def structFrom coAlg bSpec reachMap src stopSet code =
    case takeTwo (coAlg src) of
      | Zero -> (code,src)
      | One (edge,dst) ->
          structEdge coAlg bSpec reachMap src stopSet code (edge,dst)
      | Two ((e1,d1),(e2,d2),rest) ->
          if ~(empty? rest) then
            fail "structFrom: more than two branches"
          else
            let (leftCode,leftStop) = structEdge coAlg bSpec reachMap src (singleton d2) [] (e1,d1) in
            let (rightCode,rightStop) = structEdge coAlg bSpec reachMap src (singleton d1) [] (e2,d2) in
            let _ =
              if ~(leftStop = rightStop) then
                fail "structFrom: left and right branches don't coincide"
              else
                () in
            let code = code ++ [If (leftCode,rightCode)] in
            structFrom coAlg bSpec reachMap leftStop stopSet code
\end{spec}
  
We stop recursing when we reach a vertex for which there is a path
back to the stop set.

\begin{spec}
  op structEdge :
       Coalgebra
    -> BSpec
    -> PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem)
    -> Vertex.Elem
    -> PolySet.Set Vertex.Elem
    -> AbstCode
    -> (Edge.Elem * Vertex.Elem)
    -> (AbstCode * Vertex.Elem)
  def structEdge coAlg bSpec reachMap src stopSet code (edge,dst) =
    let (forw,apex,back) = edgeLabel bSpec.system edge in
    let (transType,apexTerm) = 
      case apex.properties of
         | (Axiom, name, tyVars, term)::[] -> (name,term)
         | (Axiom, name, tyVars, term)::_ ->
             fail "inlineEdge: multiple axioms on an edge"
         | _::_ -> fail "structFrom: edge not labelled with an axiom"
         | [] -> fail "structFrom: edge not labelled" in
    let code =
      case apexTerm of
        | Fun (Bool true,_) -> code
        | _ ->
          (case transType of
              "guard" -> code ++ [Guard apexTerm] 
            | "assign" -> code ++ [Assign apexTerm] 
            | "call" -> code ++ [Call apexTerm]
            | str -> fail ("structEdge: bad axiom name:" ^ str)) in
    let reachSet = eval reachMap src in
    if existsInSet (fn vertex -> member? reachSet vertex) stopSet then
      (code,dst)
    else
      structFrom coAlg bSpec reachMap dst stopSet code
\end{spec}
          
\begin{spec}
  op ppAbstCode : AbstCode -> Pretty
  def ppAbstCode code = ppSep ppNewline (map ppAbstStmt code)
    
  op ppAbstStmt : AbstStmt -> Pretty
  def ppAbstStmt block =
    case block of
      | If (left,right) ->
          ppConcat [
            ppString "if {",
            ppNewline,
            ppNest 2 (ppAbstCode left),
            ppNewline,
            ppString "} else {",
            ppNewline,
            ppNest 2 (ppAbstCode right),
            ppNewline,
            ppString "}"
          ]
      | Guard term ->
          ppConcat [
            ppString "guard: ",
            ppPTerm term
          ]
      | Assign term ->
          ppConcat [
            ppString "assign: ",
            ppPTerm term
          ]
      | Call term ->
          ppConcat [
            ppString "call: ",
            ppPTerm term
          ]
\end{spec}

What is reachable from a node, is the union of all things reachable from its children.
This is what is going on abstractly.

\begin{spec}
  op reachBackward : BSpec -> PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem)
  def reachBackward bSpec =
    let coAlg = predCoalgebra bSpec in
    let vertex =
      case (takeTwo bSpec.final2) of
        | Zero -> fail "reachBackward: bSpec has no final state"
        | One dst -> dst
        | Two (_,_,_) -> fail "reachBackward: bSpec has multiple final states" in
    let (reachSet,reachMap) = reachFrom coAlg vertex emptyMap in
    reachMap
\end{spec}

\begin{verbatim}
   op reachFrom :
        Coalgebra
     -> Vertex.Elem
     -> PolySet.Set Vertex.Elem
   def reachFrom coAlg src = 
     let reachSet = PolySet.fold (reachEdge coAlg) empty (coAlg src) in
     in PolySet.insert reachSet src
     
   def reachEdge coAlg accum (edge,dst) =
     PolySet.union accum (reachFrom coAlg dst)
\end{verbatim}

Now add caching so that we visit every node once and record the information
for every node.

\begin{spec}
   op reachFrom :
        Coalgebra
     -> Vertex.Elem
     -> PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem)
     -> (PolySet.Set Vertex.Elem * PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem))
   def reachFrom coAlg src reachMap = 
     if (PolyMap.inDomain? reachMap src) then
       (PolyMap.eval reachMap src, reachMap)
     else
       let (reachSet,reachMap) = PolySet.fold (reachEdge coAlg) (PolySet.empty,reachMap) (coAlg src) in
       let reachSet = PolySet.insert reachSet src in
       let reachMap = PolyMap.update reachMap src reachSet in
       (reachSet,reachMap)

   op reachEdge :
         Coalgebra
      -> (PolySet.Set Vertex.Elem * PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem))
      -> (Edge.Elem * Vertex.Elem)
      -> (PolySet.Set Vertex.Elem * PolyMap.Map (Vertex.Elem, PolySet.Set Vertex.Elem))
   def reachEdge coAlg (accum,reachMap) (edge,dst) =
     let (reachSet,reachMap) = reachFrom coAlg dst reachMap in
     (PolySet.union accum reachSet, reachMap)
\end{spec}

\begin{spec}
}
\end{spec}
