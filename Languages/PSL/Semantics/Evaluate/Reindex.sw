Reindex qualifying spec 
  import Oscar

  op newQid : State.Ref Id.Id
  def newQid = Ref (Id.makeId "reindex" "new")

  op makeNewVertexList : List Vrtx.Vertex -> Nat -> (List Vrtx.Vertex) * List (Vrtx.Vertex * Vrtx.Vertex)
  def makeNewVertexList vertices n =
    case vertices of
      | [] -> ([],[])
      | vrtx::rest ->
          let (newList,newMap) = makeNewVertexList rest (n + 1) in
          (cons (Nat (n,!newQid),newList), cons ((vrtx,Nat (n,!newQid)),newMap))
  
  op makeNewEdgeList : List Edg.Edge -> Nat -> (List Edg.Edge) * List (Edg.Edge * Edg.Edge)
  def makeNewEdgeList edges n =
    case edges of
      | [] -> ([],[])
      | edge::rest ->
          let (newList,newMap) = makeNewEdgeList rest (n + 1) in
          (cons (Nat (n,!newQid),newList), cons ((edge,Nat (n,!newQid)),newMap))
  
  op reindexBSpec : BSpec -> Id.Id -> BSpec 
  def reindexBSpec bSpec id =
    let _ = newQid := id in
    let (newVertexList,vertexAssoc) = makeNewVertexList (vertices (shape (system bSpec))) 0 in
    let (newEdgeList,edgeAssoc) = makeNewEdgeList (edges (shape (system bSpec))) 0 in
    let newSourceMap = reindexMap (source (shape (system bSpec))) edgeAssoc vertexAssoc in
    let newTargetMap = reindexMap (target (shape (system bSpec))) edgeAssoc vertexAssoc in
    let newEdgeMap = makeNewEdgeMap (edgeMap (system bSpec)) edgeAssoc in
    let newVertexMap = makeNewVertexMap (vertexMap (system bSpec)) edgeAssoc vertexAssoc in
    let newInitial = lookupVrtx vertexAssoc (initial bSpec) in
    let newFinal = List.map (fn vrtx -> lookupVrtx vertexAssoc vrtx) (final bSpec) in
    {
      initial = newInitial,
      final = newFinal,
      system = {
        shape = {
          vertices = newVertexList,
          edges = newEdgeList,
          source = newSourceMap,
          target = newTargetMap
        },
        edgeMap = newEdgeMap,
        vertexMap = newVertexMap
      }
    }
  
  op makeNewEdgeMap : EdgeMap.Map -> List (Edg.Edge * Edg.Edge) -> EdgeMap.Map
  def makeNewEdgeMap map edgeAssoc =
    case map of
      | [] -> []
      | (Forw edge,image)::rest -> Cons ((Forw (lookupEdge edgeAssoc edge),image),makeNewEdgeMap rest edgeAssoc)
      | (Back edge,image)::rest -> Cons ((Back (lookupEdge edgeAssoc edge),image),makeNewEdgeMap rest edgeAssoc)
  
  op makeNewVertexMap : VertexMap.Map -> List (Edg.Edge * Edg.Edge) -> List (Vrtx.Vertex * Vrtx.Vertex) -> VertexMap.Map
  def makeNewVertexMap map edgeAssoc vertexAssoc =
    case map of
      | [] -> []
      | (Edge edg,image)::rest -> Cons ((Edge (lookupEdge edgeAssoc edg),image),makeNewVertexMap rest edgeAssoc vertexAssoc)
      | (Vertex vrtx,image)::rest -> Cons ((Vertex (lookupVrtx vertexAssoc vrtx),image),makeNewVertexMap rest edgeAssoc vertexAssoc)
  
  op reindexMap : List (Edg.Edge * Vrtx.Vertex) ->  List (Edg.Edge * Edg.Edge) -> List (Vrtx.Vertex * Vrtx.Vertex) -> List (Edg.Edge * Vrtx.Vertex) 
  def reindexMap map edgeAssoc vertexAssoc = 
    case map of
      | [] -> []
      | (edge,cod)::rest ->
           let newMap = reindexMap rest edgeAssoc vertexAssoc in
           Cons ((lookupEdge edgeAssoc edge,lookupVrtx vertexAssoc cod),newMap)
   
  op lookupVrtx : List (Vrtx.Vertex * Vrtx.Vertex) -> Vrtx.Vertex -> Vrtx.Vertex
  def lookupVrtx map idx =
    case map of
      | [] -> fail "lookupVrtx failed"
      | (dom,cod)::rest ->
          if Vrtx.eq? (dom,idx) then
            cod
          else
            lookupVrtx rest idx

  op lookupEdge : List (Edg.Edge * Edg.Edge) -> Edg.Edge -> Edg.Edge
  def lookupEdge map idx =
    case map of
      | [] -> fail "lookupEdge failed"
      | (dom,cod)::rest ->
          if Edg.eq? (dom,idx) then
            cod
          else
            lookupEdge rest idx
endspec
