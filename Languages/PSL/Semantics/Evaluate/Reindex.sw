Reindex qualifying spec 
  import Oscar

  op newQid : State.Ref Id.Id
  def newQid = Ref (makeId "ReIndex")

  op counter : State.Ref Nat
  def counter = Ref 0

  op newIndex : () -> Nat
  def newIndex () =
    (counter := !counter + 1; !counter)

  op Oscar.reindex : Oscar.Spec -> Env Oscar.Spec
  def Oscar.reindex oscSpec =
    let def handler id proc except =
      case except of
        | SpecError (pos, msg) -> {
             print ("Oscar.reindex exception: procId=" ^ (Id.show id) ^ "\n");
             print (msg ^ "\n");
             % print (ppFormat (pp proc));
             % print "\n";
             raise (SpecError (pos, "except : " ^ msg))
           }
        | _ -> raise except
    in {
      procedures <- ProcMapEnv.fold (fn procMap -> fn procId -> fn proc -> {
          print ("Oscar.reindex: procId=" ^ (Id.show procId) ^ "\n");
          reindexedProc <- catch (Proc.reindex proc) (handler procId proc);
          return (ProcMap.update (procMap,procId,reindexedProc))
         }) ProcMap.empty (procedures oscSpec);
      return {
        modeSpec = modeSpec oscSpec,
        procedures = procedures
      }
  }

  op Proc.reindex : Procedure -> Env Procedure
  def Proc.reindex proc = return (proc withBSpec (BSpec.reindex (bSpec proc)))

  op makeNewVertexList : List Vrtx.Vertex -> Nat -> (List Vrtx.Vertex) * List (Vrtx.Vertex * Vrtx.Vertex)
  def makeNewVertexList vertices n =
    case vertices of
      | [] -> ([],[])
      | vrtx::rest ->
          let id = newIndex () in
          let (newList,newMap) = makeNewVertexList rest (n + 1) in
          (cons (Nat (id,!newQid),newList), cons ((vrtx,Nat (id,!newQid)),newMap))
  
  op makeNewEdgeList : List Edg.Edge -> Nat -> (List Edg.Edge) * List (Edg.Edge * Edg.Edge)
  def makeNewEdgeList edges n =
    case edges of
      | [] -> ([],[])
      | edge::rest ->
          let id = newIndex () in
          let (newList,newMap) = makeNewEdgeList rest (n + 1) in
          (cons (Nat (id,!newQid),newList), cons ((edge,Nat (id,!newQid)),newMap))
  
  op BSpec.reindex : BSpec -> BSpec 
  def BSpec.reindex bSpec =
    % let _ = newQid := id in
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
