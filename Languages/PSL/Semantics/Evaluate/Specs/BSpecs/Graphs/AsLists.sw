let
  VertexSet = translate (translate ../../Sets/AsListsEq
    by {Elem.Elem +-> Vertex.Vertex})
    by {Elem._ +-> Vertex._, Set._ +-> VertexSet._}
  EdgeSet = translate (translate ../../Sets/AsListsEq
    by {Elem.Elem +-> Edge.Edge})
    by {Elem._ +-> Edge._, Set._ +-> EdgeSet._}
  GraphMap = translate (translate ../Maps/AsAssocLists
    by {KeyValue._ +-> EdgeVertex._, Dom._ +-> Edge._, Cod._ +-> Vertex._})
    by {Edge.Dom +-> Edge.Edge, Vertex.Cod +-> Vertex.Vertex}
in spec
    import VertexSet qualifying VertexSet
    import EdgeSet qualifying EdgeSet
    import GraphMap qualifying GraphMap
    import /Library/Structures/Data/Graphs/Finite

    sort Graph = {
      vertices : VertexSet.Set,
      edges : EdgeSet.Set,
      source : GraphMap.Map,
      target : GraphMap.Map
    }

    def vertices graph = graph.vertices
    def edges graph = graph.edges
    def source graph = graph.source
    def target graph = graph.target

    def empty = {
        vertices = VertexSet.empty,
        edges = EdgeSet.empty,
        source = GraphMap.empty,
        target = GraphMap.empty
      }

    def insertVertex graph vertex = {
        vertices = VertexSet.insert (vertices graph, vertex),
        edges = edges graph,
        source = source graph,
        target = target graph
      }

    (*
     * When we insert an edge, we also add the source and target for
     * the edge. In some contexts, this might be excessive as it may be
     * possible to prove that the vertices are already in the graph.
     *)
    def insertEdge graph edge dom cod = {
        vertices = VertexSet.insert (VertexSet.insert (vertices graph, dom),cod),
        edges = EdgeSet.insert (edges graph, edge),
        source = GraphMap.update (source graph, edge, dom),
        target = GraphMap.update (target graph, edge, cod)
      }
endspec
