spec
  import Specs/OpSets/AsLists
  import Specs/EdgeSets/AsLists
  import Specs/SortSets/AsLists
  import Specs/ProcMap/AsLists
  import Specs/ModeSpec/AsRecord
  import Specs/Claim/Legacy
  import Specs/ClaimSets/AsLists
  import CoalgMap qualifying translate (translate Specs/BSpecs/Maps/AsAssocLists
    by {KeyValue._ +-> VertexEdges._, Dom._ +-> Vrtx._, Cod._ +-> EdgSet._})
    by {Vrtx.Dom +-> Vrtx.Vertex, EdgSet.Cod +-> EdgSet.Set}

  % import Specs/Morphism/AsLists
endspec

