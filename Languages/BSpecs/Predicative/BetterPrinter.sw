spec {
  import Coalgebra
  import /Languages/MetaSlang/Specs/SimplePrinter

  op ppBSpecShort : BSpec -> Spec -> Pretty
  def ppBSpecShort bSpec spc =
    let (visited,ppCode) = ppFrom bSpec spc (succCoalgebra bSpec) (initial bSpec) V.empty ppNil in
      ppConcat [
        ppString "{",
        ppString "initial = ",
        V.ppElem (initial bSpec),
        ppString ", final = ",
        V.ppSet (final bSpec),
        ppNewline,
        ppString "system = ",
        ppCode
      ]

  op ppEdge :
       BSpec
    -> Spec
    -> Coalgebra
    -> V.Elem
    -> V.Set
    -> Pretty
    -> (E.Elem * V.Elem)
    -> (V.Set * Pretty)
  def ppEdge bSpec spc coAlg src visited ppBefore (edge,dst) =
    let (forw,apex,back) = edgeLabel (system bSpec) edge in
    let pp =
      ppConcat [
        ppBefore,
        ppNewline,
        ppIndent (ppConcat [
          E.ppElem edge,
          ppString ":",
          V.ppElem src,
          ppString "->",
          V.ppElem dst,
          ppString " +->",
          ppBreak,
          ppSep ppBreak [
            ppMorphismShort forw,
            ppIndent (ppASpec (subtractSpec apex spc)),
            ppMorphismShort back
          ]
        ])
     ] in
   if V.member? visited dst then
     (visited,pp)
   else
     ppFrom bSpec spc coAlg dst visited pp
   
  op ppFrom :
       BSpec
    -> Spec
    -> Coalgebra
    -> V.Elem
    -> V.Set
    -> Pretty
    -> (V.Set * Pretty)
  def ppFrom bSpec spc coAlg src visited ppBefore =
    let visited = V.insert visited src in
    let successors = coAlg src in
    let _ = 
      if (empty? successors) & ~(V.member? (final bSpec) src) then
        toScreen ("ppFrom: system has empty set of successors")
      else
        () in
      fold (fn (visited,ppBefore) -> fn (edge,dst) ->
        ppEdge bSpec spc coAlg src visited ppBefore (edge,dst))
          (visited,ppBefore) (coAlg src)

  op ppMorphismShort : Morphism -> Doc
  def ppMorphismShort {dom=_, cod=_, sortMap, opMap} = 
    let sortM =
      foldMap (fn newMap -> fn d -> fn c ->
          if d = c then
            newMap
          else
            update newMap d c) emptyMap sortMap in
    let opM =
      foldMap (fn newMap -> fn d -> fn c ->
          if d = c then
            newMap
          else
            update newMap d c) emptyMap opMap in
    let def ppM map = ppSep (ppString ",") (foldMap (fn l -> fn dom -> fn cod
               -> Cons (ppConcat [
                          ppQualifiedId dom,
                          ppString "+->",
                          ppQualifiedId cod], l)) [] map) in
    ppConcat [
      (if sortM = emptyMap then
         ppNil
       else
         ppConcat [
           ppString "sort map {",
           ppM sortM,
           ppString "} "
         ]),
      (if opM = emptyMap then
         ppNil
       else
         ppConcat [
           ppString "op map {",
           ppM opM,
           ppString "}"
         ])
    ]
}
