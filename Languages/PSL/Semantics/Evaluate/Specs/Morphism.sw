SpecMorph qualifying spec 
  import Spec
  import OpMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo
      by {Elem._ +-> Op._, KeyValue._ +-> OpPair._})
      by {Op.Elem +-> Op.OpInfo})
  
  import SortMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo
      by {Elem._ +-> Sort._, KeyValue._ +-> SortPair._})
      by {Sort.Elem +-> Sort.SortInfo})
  
  sort Morphism

  op dom : Morphism -> Spec.Spec
  op cod : Morphism -> Spec.Spec
  op sortMap : Morphism -> SortMap.Map
  op opMap : Morphism -> OpMap.Map 

  sort Morphism = {
    dom : Spec.Spec,
    cod : Spec.Spec,
    sortMap : SortMap.Map,
    opMap : OpMap.Map
  }

  def dom morph = morph.dom
  def cod morph = morph.cod
  def sortMap morph = morph.sortMap
  def opMap morph = morph.opMap

  op makeMorphism : Spec.Spec -> Spec.Spec -> SortMap.Map -> OpMap.Map -> Morphism
  def makeMorphism dom cod sortMap opMap = {
      dom = dom,
      cod = cod,
      sortMap = sortMap,
      opMap = opMap
    }

  op identSortMap : SortMap.Map
  op identOpMap : SortMap.Map
endspec
