SpecMorph qualifying spec 
  import Spec
  import OpMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo
      by {Elem._ +-> Op._, KeyValue._ +-> OpPair._})
      by {Op.Elem +-> Op.OpInfo})
  
  import TypeMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo
      by {Elem._ +-> Type._, KeyValue._ +-> TypePair._})
      by {Type.Elem +-> Type.TypeInfo})
  
  type Morphism

  op dom : Morphism -> Spec.Spec
  op cod : Morphism -> Spec.Spec
  op typeMap : Morphism -> TypeMap.Map
  op opMap : Morphism -> OpMap.Map 

  type Morphism = {
    dom : Spec.Spec,
    cod : Spec.Spec,
    typeMap : TypeMap.Map,
    opMap : OpMap.Map
  }

  def dom morph = morph.dom
  def cod morph = morph.cod
  def typeMap morph = morph.typeMap
  def opMap morph = morph.opMap

  op makeMorphism : Spec.Spec -> Spec.Spec -> TypeMap.Map -> OpMap.Map -> Morphism
  def makeMorphism dom cod typeMap opMap = {
      dom = dom,
      cod = cod,
      typeMap = typeMap,
      opMap = opMap
    }

  op identTypeMap : TypeMap.Map
  op identOpMap : TypeMap.Map
endspec
