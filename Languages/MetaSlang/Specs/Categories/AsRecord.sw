\section{Category of Specs}

This will likely move to a new home.

This is a naive representation of the category of specs. Note that in
this case we are using a concrete record sort for categories. Categories
are data.  A category can be passed as an argument to a function.

There are many many options with respect to representing categories
including monomorphic variants and where there is no explicit sort
for categories.

It might be better to factor Morphism into a separate spec.
But it seems harder than expected to get this via refinement.

Much thought needs to go into the question of qualifiers.

Stephen has raised the question as to whether the maps might be implicitly
completed such that the maps only give the points where the morphism
differs from the identity.

\begin{spec}
SpecCat qualifying spec {
  import Cat qualifying /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
  import /Languages/MetaSlang/Specs/StandardSpec
  import PolyMap qualifying /Library/Structures/Data/Maps/Polymorphic

  sort Morphism = {
    dom : Spec,
    cod : Spec,
    sortMap : PolyMap.Map (QualifiedId, QualifiedId),
    opMap : PolyMap.Map (QualifiedId, QualifiedId)
  }

  op dom : Morphism -> Spec
  op cod : Morphism -> Spec
  op sortMap : Morphism -> PolyMap.Map (QualifiedId, QualifiedId)
  op opMap : Morphism -> PolyMap.Map (QualifiedId, QualifiedId)

  def dom morph = morph.dom
  def cod morph = morph.cod
  def opMap morph = morph.opMap
  def sortMap morph = morph.sortMap

  op compose : Morphism -> Morphism -> Morphism
  def compose mor1 mor2 = {
     dom = mor1.dom,
     cod = mor2.cod,
     sortMap = PolyMap.compose mor1.sortMap mor2.sortMap,
     opMap = PolyMap.compose mor1.opMap mor2.opMap
   }

  op specCat : Cat.Cat (Spec, Morphism)

  def specCat = {
    dom = fn {dom = dom, cod = _, sortMap = _, opMap = _} -> dom,
    cod = fn {dom = _, cod = cod, sortMap = _, opMap = _} -> cod,
    ident = fn spc -> {
       dom = spc,
       cod = spc,
       sortMap = emptyMap,
       opMap = emptyMap
    },
    colimit = fn dgm -> emptyInitialCocone, 
    compose = compose,
    ppObj = fn obj -> ppString "spec object ... later",
    ppArr = fn {dom = dom, cod = cod, sortMap = sm, opMap = om} ->
      ppString "spec morphism ... later"
  }
}
\end{spec}
