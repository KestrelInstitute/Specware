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
  import Colimit
  import ../Printer

  sort Morphism = {
    dom     : Spec,
    cod     : Spec,
    sortMap : MorphismSortMap,
    opMap   : MorphismOpMap
  }

  def makeMorphism (dom_spec, cod_spec, sort_map, op_map) =
   {dom     = dom_spec,
    cod     = cod_spec,
    sortMap = sort_map,
    opMap   = op_map}

  op ppQualifiedId : QualifiedId -> Doc
  def ppQualifiedId id = ppString (printQualifiedId id)
  
  op ppMorphism : Morphism -> Doc
  def ppMorphism {dom,cod,sortMap,opMap} = 
    ppConcat [
      ppString "Sort map=",
      ppNewline,
      ppNest 2 (ppMap ppQualifiedId ppQualifiedId sortMap),
      ppString "Op map=",
      ppNewline,
      ppNest 2 (ppMap ppQualifiedId ppQualifiedId opMap)
    ]


  def dom     morph = morph.dom
  def cod     morph = morph.cod
  def opMap   morph = morph.opMap
  def sortMap morph = morph.sortMap

  op compose : Morphism -> Morphism -> Morphism
  def compose mor1 mor2 = {
     dom     = mor1.dom,
     cod     = mor2.cod,
     sortMap = PolyMap.compose mor1.sortMap mor2.sortMap,
     opMap   = PolyMap.compose mor1.opMap mor2.opMap
   }

  def specCat = {
    dom = fn {dom = dom, cod = _,   sortMap = _, opMap = _} -> dom,
    cod = fn {dom = _,   cod = cod, sortMap = _, opMap = _} -> cod,
    ident = fn spc -> {
       dom     = spc,
       cod     = spc,
       sortMap = emptyMap,
       opMap   = emptyMap
    },
    colimit       = colimit,
    initialObject = emptySpec,
    compose       = compose,
    ppObj         = fn spc -> ppString (printSpec spc),
    % ppObj       = fn obj -> ppString "spec object ... later",
    ppArr         = ppMorphism
    % ppArr       = fn {dom = dom, cod = cod, sortMap = sm, opMap = om} ->
    % ppString "spec morphism ... later"
  }

 %% Used by colimit to actually build the initialCocone
 def makeSpecInitialCocone dg apex_spec cc_map =
  {cocone    = makeSpecCocone dg apex_spec cc_map,
   universal = fn cocone -> ident specCat (initialObject specCat)} % TODO: Fix

 def makeSpecCocone dg apex_spec cc_map =
  let apex_functor = functor dg in  % TODO: FIX
  let cc_nt = build (functor dg) apex_functor cc_map in
  {diagram  = dg,
   apex     = apex_spec,
   natTrans = cc_nt}

}
\end{spec}
