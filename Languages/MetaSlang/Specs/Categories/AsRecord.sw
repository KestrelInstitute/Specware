(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

% Category of Specs

% This will likely move to a new home. This needs to be abstracted factored!

% This is a naive representation of the category of specs. Note that in
% this case we are using a concrete record type for categories. Categories
% are data.  A category can be passed as an argument to a function.

% There are many many options with respect to representing categories
% including monomorphic variants and where there is no explicit type
% for categories.

% It might be better to factor Morphism into a separate spec.
% But it seems harder than expected to get this via refinement.

% Much thought needs to go into the question of qualifiers.

% Stephen has raised the question as to whether the maps might be implicitly
% completed such that the maps only give the points where the morphism
% differs from the identity.

SpecCalc qualifying spec
 import /Languages/MetaSlang/Specs/AnnSpec
 import /Languages/MetaSlang/Specs/SimplePrinter
 import /Library/Structures/Data/Categories/Cocomplete/Polymorphic/AsRecord
 import /Languages/SpecCalculus/AbstractSyntax/Types  % SCTerm

 type QualifiedIdMap  = PolyMap.Map (QualifiedId, QualifiedId)
 type MorphismTypeMap = QualifiedIdMap
 type MorphismOpMap   = QualifiedIdMap
 type MorphismOpFixityMap   = PolyMap.Map (QualifiedId, QualifiedId * Fixity)

 op addOpFixity (cod_spc: Spec) (m: MorphismOpMap): MorphismOpFixityMap =
   foldMap (fn newMap -> fn d -> fn c ->
              case findTheOp(cod_spc, c) of
                | Some opinfo -> update newMap d (c, opinfo.fixity)
                | None -> newMap)       % shouldn't happen
     emptyMap m


  type Morphisms = List Morphism
  type Morphism = {
    dom     : Spec,
    cod     : Spec,
    typeMap : MorphismTypeMap,
    opMap   : MorphismOpMap,
    pragmas : SM_Pragmas,
    sm_tm   : Option SCTerm
  }

  op makeMorphism : Spec * Spec * MorphismTypeMap * MorphismOpMap * SM_Pragmas * Option SCTerm -> Morphism
  def makeMorphism (dom_spec, cod_spec, type_map, op_map, pragmas, sm_tm) =
   {dom     = dom_spec,
    cod     = cod_spec,
    typeMap = type_map,
    opMap   = op_map,
    pragmas = pragmas,
    sm_tm   = sm_tm}

 op emptyMorphism: Morphism =
   {dom     = emptySpec,
    cod     = emptySpec,
    typeMap = emptyMap,
    opMap   = emptyMap,
    pragmas = [],
    sm_tm   = None}

  % when omit printing the concrete domain and codomain specs.
  % When printing the maps, we print only where they differ
  % from the canonical injection (where they differ from
  % the identity)
  op ppMorphMap : PolyMap.Map (QualifiedId,QualifiedId) -> WLPretty
  def ppMorphMap map =
    let abbrevMap =
      foldMap (fn newMap -> fn d -> fn c ->
          if d = c then
            newMap
          else
            update newMap d c) emptyMap map in
    if abbrevMap = emptyMap then
      ppString "{}"
    else
      ppGroup (ppIndent (ppConcat [
        ppString "{",
        ppBreak,
        ppGroup (ppSep (ppCons (ppString ",") ppBreak) (foldMap (fn l -> fn dom -> fn cod
                 -> Cons (ppConcat [
                            ppQualifiedId dom,
                            ppString " +-> ",
                            ppQualifiedId cod], l)) [] abbrevMap)),
        ppBreak,
        ppString "}"
      ]))

  op  ppMorphPragmas : SM_Pragmas -> WLPretty
  def ppMorphPragmas pragmas =
    case pragmas of
      | [] -> ppNil
      | _ -> ppSep (ppString "") 
                   (map (fn ((prefix, body, postfix), _) -> 
			 ppString (prefix ^ body ^ postfix)) 
		        pragmas)

  op ppMorphism : Morphism -> Doc
  def ppMorphism {dom=_, cod=_, typeMap, opMap, pragmas, sm_tm =_} = 
    ppGroup (ppConcat [
      ppString "type map = ",
      ppMorphMap typeMap,
      ppNewline,
      ppString "op map = ",
      ppMorphMap opMap,
      ppMorphPragmas pragmas
    ])

  op dom     : Morphism -> Spec
  op cod     : Morphism -> Spec
  op opMap   : Morphism -> MorphismOpMap
  op typeMap : Morphism -> MorphismTypeMap

  def dom     morph = morph.dom
  def cod     morph = morph.cod
  def opMap   morph = morph.opMap
  def typeMap morph = morph.typeMap

  op compose : Morphism -> Morphism -> Morphism
  def compose mor1 mor2 = {
     dom     = mor1.dom,
     cod     = mor2.cod,
     typeMap = PolyMap.compose mor1.typeMap mor2.typeMap,
     opMap   = PolyMap.compose mor1.opMap mor2.opMap,
     pragmas = mor1.pragmas ++ mor2.pragmas,			   
     sm_tm   = mor1.sm_tm
   }

  %% We could have named InitialCocone (and SpecInitialCocone, etc.) 
  %%  as Colimit (and SpecColimit, etc.), but InitialCocone is a bit more explicit
  type SpecDiagram        = Cat.Diagram       (Spec, Morphism)
  type SpecCocone         = Cat.Cocone        (Spec, Morphism) 
  type SpecInitialCocone  = Cat.InitialCocone (Spec, Morphism) 
  op specColimit : SpecDiagram -> Option SpecInitialCocone * Option String


  op specCat : () -> Cat.Cat (Spec, Morphism)
  def specCat () = 
    {
    dom = fn {dom = dom, cod = _,   typeMap = _, opMap = _, pragmas = _, sm_tm = _} -> dom,
    cod = fn {dom = _,   cod = cod, typeMap = _, opMap = _, pragmas = _, sm_tm = _} -> cod,
    ident = fn spc -> {
       dom     = spc,
       cod     = spc,
       typeMap = emptyMap,
       opMap   = emptyMap,
       pragmas = [],		       
       sm_tm   = None
    },
    colimit       = specColimit,
    initialObject = initialSpecInCat,
    compose       = compose,
    ppObj         = ppASpec,
    ppArr         = ppMorphism
  }

 %% Used by colimit to actually build the initialCocone
 op makeSpecInitialCocone : SpecDiagram -> Spec -> PolyMap.Map (Vertex.Elem,Morphism) -> SpecInitialCocone
 def makeSpecInitialCocone dg apex_spec cc_map =
  let cat = cod (functor dg) in 
  {
   cocone    = makeSpecCocone dg apex_spec cc_map,
   universal = fn _(* other_cocone *) -> ident cat (initialObject cat) % TODO: This is bogus.  Fix it.
  }

 op makeSpecCocone : SpecDiagram -> Spec -> PolyMap.Map (Vertex.Elem,Morphism) -> SpecCocone
 def makeSpecCocone dg apex_spec cc_map =
  let apex_functor = functor dg in  % TODO: FIX
  let cc_nt = build (functor dg) apex_functor cc_map in
  {diagram  = dg,
   apex     = apex_spec,
   natTrans = cc_nt}

 op ppColimit : SpecInitialCocone -> Doc
 def ppColimit {cocone, universal=_} =
    ppConcat [ppString "colimit ",
	      ppNewline,
	      ppDiagram (diagram cocone)]

end-spec
