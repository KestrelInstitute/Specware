CGenUtils qualifying spec {

   import ../Semantics/Evaluate/Specs/Oscar

   sort OscarSpec = Oscar.Spec
   sort MSSpec = Spec.Spec

   % --------------------------------------------------------------------------------

   (**
    * processes the MetaSlang spec occuring in an Oscar spec
    * analog to mapSpec mapTerm etc.
    *)
   op mapOscarSpec: (MSSpec -> MSSpec) -> OscarSpec -> OscarSpec
   def mapOscarSpec transformSpec ospc =
     {
      modeSpec = mapModeSpec transformSpec ospc.modeSpec,
      procedures = mapProcMap transformSpec ospc.procedures
     }

   op mapModeSpec: (MSSpec -> MSSpec) -> ModeSpec -> ModeSpec
   def mapModeSpec transformSpec mspec =
     ModeSpec.withSpec(mspec,transformSpec(specOf mspec))

   op mapProcMap: (MSSpec -> MSSpec) -> ProcMap.Map -> ProcMap.Map
   def mapProcMap transformSpec pmap =
     ProcMap.map pmap (mapProcedure transformSpec)

   op mapProcedure: (MSSpec -> MSSpec) -> Procedure -> Procedure
   def mapProcedure transformSpec proc =
     let proc = Proc.withModeSpec(proc,(mapModeSpec transformSpec (Proc.modeSpec proc))) in
     Proc.withBSpec(proc,mapBSpec transformSpec (Proc.bSpec proc))

   op mapBSpec: (MSSpec -> MSSpec) -> BSpec -> BSpec
   def mapBSpec transformSpec bspec =
     {
      modes = map (mapMode transformSpec) bspec.modes,
      transitions = map (mapTransition transformSpec) bspec.transitions,
      outTrans = mapCoAlg transformSpec bspec.outTrans,
      inTrans = mapCoAlg transformSpec bspec.inTrans,
      initial = mapMode transformSpec bspec.initial,
      final = map (mapMode transformSpec) bspec.final,
      nextIdx = bspec.nextIdx,
      id = bspec.id
     }

   op mapTransition: (MSSpec -> MSSpec) -> Transition -> Transition
   def mapTransition transformSpec transition =
     {
      edge = transition.edge,
      source = mapMode transformSpec transition.source,
      target = mapMode transformSpec transition.target,
      transSpec = mapTransSpec transformSpec transition.transSpec
     }

   op mapTransSpec: (MSSpec -> MSSpec) -> TransSpec -> TransSpec
   def mapTransSpec transformSpec (tspec as (morph1,mspec,morph2)) =
     (morph1,mapModeSpec transformSpec mspec,morph2)

   op mapCoAlg: (MSSpec -> MSSpec) -> CoAlg -> CoAlg
   def mapCoAlg transformSpec coalg =
     map (fn(vtx,transitionList) -> (vtx,map (mapTransition transformSpec) transitionList)) coalg

   op mapMode: (MSSpec -> MSSpec) -> Mode -> Mode
   def mapMode transformSpec {vertex=vtx,modeSpec=mspec} =
      {vertex=vtx,modeSpec=mapModeSpec transformSpec mspec}
      
}