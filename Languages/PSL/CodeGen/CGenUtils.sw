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
   def mapProcedure transformSpec procedure =
     let procedure = Proc.withModeSpec(procedure,(mapModeSpec transformSpec (Proc.modeSpec procedure))) in
     Proc.withBSpec(procedure,mapBSpec transformSpec (Proc.bSpec procedure))

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


  % --------------------------------------------------------------------------------

  op foldlSpecsOscarSpec: fa(a) (MSSpec * a -> a) -> a -> OscarSpec -> a
  def foldlSpecsOscarSpec f ival ospc =
    let ival = foldlSpecsModeSpec f ival ospc.modeSpec in
    foldlSpecsProcMap f ival ospc.procedures

  op foldlSpecsModeSpec: fa(a) (MSSpec * a -> a) -> a -> ModeSpec -> a
  def foldlSpecsModeSpec f ival mspec =
    f(specOf mspec,ival)

  op foldlSpecsProcMap: fa(a) (MSSpec * a -> a) -> a -> ProcMap.Map -> a
  def foldlSpecsProcMap f ival pmap =
    ProcMap.fold ((fn(ival,(_,procedure)) -> foldlSpecsProcedure f ival procedure),ival,pmap)

  op foldlSpecsProcedure: fa(a) (MSSpec * a -> a) -> a -> Procedure -> a
  def foldlSpecsProcedure f ival procedure =
    let ival = foldlSpecsModeSpec f ival (Proc.modeSpec procedure) in
    foldlSpecsBSpec f ival (Proc.bSpec procedure)

  op foldlSpecsProcedureOnlyModes: fa(a) (MSSpec * a -> a) -> a -> Procedure -> a
  def foldlSpecsProcedureOnlyModes f ival procedure =
    let ival = foldlSpecsModeSpec f ival (Proc.modeSpec procedure) in
    foldlSpecsBSpecOnlyModes f ival (Proc.bSpec procedure)

  op foldlSpecsBSpec: fa(a) (MSSpec * a -> a) -> a -> BSpec -> a
  def foldlSpecsBSpec f ival bspc =
    let ival = foldl (fn(m,ival) -> foldlSpecsMode f ival m) ival bspc.modes in
    let ival = foldl (fn(tr,ival) -> foldlSpecsTransition f ival tr) ival bspc.transitions in
    let ival = foldlSpecsCoAlg f ival (bspc.outTrans) in
    let ival = foldlSpecsCoAlg f ival (bspc.inTrans) in
    foldl (fn(m,ival) -> foldlSpecsMode f ival m) ival (bspc.final)

  op foldlSpecsBSpecOnlyModes: fa(a) (MSSpec * a -> a) -> a -> BSpec -> a
  def foldlSpecsBSpecOnlyModes f ival bspc =
    foldl (fn(m,ival) -> foldlSpecsMode f ival m) ival bspc.modes

  op foldlSpecsTransition: fa(a) (MSSpec * a -> a) -> a -> Transition -> a
  def foldlSpecsTransition f ival tr =
    let ival = foldlSpecsMode f ival (tr.source) in
    let ival = foldlSpecsMode f ival (tr.target) in
    foldlSpecsTransSpec f ival (tr.transSpec)

  op foldlSpecsTransSpec: fa(a) (MSSpec * a -> a) -> a -> TransSpec -> a
  def foldlSpecsTransSpec f ival (trspec as (_,mspec,_)) =
    foldlSpecsModeSpec f ival mspec

  op foldlSpecsMode: fa(a) (MSSpec * a -> a) -> a -> Mode -> a
  def foldlSpecsMode f ival m =
    foldlSpecsModeSpec f ival (m.modeSpec)

  op foldlSpecsCoAlg: fa(a) (MSSpec * a -> a) -> a -> CoAlg -> a
  def foldlSpecsCoAlg f ival coalg =
    foldl (fn((_,trlist),ival) -> 
	   foldl (fn(tr,ival) -> foldlSpecsTransition f ival tr
		 ) ival trlist
	  ) ival coalg

  % --------------------------------------------------------------------------------

  op mergeModeSpecs: Procedure -> MSSpec
  def mergeModeSpecs(procedure) =
    foldlSpecsProcedure (fn(spc,mergedspc) -> mergeSpecs(spc,mergedspc)) initialSpecInCat procedure


}
