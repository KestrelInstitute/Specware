Proc qualifying spec
  import ../ProcMap
  import /Languages/SpecCalculus/Semantics/Monad
  import ProcMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite/AsAssocLists
      by {Dom._ +-> Id._, Cod._ +-> Proc._, KeyValue._ +-> IdProc._})
      by {Id.Dom +-> Id.Id, Proc.Cod +-> Proc.Procedure})

  def ProcMapEnv.fold f unit map =
    foldM (fn x -> fn (dom,cod) -> f x dom cod) unit map
endspec

