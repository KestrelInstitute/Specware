Proc qualifying spec
  import Procedure
  import ProcMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Finite 
      by {Dom._ +-> Id._, Cod._ +-> Proc._, KeyValue._ +-> IdProc._})
      by {Id.Dom +-> Id.Id, Proc.Cod +-> Proc.Procedure})
  op ProcMapEnv.fold : fa (a) (a -> Id.Id -> Proc.Procedure -> Env a) -> a -> ProcMap.Map -> Env a
endspec

(*
The fold definition doesn't belong here. Folds within a monad for maps, should as for sets,
be defined in a standard library.
*)
