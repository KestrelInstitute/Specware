(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

LetWildPatToSeq qualifying spec

 import /Languages/MetaSlang/Specs/StandardSpec

 (**
  * transforms "let _ = t1 in t2" into "(t1;t2)"
  *)

 op SpecTransform.letWildPatToSeq (spc : Spec) : Spec =
  let
    def lettoseq (t) =
      case t of
	| Let ([(WildPat _, t1)], t2, b) -> 
	  lettoseq (Seq ([t1,t2], b))
	| Seq ((Seq (terms0, _))::terms, b) ->
	  lettoseq (Seq (terms0 ++ terms, b))
	| _ -> t
  in
  let typeid = (fn s -> s) in
  let pattid = (fn p -> p) in
  mapSpec (lettoseq, typeid, pattid) spc

end-spec
