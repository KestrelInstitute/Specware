(**
 * this spec contains code generation related transformations that are performed
 * before the actual code generation step
 *)

CodeGenTransforms qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec

% --------------------------------------------------------------------------------

(**
 * identifies the int sorts with the Integer types; this makes sense, if the base spec is not part of the
 * code generation and treated as builtin unit
 *)
op identifyIntSorts: Spec -> Spec
def identifyIntSorts(spc) =
  let
    def identifyIntSort(srt) =
      case srt of
	| Base(Qualified("Nat","Nat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| Base(Qualified("Nat","PosNat"),[],b) -> Base(Qualified("Integer","Integer"),[],b)
	| _ -> srt
  in
  let termid = (fn(t) -> t) in
  let pattid = (fn(p) -> p) in
  mapSpec (termid,identifyIntSort,pattid) spc

% --------------------------------------------------------------------------------

(**
 * transforms "let _ = t1 in t2" into "(t1;t2)"
 *)
op letWildPatToSeq: Spec -> Spec
def letWildPatToSeq(spc) =
  let
    def lettoseq(t) =
      case t of
	| Let([(WildPat _,t1)],t2,b) -> 
	  lettoseq(Seq([t1,t2],b))
	| Seq((Seq(terms0,_))::terms,b) ->
	  lettoseq(Seq(concat(terms0,terms),b))
	| _ -> t
  in
  let sortid = (fn(s) -> s) in
  let pattid = (fn(p) -> p) in
  mapSpec (lettoseq,sortid,pattid) spc

endspec
