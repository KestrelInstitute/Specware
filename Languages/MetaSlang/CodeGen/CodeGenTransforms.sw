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


op unfoldSortAliases: Spec -> Spec
def unfoldSortAliases(spc) =
  let srts = sortsAsList(spc) in
  case find (fn(_,_,sortinfo) -> 
	     case sortinfo of
	       | (_,_,(_,Base(qid,_,_))::_) -> true
	       | _ -> false) srts of
    | None -> spc
    | Some (q0,id0,(_,_,(_,Base(qid,_,_))::_)) ->
      let qid0 = mkQualifiedId(q0,id0) in
      let _ = writeLine("sort alias found: "^printQualifiedId(qid0)^" = "^printQualifiedId(qid)) in
      let srts = filter (fn(q1,id1,_) -> ~((q1=q0)&(id1=id0))) srts in
      let sortmap = foldl (fn((q,id,sinfo),srtmap) ->
			    insertAQualifierMap(srtmap,q,id,sinfo))
                           emptyASortMap srts
      in
      let spc = setSorts(spc,sortmap) in
      let spc = mapSpec (id,
			 fn|s as Base(qid2,srt,b) -> if (qid2 = qid0) then Base(qid,srt,b) else s
			   |s -> s
			 ,id) spc
      in
      unfoldSortAliases spc

endspec
