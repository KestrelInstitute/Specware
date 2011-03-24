LetWildPatToSeq qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec
import /Languages/SpecCalculus/Semantics/Evaluate/Spec/AddSpecElements 

op unfoldSortAliases (spc : Spec) : Spec =
  let srts = sortsAsList spc in
  case findLeftmost (fn (_, _, info) -> 
                       case sortInfoDefs info of
                         | srt :: _ -> 
                           (case sortInnerSort srt of
                              | Base (_, _, _) -> true
                              | Boolean _ -> true
                              | _ -> false)
                         | _ -> false)
            srts 
   of
    | None -> spc
    | Some (q0, id0, info) ->
      let (tvs, srt) = unpackFirstSortDef info in
      let (isBooleanAlias,opt_qid_psrts) = (case srt of
					      | Base(qid,psrts,_) -> (false,Some(qid,psrts))
					      | Boolean _ -> (true,None)
					      | _ -> (false,None))
      in
      %let Base (qid, psrts, _) = srt in
      let qid0 = Qualified (q0, id0) in
      %let _ = writeLine ("--> sort alias found: "^printQualifiedId qid0^" = "^printQualifiedId qid) in
      %let srts = filter (fn (q1, id1, _) -> ~((q1 = q0) && (id1 = id0))) srts in
      let sortmap = foldl (fn (srtmap, (q, id, info)) ->
			   let new_names = filter (fn Qualified(q1,id1) -> ~((q1 = q0) && (id1 = id0))) info.names in
			   case new_names of
			     | [] -> srtmap
			     | _ -> insertAQualifierMap (srtmap, q, id, info << {names = new_names}))
                          emptyASortMap
			  srts
      in
      let spc = setSorts (spc, sortmap) in
      let spc = setElements(spc, filterSpecElements (fn el ->
						     case el of
						       | Sort (qidi,_) -> ~(qid0 =qidi)
						       | SortDef (qidi,_) -> ~(qid0 =qidi)
						       | _ -> true)
			           spc.elements)
      in
      let
        def mapSrt s =
	  case opt_qid_psrts of 
	    | Some(qid,psrts) ->
	       (case s of
		  | Base (qid2, srts, b) ->
		    if qid2 = qid0 then 
		      %let Qualified(_,id) = qid in
		      %let Qualified(_,id2) = qid2 in
		      %let _ = writeLine("---> replacing type "^id2^" with "^id) in
		      Base (qid,  psrts, b)
		    else
		      Base (qid2, srts,  b)
		  | _ -> s)
	    | None ->
	      if isBooleanAlias then
		(case s of
		   | Base(qid2, srts, b) ->
		     if qid2 = qid0 then
		       let Qualified(_,id2) = qid2 in
		       %let _ = writeLine("---> replacing type "^id2^" with Boolean") in
		       Boolean b
		     else
		       s
		   | _ -> s)
	      else s
      in
      let spc = mapSpec (id, mapSrt, id) spc in
      unfoldSortAliases spc

end-spec
