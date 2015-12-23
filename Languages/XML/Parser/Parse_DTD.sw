(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec
  import Parse_InternalDTD
  import Parse_ExternalDTD

  %% DocTypeDecl is a logical structure containing the internal and external subsets.
  %% The internal subset is parsed as part of the current character stream.
  %% It might contain an external id, which is a URI from which the external subset
  %% is parsed.  In particular, the external subset, if any, is parsed from a different
  %% character stream than this one.

  def parse_DTD (start : UChars) : Required DocTypeDecl =
    {
     %% If there are multiple declarations for a given name, the first occurrence is the match.
     %% Also, look in the internal subset first, then the external subset.
     (possible_internal_dtd, tail) <- parse_InternalDTD start;
     possible_external_dtd <- parse_ExternalDTD possible_internal_dtd;
     return ({internal = possible_internal_dtd,
	      external = possible_external_dtd,
	      entities = []},
	     tail)
     }

endspec