XML qualifying spec

  import Parse_ExternalDTD

  %  sort ExternalID = (GenericID | well_formed_external_id?)
  %  sort GenericID = {w1     : WhiteSpace,
  %                    public : Option PubidLiteral,
  %                    w2     : WhiteSpace,
  %                    system : Option SystemLiteral}
  %
  %  sort PubidLiteral  = (QuotedText | well_formed_pubid_literal?)
  %  sort SystemLiteral = QuotedText
  %  sort QuotedText = (BoundedText | quoted_text?)
  %  sort BoundedText = {qchar : QuoteChar,
  %                      text  : UString}

  %% TEMPORARY!
  def get_uchars_from_uri (uri : ExternalID) : Env UChars =
    case uri.system of
      | Some sys_lit ->
        (let filename = string sys_lit.text in
	 case read_unicode_chars_from_file (filename, null_decoding) of
	   | Some uchars -> return uchars
	   | _ -> fail ("Problem getting chars from external dtd: " ^ filename))
      | _ ->
        case uri.public of
	  | Some pub_lit ->
	    (let filename = string pub_lit.text in
	     case read_unicode_chars_from_file (filename, null_decoding) of
	       | Some uchars -> return uchars
	       | _ -> fail ("Problem getting chars from external dtd: " ^ filename))
	  | _ ->
	    return []

endspec