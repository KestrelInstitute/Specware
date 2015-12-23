(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import Parse_ExternalDTD

  %  type ExternalID = (GenericID | well_formed_external_id?)
  %  type GenericID = {w1     : WhiteSpace,
  %                    public : Option PubidLiteral,
  %                    w2     : WhiteSpace,
  %                    system : Option SystemLiteral}
  %
  %  type PubidLiteral  = (QuotedText | well_formed_pubid_literal?)
  %  type SystemLiteral = QuotedText
  %  type QuotedText = (BoundedText | quoted_text?)
  %  type BoundedText = {qchar : QuoteChar,
  %                      text  : UString}

  %% TEMPORARY!
  def XML.get_uchars_from_uri (uri : ExternalID) : Env UChars =
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
