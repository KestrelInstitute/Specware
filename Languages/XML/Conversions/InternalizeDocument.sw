spec

  import ../XML_Sig
  import /Languages/MetaSlang/Specs/Elaborate/SortDescriptor
  import ../Printers/XML_Printer % for error messages
  import Magic

  %% need to sanitize string before calling stringToInt
  def trim_whitespace (s : String) : String =
    let chars = explode s in
    let 
       def trim chars =
	 case chars of
	   | [] -> []
	   | #\s :: tail -> trim tail
	   | #\t :: tail -> trim tail
	   | #\n :: tail -> trim tail
	   | _ -> chars
    in
      implode (rev (trim (rev (trim chars))))

  def fa (X) aux_internalize_Document (document : Document,
				       sd       : SortDescriptor,
				       table    : SortDescriptorExpansionTable)
    : Option X =
    internalize_Element (document.element, sd, table)
    
  def fa (X) internalize_Element (element : Element,
				  sd      : SortDescriptor,
				  table   : SortDescriptorExpansionTable)
    : Option X =
    let pattern   = expand_SortDescriptor (sd, table) in
    % let attribute_info = ... in
    case element of
      | Full x -> internalize_content (x, (* sd, *) pattern, table)
      | Empty _ -> fail "empty element"

  def fa (X) internalize_content (element    : PossibleElement,
				  % sd         : SortDescriptor,
				  sd_pattern : SortDescriptor,
				  table      : SortDescriptorExpansionTable)
    : Option X =
    %%
    %%   sort Content = {items   : List (Option CharData * Content_Item),
    %%                   trailer : Option CharData}
    %% 
    %%   sort Content_Item = | Element   Element
    %%                       | Reference Reference
    %%                       | CDSect    CDSect
    %%                       | PI        PI
    %%                       | Comment   Comment
    %%
    let xml_items         = element.content.items   in
    case sd_pattern of
      | Product sd_fields ->
        %% Note that datum_elements is a heterogenous list,
        %%  hence cannot be properly typed in metaslang,
        %%  hence the "magic" here.
        let _ = toScreen ("\nBegin product\n") in
        let new_fields =
            map (fn (desired_name, desired_sd) ->
		 let _ = toScreen ("\nSeeking " ^ desired_name ^ "\n") in
		 let possible_matching_elt =
		     foldl (fn ((_, item), result) ->
			    case result of
			      | Some _ -> result
			      | _ ->
			        case item of
				  | Element (Full elt) -> 
				    if desired_name = string elt.stag.name then
				      Some elt
				    else
				      None)
		            None
		            xml_items
		 in
		 case possible_matching_elt of
		   | Some matching_elt ->
		     internalize_content (matching_elt,
					  % desired_sd,
					  expand_SortDescriptor (desired_sd, table),
					  table)
		   | None -> 
		     let _ = toScreen ("Could not find field " ^ desired_name) in
		     case desired_sd of
		       | Base (("Nat", "Nat"),       []) -> magicCastFromInteger 0
		       | Base (("String", "String"), []) -> magicCastFromString ""
		       | _ -> fail "Have defaults for just nat and string")
	        sd_fields
	in
        let _ = toScreen ("\nEnd product\n") in
	  Magic.magicMakeProduct new_fields
      | Base (qid, args) ->
	let possible_datum = element.content.trailer in
	(case qid of
	  | ("String",  "String") ->
	     Some (magicCastFromString 
		   (case possible_datum of
		      | Some char_data -> string char_data
		      | None -> "<default string>"))
	  | ("Integer", "Integer") ->
	    Some (magicCastFromInteger 
		  (case possible_datum of
		     | Some char_data -> stringToInt (trim_whitespace (string char_data))
		     | None -> 0))
	  | ("List",    "List") -> fail "decoding list"
	  | ("Boolean", "Boolean") ->
	    Some (magicCastFromBoolean 
		  (case possible_datum of
		     | Some char_data -> 
		       (case string char_data of
			  | "true"  -> true
			  | "false" -> false)
		     | None -> false))
	  | ("Char",    "Char")   -> fail "decoding char"
	  | ("Option" , "Option") -> fail "decoding option"
	  | _ -> fail "decoding mystery")
      | CoProduct sd_options ->
	fail ("decoding CoProduct: " ^ (string (print_Element (Full element))))
      | _ ->
	fail "?? decoding unrecognized type  ?? "


endspec