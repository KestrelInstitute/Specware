XML qualifying spec

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

  %% need to sanitize and strip quotes off of string that contains a string
  %% " \"abcd\" "  => 'abcd'
  def trim_whitespace_and_quotes (s : String) : String =
    let chars = explode s in
    let 
       def trim chars =
	 case chars of
	   | [] -> []
	   | #\s :: tail -> trim tail
	   | #\t :: tail -> trim tail
	   | #\n :: tail -> trim tail
	   | #"  :: tail -> tail             % silliness with emacs: #"
	   | _ -> chars
    in
      implode (rev (trim (rev (trim chars))))

  def fa (X) aux_internalize_Document (document : Document,
				       sd       : SortDescriptor,
				       table    : SortDescriptorExpansionTable)
    : Option X =
    internalize_Element (document.element, sd, table)
    
  def type_attribute (element : PossibleElement) : Option String =
    foldl (fn (attribute : ElementAttribute, result) ->
	   case result of
	     | Some _ -> result
	     | _ -> (if "type" = (string attribute.name) then
		       Some (foldl (fn (item, result) ->
				    result ^ (case item of
						| NonRef ustr -> string ustr
						| Ref _ -> "<xmlref>"))
			           ""
				   attribute.value.items)
		     else
		       result))
          None
	  element.stag.attributes

  def fa (X) internalize_Element (element : Element,
				  sd      : SortDescriptor,
				  table   : SortDescriptorExpansionTable)
    : Option X =
    let pattern   = expand_SortDescriptor (sd, table) in
    case element of
      | Full elt -> 
        let desired = print_SortDescriptor sd in
	let given_type = (case (type_attribute elt) of
			    | Some str -> str
			    | _ -> "unspecified type")
	in
	  %let _ = toScreen ("\nSeeking " ^ desired ^ " from " ^ string elt.stag.name ^" of " ^ given_type ^ "\n") in
	  internalize_PossibleElement (elt, pattern, table)
      | Empty _ -> fail "empty element"

  def fa (X) internalize_PossibleElement (element    : PossibleElement,
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
        %let _ = toScreen ("\nSeeking product\n") in
        let new_fields =
            map (fn (desired_name, desired_sd) ->
		 %let _ = toScreen ("\nSeeking " ^ desired_name ^ "\n") in
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
		     (case internalize_PossibleElement (matching_elt,
							expand_SortDescriptor (desired_sd, table),
							table) 
			of
			| Some x -> x
			| None -> fail "Could not internalize")
		   | None -> 
		     let _ = toScreen ("Could not find field " ^ desired_name) in
		     case desired_sd of
		       | Base (("Boolean", "Boolean"),       []) -> 
		         let _ = toScreen ("\nUsing default value of false for " ^ (print_SortDescriptor desired_sd) ^ "\n") in
			 magicCastFromBoolean false
		       | Base (("Nat", "Nat"),       []) -> 
		         let _ = toScreen ("\nUsing default value of 0 for "     ^ (print_SortDescriptor desired_sd) ^ "\n") in
			 magicCastFromInteger 0
		       | Base (("String", "String"), []) -> 
		         let _ = toScreen ("\nUsing default value of \"\" for "  ^ (print_SortDescriptor desired_sd) ^ "\n") in
			 magicCastFromString ""
		       | _ -> fail "Have defaults for just Boolean, Nat, and String")
	        sd_fields
	in
	  %let _ = toScreen ("\nFound product\n") in
	  Some (Magic.magicMakeProduct new_fields)
      | Base (qid, args) ->
	(case qid of
	  | ("Boolean", "Boolean") ->
	    let possible_datum = element.content.trailer in
	    Some (magicCastFromBoolean 
		  (case possible_datum of
		     | Some char_data -> 
		       (case string char_data of
			  | "true"  -> true
			  | "false" -> false)
		     | None -> 
		       let _ = toScreen ("\nUsing default value of false for " ^ (print_SortDescriptor sd_pattern) ^ "\n") in
		       false))
	  | ("Integer", "Integer") ->
	    let possible_datum = element.content.trailer in
	    Some (magicCastFromInteger 
		  (case possible_datum of
		     | Some char_data -> stringToInt (trim_whitespace (string char_data))
		     | None -> 
		       let _ = toScreen ("\nUsing default value of 0 for " ^ (print_SortDescriptor sd_pattern) ^ "\n") in
		       0))
	  | ("String",  "String") ->
	     let possible_datum = element.content.trailer in
	     Some (magicCastFromString 
		   (case possible_datum of
 		      | Some char_data -> 
		        %% '<...> "abcd" <...>'  => "abcd", as opposed to " \"abcd\" ",
		        %% which would print back out as '<...> " "abcd" " <...>'
		        trim_whitespace_and_quotes (string char_data)
		      | None -> 
			let _ = toScreen ("\nUsing default value of \"\" for " ^ (print_SortDescriptor sd_pattern) ^ "\n") in
			""))
	  | ("List",    "List") ->
	    let element_sd = expand_SortDescriptor (hd args, table) in
	    let data = rev (foldl (fn ((_,item), result) ->
				   case item of
				     | Element (Full elt) ->
				       %let _ = toScreen ("\nSeeking next list element: " ^ (print_SortDescriptor (hd args)) ^ "\n") in
				       (case internalize_PossibleElement (elt, element_sd, table) of
					  | Some datum -> cons (datum, result)
					  | _ -> 
					    let _ = toScreen ("Warning: failure looking for list element: " ^ 
							      (print_SortDescriptor element_sd) ^ "\n" )
					    in
					      result)
	                             | _ -> 
				       let _ = toScreen ("While looking for list element: " ^ (print_SortDescriptor element_sd) ^ "\n" ^
							 "Ignoring: " ^ (string (print_Content_Item item)) ^ "\n")
				       in
					 result)
			          []
				  element.content.items)
	    in
	      Some (magicCastFromList data)
	  | ("Char",    "Char")   -> fail "decoding char"
	  | ("Option" , "Option") -> fail "decoding option"
	  | (x, y) -> fail ("decoding " ^ x ^ "." ^ y))
      | CoProduct sd_options ->
	(let element_name = string element.stag.name in
	 case (find (fn sd_option -> 
		     (case type_attribute element of
			| Some str -> sd_option.1 = str
			| _ -> false)
			or
			(sd_option.1 = element_name))
	            sd_options)
	   of
	   | Some (_, Some matching_sd_option) -> 
	      (case internalize_PossibleElement (element,
						 expand_SortDescriptor (matching_sd_option, table),
						 table) 
		 of
		 | Some datum -> Some (magicMakeConstructor (element_name, datum))
		 | _ ->
		   fail ("looking for coproduct element: " ^ (print_SortDescriptor sd_pattern) ^ "\n" ))
           | _ ->
	     fail ("decoding CoProduct: XML " ^ element_name ^ " datum doesn't match any of " ^ 
		   (foldl (fn ((name, _), result) ->
			   case result of
			     | "" -> name
			     | _ -> result ^ ", " ^ name)
		          ""
			  sd_options)
		   ^ " coproduct options"))
      | _ ->
	fail "unrecognized type"

endspec
