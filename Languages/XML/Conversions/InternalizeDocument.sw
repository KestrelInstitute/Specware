(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

XML qualifying spec

  %% Throughout these routines we often have a value typed as "Option X",
  %% and cast created values using routines with names such as "castFromXXX"
  %% or "magicMakeXXX"
  %%
  %% Those casts map variously typed elements to the arbitrary type X,
  %% so we will need independent assurances we are not creating ill-typed
  %% structures.  For now those assurances are via hand-waving.

  import InternalizeAux
  import /Library/Legacy/Utilities/System

  op [X] aux_internalize_Document (document : Document,
                                   sd       : TypeDescriptor,
                                   table    : TypeDescriptorExpansionTable)
    : Option X =
    aux_internalize_Element (document.element, sd, table)
    
  %% we seem to need these op decls to avoid conflicts caused when 
  %% the type checker assumes various invocations are for monomophic versions,
  %% e.g. Option String -- [bug in type checker?]

  op [X] aux_internalize_Element (element     : Element,
                                  sd          : TypeDescriptor,
                                  table       : TypeDescriptorExpansionTable)
    : Option X =
    let expanded_sd : TypeDescriptor = expand_TypeDescriptor (sd, table) in
    case element of

      | Full elt ->
	%%% let _ = (let desired = print_TypeDescriptor sd in
	%%% 	 let given_type = (case (element_type_attribute elt) of
	%%% 			     | Some str -> str
	%%% 			     | _ -> "unspecified type")
	%%% 	 in
	%%% 	   toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from xml element named " ^ string elt.stag.name ^" of " ^ given_type ^ "\n"))
	%%% in
	internalize_PossibleElement (elt, sd, expanded_sd, table)

      | Empty etag -> 
	%%% let _ = (let desired = print_TypeDescriptor sd in
	%%% 	let given_type = (case (etag_type_attribute etag) of
        %%% 			    | Some str -> str
        %%% 			    | _ -> "unspecified type")
        %%% 	in
        %%% 	  toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from empty xml element named " ^ string etag.name ^" of " ^ given_type ^ "\n"))
        %%% in
	internalize_EmptyElemTag (etag, sd, expanded_sd, table)

  op [X] internalize_PossibleElement (element     : PossibleElement,
                                      sd          : TypeDescriptor,
                                      expanded_sd : TypeDescriptor,
                                      table       : TypeDescriptorExpansionTable)
    : Option X =
    %%
    %%   type Content = {items   : List (Option CharData * Content_Item),
    %%                   trailer : Option CharData}
    %% 
    %%   type Content_Item = | Element   Element
    %%                       | Reference Reference
    %%                       | CDSect    CDSect
    %%                       | PI        PI
    %%                       | Comment   Comment
    %%
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as " ^ (print_TypeDescriptor sd) ^ "\n") in
    case expanded_sd of
      | Product   field_sds    -> internalize_PossibleElement_as_product   (element, sd, field_sds,    table)
      | CoProduct optional_sds -> internalize_PossibleElement_as_coproduct (element, sd, optional_sds, table)
      | Base      (qid, args)  -> internalize_PossibleElement_as_base_type (element, sd, qid, args,    table)
      | Boolean                -> internalize_PossibleElement_as_Boolean   element
      | _ -> fail "unrecognized type"


  op making_attributes_and_elements_explicit? (field_sds  : List (IdDescriptor * TypeDescriptor)) 
    : Bool =
    case field_sds of
      | [("attributes", _), ("elements", _)] -> true
      | _ -> false

  op explicit_attributes_and_elements? (element : PossibleElement)
    : Bool =
    (case find_matching_sub_element (element, "attributes") of | Some _ -> true | _ -> false)
    &&
    (case find_matching_sub_element (element, "elements")   of | Some _ -> true | _ -> false)

  op [X] internalize_PossibleElement_as_product (element    : PossibleElement,
                                                 product_sd : TypeDescriptor,
                                                 field_sds  : List (IdDescriptor * TypeDescriptor),
                                                 table      : TypeDescriptorExpansionTable)
    : Option X =
    %% Note that datum_elements is a heterogenous list,
    %%  hence cannot be properly typed in metaslang,
    %%  hence there is "magic" here.
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as product for " ^ (print_TypeDescriptor product_sd) ^ "\n") in
    if (making_attributes_and_elements_explicit? field_sds) && ~(explicit_attributes_and_elements? element) then
      internalize_Attributes_and_Elements (Full element, product_sd, table)
    else
      let possible_magic_values =
          foldl (fn (possible_magic_values, (field_name, field_sd)) ->
		 case possible_magic_values of
		   | None -> None
		   | Some magic_values ->
		     %%% let _ = toScreen ((level_str level) ^ "First, seeking field named " ^ field_name ^ " to construct " ^ (print_TypeDescriptor field_sd) ^ "\n") in
		     case (case find_matching_sub_element (element, field_name) of
			     | Some matching_elt ->
			       (%%% let _ = toScreen ((level_str level) ^ "Second, internalizing matching xml element named " ^ (string matching_elt.stag.name) ^ " as " ^ (print_TypeDescriptor field_sd) ^ "\n") in
				let expanded_field_sd = expand_TypeDescriptor (field_sd, table) in
				internalize_PossibleElement (matching_elt, field_sd, expanded_field_sd, table))
			     | None -> 
			       case default_field_value (element, field_sd, table) of
				 | Some field_value  -> Some field_value
				 | None -> 
				   % let expanded_field_sd = expand_TypeDescriptor (field_sd, table) in
				 default_field_value (element, field_sd, table))
		       of 
                         %% magic_values is a list over some unknown generic type
			 %% In practice, each field_value has its own independent type, 
			 %% but we have cast all of them to that generic type.
			 %% Thus we must be very careful what we do with magic_value:
			 %% operations such as cons/hd/tl/rev are ok.
			 | Some field_value  -> Some (field_value :: magic_values)
			 | None -> None)
	        (Some [])
		field_sds
      in
	case possible_magic_values of
	  | Some magic_values ->
	    %%% let _ = toScreen ((level_str level) ^ "Found product\n") in
	    %% magicMakeProduct restructures the implementation of magic_values from a list to a product 
	    %% See casting note at start of file.
	    Some (Magic.magicMakeProduct (reverse magic_values))
	  | _ -> None


  op find_matching_sub_element (element    : PossibleElement,
                                field_name : IdDescriptor)
    : Option PossibleElement =
    foldl (fn (result, (_, item)) ->
	   case result of
	     | Some _ -> result
	     | _ ->
	       case item of
		 | Element (Full elt) -> 
		   if ms_name_matches_xml_name? (field_name, elt.stag.name) then
		     %%% let _ = toScreen ((level_str level) ^ "Found xml element named " ^ field_name ^ "\n") in
		     Some elt
		   else
		     %%% let _ = toScreen ((level_str level) ^ "No match: " ^ field_name ^ " with " ^ (string elt.stag.name) ^ "\n") in
		     None
		 | Element (Empty etag) -> 
		     % let _ = toScreen ((level_str level) ^ "Saw empty " ^ (string etag.name) ^ "\n") in
		     None)
          None
	  element.content.items

  op [X] default_field_value (element    : PossibleElement,
                              field_sd   : TypeDescriptor, 
                              table      : TypeDescriptorExpansionTable)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Could not find field " ^ field_name ^ "\n") in
    case field_sd of % don't chase expansion, as that would expand list and option
      | Boolean -> 
        %%% let _ = toScreen ((level_str level) ^ "Using default value of false for Bool\n") in
	Some (magicCastFromBool false)
      | Base (("Nat", "Nat"),       []) -> 
	%%% let _ = toScreen ((level_str level) ^ "Using default value of 0 for "     ^ (print_TypeDescriptor field_sd) ^ "\n") in
	Some (magicCastFromInt 0)
      | Base (("String", "String"), []) -> 
	%%% let _ = toScreen ((level_str level) ^ "Using default value of \"\" for "  ^ (print_TypeDescriptor field_sd) ^ "\n") in
	Some (magicCastFromString "")
      | Base (("List", "List"), args) -> 
	Some (case internalize_PossibleElement_as_List (element, args, table) of
		| Some XX -> magicCastFromList XX
		| _       -> magicCastFromList [])
      | Base (("Option", "Option"), _) -> 
	Some (magicCastFromOption None)
      | _ -> 
        %% todo: add hook for user defined base types
	None

  op [X] internalize_PossibleElement_as_coproduct (element      : PossibleElement,
                                                   coproduct_sd : TypeDescriptor,
                                                   sd_options   : List (IdDescriptor * Option TypeDescriptor),
                                                   table        : TypeDescriptorExpansionTable)
    : Option X =
    let element_name = element.stag.name in
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element_name) ^ " as coproduct for " ^ (print_TypeDescriptor coproduct_sd) ^ "\n") in
    case (findLeftmost (fn sd_option -> 
                          (case element_type_attribute element of
                             | Some str -> sd_option.1 = str
                             | _ -> false)
                         ||
                           ms_name_matches_xml_name? (sd_option.1, element_name))
	       sd_options)
      of
       | Some (_, Some matching_sd_option) -> 
	 (case internalize_PossibleElement (element,
					    coproduct_sd,
					    expand_TypeDescriptor (matching_sd_option, table),
					    table)
	    of
	     | Some datum -> Some (magicMakeConstructor (convert_xml_name_to_ms_name element_name, datum))
	     | _ ->
	       fail ("looking for coproduct element: " ^ (print_TypeDescriptor coproduct_sd) ^ "\n" ))
       | _ ->
	 case element.content.items of
	   | [(_, Element (Full elt))] -> 
	     %% looking at "<n> <baz> ,,, </baz>  </n>" while expecting a coproduct with possible constructor baz
	     %% which can happen while looking at "<foo> <1> ... </1> .... <n> <baz> ,,, </baz> </n> ... </foo>"
	     %% ? also check for name to be "1" "2" etc.? (or would that make explicitly named products fail?)
	     (case internalize_PossibleElement (elt, coproduct_sd, coproduct_sd, table) of
		| Some datum -> Some (magicMakeConstructor (convert_xml_name_to_ms_name elt.stag.name, datum))
		| _ ->
		  fail ("looking for coproduct element: " ^ (print_TypeDescriptor coproduct_sd) ^ "\n" ))
	   | _ -> 
	     fail ("decoding CoProduct: XML datum named " ^ (string element_name) ^ " doesn't match any of " ^ 
		   (foldl (fn (result, (name, _)) ->
			   case result of
			     | "" -> name
			     | _ -> result ^ ", " ^ name)
		          ""
			  sd_options)
		   ^ " coproduct options")

  op [X] internalize_PossibleElement_as_base_type (element : PossibleElement,
                                                   base_sd : TypeDescriptor,
                                                   qid     : QIdDescriptor,
                                                   args    : List TypeDescriptor,
                                                   table   : TypeDescriptorExpansionTable)
    : Option X =
    case qid of
      | ("Integer", "Int")    -> internalize_PossibleElement_as_Int    (element)
      | ("String",  "String") -> internalize_PossibleElement_as_String (element)
      | ("Char",    "Char")   -> internalize_PossibleElement_as_Char   (element)
      | ("List",    "List")   -> internalize_PossibleElement_as_List   (element, args,    table)
      | ("Option" , "Option") -> internalize_PossibleElement_as_Option (element, head args, table)
      | _                     -> internalize_PossibleElement_ad_hoc    (element, base_sd (* , qid, args, table, *))

  op [X] internalize_PossibleElement_as_Boolean (element : PossibleElement)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Bool for " ^ (print_TypeDescriptor boolean_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromBool 
	  (case possible_datum of
	     | Some char_data -> 
	       (case string char_data of
		  | "true"  -> true
		  | "false" -> false)
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of false for " ^ (print_TypeDescriptor boolean_sd) ^ "\n") in
	       false))


  op [X] internalize_PossibleElement_as_Int (element : PossibleElement)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Int for " ^ (print_TypeDescriptor integer_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromInt
	  (case possible_datum of
	     | Some char_data -> stringToInt (trim_whitespace (string char_data))
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of 0 for " ^ (print_TypeDescriptor integer_sd) ^ "\n") in
	       0))


  op [X] internalize_PossibleElement_as_String (element : PossibleElement)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as String for " ^ (print_TypeDescriptor string_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromString 
	  (case possible_datum of
	     | Some char_data -> 
	       %% '<...> "abcd" <...>'  => "abcd", as opposed to " \"abcd\" ",
	       %% which would print back out as '<...> " "abcd" " <...>'
	       trim_whitespace_and_quotes (string char_data)
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of \"\" for " ^ (print_TypeDescriptor string_sd) ^ "\n") in
	       ""))


  op [X] internalize_PossibleElement_as_Char (element : PossibleElement)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Char for " ^ (print_TypeDescriptor char_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    case possible_datum of
      | Some char_data -> 
        %% '<...> "abcd" <...>'  => "abcd", as opposed to " \"abcd\" ",
        %% which would print back out as '<...> " "abcd" " <...>'
        let char_string = string char_data in
	(case ustring (trim_whitespace_and_quotes char_string) of
	   | 38 :: 35 ::           k :: 59 :: [] -> Some (magicCastFromChar (chr (                   k))) % &#k;
	   | 38 :: 35 ::      j :: k :: 59 :: [] -> Some (magicCastFromChar (chr (          10 * j + k))) % &#jk;
	   | 38 :: 35 :: i :: j :: k :: 59 :: [] -> Some (magicCastFromChar (chr (100 * i + 10 * j + k))) % &#ijk;
	   | _ -> 
	     %%% let _ = toScreen ((level_str level) ^ "Unrecognized character description: " ^ char_string ^ "\n") in
	     None)
      | None -> 
	None

  op internalize_PossibleElement_as_List : [X] PossibleElement * (List TypeDescriptor) * TypeDescriptorExpansionTable -> Option X 

  op [X] internalize_PossibleElement_as_List (element : PossibleElement,
                                              args    : List TypeDescriptor,
                                              table   : TypeDescriptorExpansionTable)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as List for " ^ (print_TypeDescriptor list_sd) ^ "\n") in
    let element_sd = head args in
    let data = reverse (foldl (fn (result, (possible_chardata,item)) ->
			   %%% let _ = toScreen ((level_str level) ^ "Seeking next list element: " ^ (print_TypeDescriptor element_sd) ^ "\n") in
			   case item of
			     | Element element ->
			       (case aux_internalize_Element (element, element_sd, table) of
				  | Some datum -> 
				    %%% let _ = toScreen ((level_str level) ^ "Found list element: " ^ (print_TypeDescriptor (hd args)) ^ "\n") in
				    datum:: result
				  | _ -> 
				    let _ = toScreen ("\nWarning: failure looking for list element: " ^ (print_TypeDescriptor element_sd) ^ "\n" ) in
				    result)
			     | _ -> 
			       case possible_chardata of
				 | Some ustr -> trim_whitespace (string ustr) :: result
				 | _ -> 
				   %%% let _ = toScreen ((level_str level) ^ "While looking for list element: " ^ (print_TypeDescriptor element_sd) ^ "\n" ^ "Ignoring: " ^ (string (print_Content_Item item)) ^ "\n") in
				   result)
		          []
			  element.content.items)
    in
      Some (magicCastFromList data)

  op [X] internalize_PossibleElement_ad_hoc (element : PossibleElement,
                                             base_sd : TypeDescriptor
                                               % qid     : QIdDescriptor,
                                               % args    : List TypeDescriptor,
                                               % table   : TypeDescriptorExpansionTable,
                                               )
    : Option X =
    %% Allow sophisticated users to hack with their own base types
    %% TODO: make fn names more regular
    Some (read_ad_hoc_string (base_sd, element.content))

  op [X] internalize_PossibleElement_as_Option (element   : PossibleElement,
                                                sd        : TypeDescriptor,
                                                table     : TypeDescriptorExpansionTable)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Option for " ^ (print_TypeDescriptor option_sd) ^ "\n") in
    let expanded_sd = expand_TypeDescriptor (sd, table) in
    magicCastToOption (Some (internalize_PossibleElement (element, sd, expanded_sd, table)))

  op [X] internalize_EmptyElemTag (etag        : EmptyElemTag,
                                   sd          : TypeDescriptor,
                                   expanded_sd : TypeDescriptor,
                                   table       : TypeDescriptorExpansionTable)
    : Option X =
    %%
    %%   type Content = {items   : List (Option CharData * Content_Item),
    %%                   trailer : Option CharData}
    %% 
    %%   type Content_Item = | Element   Element
    %%                       | Reference Reference
    %%                       | CDSect    CDSect
    %%                       | PI        PI
    %%                       | Comment   Comment
    %%
    %%% let _ = toScreen ((level_str level) ^ "Internalizing " ^ (string etag.name) ^ " as " ^ (print_TypeDescriptor sd) ^ " = " ^ (print_TypeDescriptor expanded_sd) ^ "\n") in
    case expanded_sd of
      | Product   field_sds    -> internalize_EmptyElemTag_as_product   (etag, sd, field_sds,    table) 
      | CoProduct optional_sds -> internalize_EmptyElemTag_as_coproduct (etag, sd, optional_sds, table)
      | Base      (qid, args)  -> internalize_EmptyElemTag_as_base_type (etag, sd, qid, args,    table)
      | Boolean                -> Some (magicCastFromBool false)
      | _ -> fail "unrecognized type"


  op [X] internalize_EmptyElemTag_as_product (etag       : EmptyElemTag,
                                              product_sd : TypeDescriptor,
                                              field_sds  : List (IdDescriptor * TypeDescriptor),
                                              table      : TypeDescriptorExpansionTable)
    : Option X =
    %% Note that datum_etags is a heterogenous list,
    %%  hence cannot be properly typed in metaslang,
    %%  hence the "magic" here.
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as product for " ^ (print_TypeDescriptor product_sd) ^ "\n") in
    if making_attributes_and_elements_explicit? field_sds then
      internalize_Attributes_and_Elements (Empty etag, product_sd, table)
    else
      %%% let _ = toScreen ((level_str level) ^ "No product\n") in
      magicCastFromOption (Some ())

  op [X] internalize_EmptyElemTag_as_coproduct (etag         : EmptyElemTag,
                                                coproduct_sd : TypeDescriptor,
                                                sd_options   : List (IdDescriptor * Option TypeDescriptor),
                                                table        : TypeDescriptorExpansionTable)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as coproduct for " ^ (print_TypeDescriptor coproduct_sd) ^ "\n") in
    case (findLeftmost (fn sd_option -> 
                          (case etag_type_attribute etag of
                             | Some str -> sd_option.1 = str
                             | _ -> false)
                         ||
                           ms_name_matches_xml_name? (sd_option.1, etag.name))
	       sd_options)
       of 
        | Some (_, Some matching_sd_option) -> 
 	  (case internalize_EmptyElemTag (etag,
					  matching_sd_option,
					  expand_TypeDescriptor (matching_sd_option, table),
					  table) 
	     of
	      | Some datum -> Some (magicMakeConstructor (convert_xml_name_to_ms_name etag.name, datum))
	      | _ ->
	        fail ("looking for coproduct etag: " ^ (print_TypeDescriptor coproduct_sd) ^ "\n" ))
	| _ ->
          None

  op [X] internalize_EmptyElemTag_as_base_type (etag    : EmptyElemTag,
                                                base_sd : TypeDescriptor,
                                                qid     : QIdDescriptor,
                                                args    : List TypeDescriptor,
                                                table   : TypeDescriptorExpansionTable)
    : Option X =
    case qid of
      %% Todo: maybe extract some of these from attributes?
      | ("Integer", "Int")    -> Some (magicCastFromInt    0)
      | ("String",  "String") -> Some (magicCastFromString "")
      | ("Char",    "Char")   -> None
      | ("List",    "List")   -> Some (magicCastFromList    [])
      | ("Option" , "Option") -> internalize_EmptyElemTag_as_Option (etag, head args, table)
      | _                     -> internalize_EmptyElemTag_ad_hoc    (etag, base_sd (* , qid, args, table, *))

  %% TODO: Implement this
  op internalize_EmptyElemTag_ad_hoc : [X] EmptyElemTag * TypeDescriptor (* * QIdDescriptor * (List TypeDescriptor) * TypeDescriptorExpansionTable *) -> Option X

  op [X] internalize_EmptyElemTag_as_Option (etag      : EmptyElemTag,
                                             sd        : TypeDescriptor,
                                             table     : TypeDescriptorExpansionTable)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as Option for " ^ (print_TypeDescriptor option_sd) ^ "\n") in
    let expanded_sd = expand_TypeDescriptor (sd, table) in
    magicCastToOption (Some (internalize_EmptyElemTag (etag, sd, expanded_sd, table)))

  op [Z] internalize_Attributes_and_Elements (element     : Element,
                                              sd          : TypeDescriptor,
                                              table       : TypeDescriptorExpansionTable)
    : Option Z =
    %% We know that expanded_sd matches:  Product [("attributes", _), ("elements", _)]

    %%% let _ = toScreen ("\nHere goes..." ^ (print_TypeDescriptor sd) ^ " \n") in
    case element of

      | Full elt ->
	(%%% let _ = (let desired = print_TypeDescriptor sd in
	 %%% 	  let given_type = (case (element_type_attribute elt) of
	 %%% 			      | Some str -> str
         %%%                          | _ -> "unspecified type")
	 %%% 	  in
	 %%% 	    toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from xml element named " ^ string elt.stag.name ^" of " ^ given_type ^ "\n"))
	 %%%  in
	 let attributes : Attributes = internalize_PossibleElement_Attributes (elt (* , sd, table, *)) in
	 let expanded_sd = expand_TypeDescriptor (sd, table) in
	 let elements_sd = (case expanded_sd of Product [("attributes", _), ("elements", xx)] -> xx) in
	 let expanded_sd : TypeDescriptor = expand_TypeDescriptor (elements_sd, table) in
	 case internalize_PossibleElement (elt, elements_sd, expanded_sd, table) of
	   | Some elements -> 
	     Some (magicCastFromAE {attributes = attributes,
				    elements   = elements})
	   | _ -> None)

      | Empty etag -> 
	%%% let _ = (let desired = print_TypeDescriptor sd in
	%%% 	 let given_type = (case (etag_type_attribute etag) of
	%%% 			     | Some str -> str
	%%% 			     | _ -> "unspecified type")
	%%% 	 in
	%%% 	   toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from empty xml element named " ^ string etag.name ^" of " ^ given_type ^ "\n"))
	%%% in
	let attributes : Attributes = internalize_EmptyElemTag_Attributes (etag (* , sd, table, *)) in
	Some (magicCastFromAE {attributes = attributes,
			       elements   = ()})

  op Magic.magicCastFromAE       : [E,X]  {attributes : Attributes, elements : E} -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp


  %% op internalize_EmptyElemTag_Attributes    : EmptyElemTag    * TypeDescriptor * TypeDescriptor * TypeDescriptorExpansionTable -> Attributes
  %% op internalize_PossibleElement_Attributes : PossibleElement * TypeDescriptor * TypeDescriptor * TypeDescriptorExpansionTable -> Attributes

  op internalize_EmptyElemTag_Attributes (etag  : EmptyElemTag
                                            % sd    : TypeDescriptor,
                                            % table : TypeDescriptorExpansionTable,
                                          )
    : Attributes =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing attributes for empty xml element " ^ (string etag.name) ^ " as " ^ (print_TypeDescriptor sd) ^ "\n") in
    internalize_ElementTag_Attributes (etag (* , sd, table *))

  op internalize_PossibleElement_Attributes (element : PossibleElement
                                               % sd      : TypeDescriptor,
                                               % table   : TypeDescriptorExpansionTable
                                               )
    : Attributes =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing attributes for xml element " ^ (string element.stag.name) ^ " as " ^ (print_TypeDescriptor sd) ^ "\n") in
    internalize_ElementTag_Attributes (element.stag (* , sd, table, *))

  op internalize_ElementTag_Attributes (tag   : ElementTag
                                          % sd    : TypeDescriptor,
                                          % table : TypeDescriptorExpansionTable
                                        )
    : Attributes =
    map (fn (attr : ElementAttribute) -> 
	 %% TODO: be smarter about typing -- not everything is CDATA 
	 (convert_xml_name_to_ms_name attr.name, CDATA (string attr.value.value))) 
        tag.attributes


endspec
