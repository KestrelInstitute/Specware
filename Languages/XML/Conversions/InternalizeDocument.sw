XML qualifying spec

  %% Throughout these routines we often have a value typed as "Option X",
  %% and cast created values using routines with names such as "castFromXXX"
  %% or "magicMakeXXX"
  %%
  %% Those casts map variously typed elements to the arbitrary type X,
  %% so we will need independent assurances we are not creating ill-typed
  %% structures.  For now those assurances are via hand-waving.

  import InternalizeAux

  def fa (X) aux_internalize_Document (document : Document,
				       sd       : SortDescriptor,
				       table    : SortDescriptorExpansionTable)
    : Option X =
    let expanded_sd : SortDescriptor = expand_SortDescriptor (sd, table) in
    internalize_Element (document.element, sd, expanded_sd, table, 0)
    
  %% we seem to need these op decls to avoid conflicts caused when 
  %% the type checker assumes various invocations are for monomophic versions,
  %% e.g. Option String -- [bug in type checker?]
  op internalize_Element         : fa (X) Element         * SortDescriptor * SortDescriptor * SortDescriptorExpansionTable * Nat -> Option X
  op internalize_PossibleElement : fa (X) PossibleElement * SortDescriptor * SortDescriptor * SortDescriptorExpansionTable * Nat -> Option X
  op internalize_EmptyElemTag    : fa (X) EmptyElemTag    * SortDescriptor * SortDescriptor * SortDescriptorExpansionTable * Nat -> Option X

  def fa (X) internalize_Element (element     : Element,
				  sd          : SortDescriptor,
				  expanded_sd : SortDescriptor,
				  table       : SortDescriptorExpansionTable,
				  level       : Nat)
    : Option X =
    case element of

      | Full elt ->
	%%% let _ = (let desired = print_SortDescriptor sd in
	%%% 	 let given_type = (case (element_type_attribute elt) of
	%%% 			     | Some str -> str
	%%% 			     | _ -> "unspecified type")
	%%% 	 in
	%%% 	   toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from xml element named " ^ string elt.stag.name ^" of " ^ given_type ^ "\n"))
	%%% in
	internalize_PossibleElement (elt, sd, expanded_sd, table, level + 1)

      | Empty etag -> 
	%%% let _ = (let desired = print_SortDescriptor sd in
	%%% 	let given_type = (case (etag_type_attribute etag) of
        %%% 			    | Some str -> str
        %%% 			    | _ -> "unspecified type")
        %%% 	in
        %%% 	  toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from empty xml element named " ^ string etag.name ^" of " ^ given_type ^ "\n"))
        %%% in
	internalize_EmptyElemTag (etag, sd, expanded_sd, table, level + 1)

  def fa (X) internalize_PossibleElement (element     : PossibleElement,
					  sd          : SortDescriptor,
					  expanded_sd : SortDescriptor,
					  table       : SortDescriptorExpansionTable,
					  level       : Nat)
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
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as " ^ (print_SortDescriptor sd) ^ "\n") in
    case expanded_sd of
      | Product   field_sds    -> internalize_PossibleElement_as_product   (element, sd, field_sds,    table, level + 1)
      | CoProduct optional_sds -> internalize_PossibleElement_as_coproduct (element, sd, optional_sds, table, level + 1)
      | Base      (qid, args)  -> internalize_PossibleElement_as_base_sort (element, sd, qid, args,    table, level + 1)
      | _ -> fail "unrecognized type"


  def fa (X) internalize_PossibleElement_as_product (element    : PossibleElement,
						     product_sd : SortDescriptor,
						     field_sds  : List (IdDescriptor * SortDescriptor),
						     table      : SortDescriptorExpansionTable,
						     level      : Nat)
    : Option X =
    %% Note that datum_elements is a heterogenous list,
    %%  hence cannot be properly typed in metaslang,
    %%  hence there is "magic" here.
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as product for " ^ (print_SortDescriptor product_sd) ^ "\n") in
    case field_sds of
      | [("attributes", _), ("elements", _)] -> 
        internalize_Attributes_and_Elements (Full element, product_sd, table, level + 1)
      | _ ->
        let possible_magic_values =
            foldl (fn ((field_name, field_sd), possible_magic_values) ->
		   case possible_magic_values of
		     | None -> None
		     | Some magic_values ->
		       %%% let _ = toScreen ((level_str level) ^ "First, seeking field named " ^ field_name ^ " to construct " ^ (print_SortDescriptor field_sd) ^ "\n") in
		       case (case find_matching_sub_element (element, field_name, level + 1) of
			       | Some matching_elt ->
			         (%%% let _ = toScreen ((level_str level) ^ "Second, internalizing matching xml element named " ^ (string matching_elt.stag.name) ^ " as " ^ (print_SortDescriptor field_sd) ^ "\n") in
				  internalize_PossibleElement (matching_elt, field_sd, field_sd, table, level + 1))
			       | None -> 
				 case default_field_value (element, field_sd, table, level + 1) of
				  | Some field_value  -> Some field_value
				  | None -> 
				    let expanded_field_sd = expand_SortDescriptor (field_sd, table) in
				    default_field_value (element, field_sd, table, level + 1))
			 of 
                          %% magic_values is a list over some unknown generic type
			  %% In practice, each field_value has its own independent type, 
			  %% but we have cast all of them to that generic type.
			  %% Thus we must be very careful what we do with magic_value:
			  %% operations such as cons/hd/tl/rev are ok.
			  | Some field_value  -> Some (cons (field_value, magic_values))
			  | None -> None)
	          (Some [])
		  field_sds
	in
	  case possible_magic_values of
	    | Some magic_values ->
	      %%% let _ = toScreen ((level_str level) ^ "Found product\n") in
	      %% magicMakeProduct restructures the implementation of magic_values from a list to a product 
	      %% See casting note at start of file.
	      Some (Magic.magicMakeProduct (rev magic_values))
	    | _ -> None


  def find_matching_sub_element (element    : PossibleElement,
				 field_name : IdDescriptor,
				 level      : Nat)
    : Option PossibleElement =
    foldl (fn ((_, item), result) ->
	   case result of
	     | Some _ -> result
	     | _ ->
	       case item of
		 | Element (Full elt) -> 
		   if field_name = string elt.stag.name then
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


  def fa (X) default_field_value (element    : PossibleElement,
				  field_sd   : SortDescriptor, 
				  table      : SortDescriptorExpansionTable,
				  level      : Nat) 
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Could not find field " ^ field_name ^ "\n") in
    case field_sd of % don't chase expansion, as that would expand list and option
      | Base (("Boolean", "Boolean"),       []) -> 
        %%% let _ = toScreen ((level_str level) ^ "Using default value of false for " ^ (print_SortDescriptor field_sd) ^ "\n") in
	Some (magicCastFromBoolean false)
      | Base (("Nat", "Nat"),       []) -> 
	%%% let _ = toScreen ((level_str level) ^ "Using default value of 0 for "     ^ (print_SortDescriptor field_sd) ^ "\n") in
	Some (magicCastFromInteger 0)
      | Base (("String", "String"), []) -> 
	%%% let _ = toScreen ((level_str level) ^ "Using default value of \"\" for "  ^ (print_SortDescriptor field_sd) ^ "\n") in
	Some (magicCastFromString "")
      | Base (("List", "List"), args) -> 
	Some (case internalize_PossibleElement_as_List (element, args, table, level + 1) of
		| Some XX -> magicCastFromList XX
		| _       -> magicCastFromList [])
      | Base (("Option", "Option"), _) -> 
	Some (magicCastFromOption None)
      | _ -> 
        %% todo: add hook for user defined base sorts
	None

  def fa (X) internalize_PossibleElement_as_coproduct (element      : PossibleElement,
						       coproduct_sd : SortDescriptor,
						       sd_options   : List (IdDescriptor * Option SortDescriptor),
						       table        : SortDescriptorExpansionTable,
						       level        : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as coproduct for " ^ (print_SortDescriptor coproduct_sd) ^ "\n") in
    (let element_name = string element.stag.name in
	 case (find (fn sd_option -> 
		     (case element_type_attribute element of
			| Some str -> sd_option.1 = str
			| _ -> false)
			or
			(sd_option.1 = element_name))
	            sd_options)
	   of
	   | Some (_, Some matching_sd_option) -> 
	      (case internalize_PossibleElement (element,
						 coproduct_sd,
						 expand_SortDescriptor (matching_sd_option, table),
						 table,
						 level + 1) 
		 of
		 | Some datum -> Some (magicMakeConstructor (element_name, datum))
		 | _ ->
		   fail ("looking for coproduct element: " ^ (print_SortDescriptor coproduct_sd) ^ "\n" ))
           | _ ->
	     case element.content.items of
	       | [(_, Element (Full elt))] -> 
                 %% looking at "<n> <baz> ,,, </baz>  </n>" while expecting a coproduct with possible constructor baz
   	         %% which can happen while looking at "<foo> <1> ... </1> .... <n> <baz> ,,, </baz> </n> ... </foo>"
	         %% ? also check for name to be "1" "2" etc.? (or would that make explicitly named products fail?)
	         internalize_PossibleElement (elt, coproduct_sd, coproduct_sd, table, level + 1)
	       | _ -> 
	         fail ("decoding CoProduct: XML datum named " ^ element_name ^ " doesn't match any of " ^ 
		       (foldl (fn ((name, _), result) ->
			       case result of
				 | "" -> name
				 | _ -> result ^ ", " ^ name)
			      ""
			      sd_options)
		       ^ " coproduct options"))

  def fa (X) internalize_PossibleElement_as_base_sort (element : PossibleElement,
						       base_sd : SortDescriptor,
						       qid     : QIdDescriptor,
						       args    : List SortDescriptor,
						       table   : SortDescriptorExpansionTable,
						       level   : Nat)
    : Option X =
    case qid of
      | ("Boolean", "Boolean") -> internalize_PossibleElement_as_Boolean (element, level)
      | ("Integer", "Integer") -> internalize_PossibleElement_as_Integer (element, level)
      | ("String",  "String")  -> internalize_PossibleElement_as_String  (element, level)
      | ("Char",    "Char")    -> internalize_PossibleElement_as_Char    (element, level)
      | ("List",    "List")    -> internalize_PossibleElement_as_List    (element, args,    table, level)
      | ("Option" , "Option")  -> internalize_PossibleElement_as_Option  (element, hd args, table, level)
      | _                      -> internalize_PossibleElement_ad_hoc     (element, base_sd, (* qid, args, table, *) level)

  def fa (X) internalize_PossibleElement_as_Boolean (element : PossibleElement,
						     level   : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Boolean for " ^ (print_SortDescriptor boolean_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromBoolean 
	  (case possible_datum of
	     | Some char_data -> 
	       (case string char_data of
		  | "true"  -> true
		  | "false" -> false)
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of false for " ^ (print_SortDescriptor boolean_sd) ^ "\n") in
	       false))


  def fa (X) internalize_PossibleElement_as_Integer (element : PossibleElement,
						     level   : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Integer for " ^ (print_SortDescriptor integer_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromInteger 
	  (case possible_datum of
	     | Some char_data -> stringToInt (trim_whitespace (string char_data))
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of 0 for " ^ (print_SortDescriptor integer_sd) ^ "\n") in
	       0))


  def fa (X) internalize_PossibleElement_as_String (element : PossibleElement,
						    level   : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as String for " ^ (print_SortDescriptor string_sd) ^ "\n") in
    let possible_datum = element.content.trailer in
    Some (magicCastFromString 
	  (case possible_datum of
	     | Some char_data -> 
	       %% '<...> "abcd" <...>'  => "abcd", as opposed to " \"abcd\" ",
	       %% which would print back out as '<...> " "abcd" " <...>'
	       trim_whitespace_and_quotes (string char_data)
	     | None -> 
	       %%% let _ = toScreen ((level_str level) ^ "Using default value of \"\" for " ^ (print_SortDescriptor string_sd) ^ "\n") in
	       ""))


  def fa (X) internalize_PossibleElement_as_Char (element : PossibleElement,
						  level   : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Char for " ^ (print_SortDescriptor char_sd) ^ "\n") in
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

  op internalize_PossibleElement_as_List : fa (X) PossibleElement * (List SortDescriptor) * SortDescriptorExpansionTable * Nat -> Option X 

  def fa (X) internalize_PossibleElement_as_List (element : PossibleElement,
						  args    : List SortDescriptor,
						  table   : SortDescriptorExpansionTable,
						  level   : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as List for " ^ (print_SortDescriptor list_sd) ^ "\n") in
    let element_sd = hd args in
    let expanded_sd = expand_SortDescriptor (element_sd, table) in
    let data = rev (foldl (fn ((possible_chardata,item), result) ->
			   %%% let _ = toScreen ((level_str level) ^ "Seeking next list element: " ^ (print_SortDescriptor element_sd) ^ "\n") in
			   case item of
			     | Element element ->
			       (case internalize_Element (element, element_sd, expanded_sd, table, level + 1) of
				  | Some datum -> 
				    %%% let _ = toScreen ((level_str level) ^ "Found list element: " ^ (print_SortDescriptor (hd args)) ^ "\n") in
				    cons (datum, result)
				  | _ -> 
				    let _ = toScreen ((level_str level) ^ "Warning: failure looking for list element: " ^ (print_SortDescriptor element_sd) ^ "\n" ) in
				    result)
			     | _ -> 
			       case possible_chardata of
				 | Some ustr -> cons (trim_whitespace (string ustr), result)
				 | _ -> 
				   %%% let _ = toScreen ((level_str level) ^ "While looking for list element: " ^ (print_SortDescriptor element_sd) ^ "\n" ^ "Ignoring: " ^ (string (print_Content_Item item)) ^ "\n") in
				   result)
		          []
			  element.content.items)
    in
      Some (magicCastFromList data)

  def fa (X) internalize_PossibleElement_ad_hoc (element : PossibleElement,
						 base_sd : SortDescriptor,
						 % qid     : QIdDescriptor,
						 % args    : List SortDescriptor,
						 % table   : SortDescriptorExpansionTable,
						 level   : Nat)
    : Option X =
    %% Allow sophisticated users to hack with their own base types
    %% TODO: make fn names more regular
    Some (read_ad_hoc_string (base_sd, element.content))

  def fa (X) internalize_PossibleElement_as_Option (element   : PossibleElement,
						    sd        : SortDescriptor,
						    table     : SortDescriptorExpansionTable,
						    level     : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing xml element " ^ (string element.stag.name) ^ " as Option for " ^ (print_SortDescriptor option_sd) ^ "\n") in
    let expanded_sd = expand_SortDescriptor (sd, table) in
    magicCastToOption (Some (internalize_PossibleElement (element, sd, expanded_sd, table, level + 1)))

  def fa (X) internalize_EmptyElemTag (etag        : EmptyElemTag,
				       sd          : SortDescriptor,
				       expanded_sd : SortDescriptor,
				       table       : SortDescriptorExpansionTable,
				       level       : Nat)
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
    %%% let _ = toScreen ((level_str level) ^ "Internalizing " ^ (string etag.name) ^ " as " ^ (print_SortDescriptor sd) ^ " = " ^ (print_SortDescriptor expanded_sd) ^ "\n") in
    case expanded_sd of
      | Product   field_sds    -> internalize_EmptyElemTag_as_product   (etag, sd, field_sds,    table, level) 
      | CoProduct optional_sds -> internalize_EmptyElemTag_as_coproduct (etag, sd, optional_sds, table, level)
      | Base      (qid, args)  -> internalize_EmptyElemTag_as_base_sort (etag, sd, qid, args,    table, level)
      | _ -> fail "unrecognized type"


  def fa (X) internalize_EmptyElemTag_as_product (etag       : EmptyElemTag,
						  product_sd : SortDescriptor,
						  field_sds  : List (IdDescriptor * SortDescriptor),
						  table      : SortDescriptorExpansionTable,
						  level      : Nat)
    : Option X =
    %% Note that datum_etags is a heterogenous list,
    %%  hence cannot be properly typed in metaslang,
    %%  hence the "magic" here.
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as product for " ^ (print_SortDescriptor product_sd) ^ "\n") in
    case field_sds of
      | [("attributes", _), ("elements", _)] -> 
        internalize_Attributes_and_Elements (Empty etag, product_sd, table, level + 1)
      | _ ->
        %%% let _ = toScreen ((level_str level) ^ "No product\n") in
        magicCastFromOption (Some ())

  def fa (X) internalize_EmptyElemTag_as_coproduct (etag         : EmptyElemTag,
						    coproduct_sd : SortDescriptor,
						    sd_options   : List (IdDescriptor * Option SortDescriptor),
						    table        : SortDescriptorExpansionTable,
						    level        : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as coproduct for " ^ (print_SortDescriptor coproduct_sd) ^ "\n") in
    let etag_name = string etag.name in
    case (find (fn sd_option -> 
		(case etag_type_attribute etag of
		   | Some str -> sd_option.1 = str
		   | _ -> false)
		   or
		   (sd_option.1 = etag_name))
	       sd_options)
       of 
        | Some (_, Some matching_sd_option) -> 
 	  (case internalize_EmptyElemTag (etag,
					  matching_sd_option,
					  expand_SortDescriptor (matching_sd_option, table),
					  table,
					  level + 1) 
	     of
	      | Some datum -> Some (magicMakeConstructor (etag_name, datum))
	      | _ ->
	        fail ("looking for coproduct etag: " ^ (print_SortDescriptor coproduct_sd) ^ "\n" ))
	| _ ->
          None

  def fa (X) internalize_EmptyElemTag_as_base_sort (etag    : EmptyElemTag,
						    base_sd : SortDescriptor,
						    qid     : QIdDescriptor,
						    args    : List SortDescriptor,
						    table   : SortDescriptorExpansionTable,
						    level   : Nat)
    : Option X =
    case qid of
      %% Todo: maybe extract some of these from attributes?
      | ("Boolean", "Boolean") -> Some (magicCastFromBoolean false)
      | ("Integer", "Integer") -> Some (magicCastFromInteger 0)
      | ("String",  "String")  -> Some (magicCastFromString  "")
      | ("Char",    "Char")    -> None
      | ("List",    "List")    -> Some (magicCastFromList    [])
      | ("Option" , "Option")  -> internalize_EmptyElemTag_as_Option (etag, hd args, table, level + 1)
      | _                      -> internalize_EmptyElemTag_ad_hoc    (etag, base_sd, (* qid, args, table, *) level + 1)

  %% TODO: Implement this
  op internalize_EmptyElemTag_ad_hoc : fa (X) EmptyElemTag * SortDescriptor (* * QIdDescriptor * (List SortDescriptor) * SortDescriptorExpansionTable *) * Nat -> Option X

  def fa (X) internalize_EmptyElemTag_as_Option (etag      : EmptyElemTag,
						 sd        : SortDescriptor,
						 table     : SortDescriptorExpansionTable,
						 level     : Nat)
    : Option X =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing empty xml element " ^ (string etag.name) ^ " as Option for " ^ (print_SortDescriptor option_sd) ^ "\n") in
    let expanded_sd = expand_SortDescriptor (sd, table) in
    magicCastToOption (Some (internalize_EmptyElemTag (etag, sd, expanded_sd, table, level + 1)))

  op internalize_Attributes_and_Elements : fa (Z) Element * SortDescriptor * SortDescriptorExpansionTable * Nat -> Option Z

  def fa (Z) internalize_Attributes_and_Elements (element     : Element,
						  sd          : SortDescriptor,
						  table       : SortDescriptorExpansionTable,
						  level       : Nat)
    : Option Z =
    %% We know that expanded_sd matches:  Product [("attributes", _), ("elements", _)]

    %%% let _ = toScreen ("\nHere goes..." ^ (print_SortDescriptor sd) ^ " \n") in
    case element of

      | Full elt ->
	(%%% let _ = (let desired = print_SortDescriptor sd in
	 %%% 	  let given_type = (case (element_type_attribute elt) of
	 %%% 			      | Some str -> str
         %%%                          | _ -> "unspecified type")
	 %%% 	  in
	 %%% 	    toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from xml element named " ^ string elt.stag.name ^" of " ^ given_type ^ "\n"))
	 %%%  in
	 let attributes : Attributes = internalize_PossibleElement_Attributes (elt, (* sd, table, *) level + 1) in
	 let expanded_sd = expand_SortDescriptor (sd, table) in
	 let elements_sd = (case expanded_sd of Product [("attributes", _), ("elements", xx)] -> xx) in
	 let expanded_sd : SortDescriptor = expand_SortDescriptor (elements_sd, table) in
	 case internalize_PossibleElement (elt, elements_sd, expanded_sd, table, level + 1) of
	   | Some elements -> 
	     Some (magicCastFromAE {attributes = attributes,
				    elements   = elements})
	   | _ -> None)

      | Empty etag -> 
	%%% let _ = (let desired = print_SortDescriptor sd in
	%%% 	 let given_type = (case (etag_type_attribute etag) of
	%%% 			     | Some str -> str
	%%% 			     | _ -> "unspecified type")
	%%% 	 in
	%%% 	   toScreen ((level_str level) ^ "Seeking " ^ desired ^ " from empty xml element named " ^ string etag.name ^" of " ^ given_type ^ "\n"))
	%%% in
	let attributes : Attributes = internalize_EmptyElemTag_Attributes (etag, (* sd, table, *) level + 1) in
	Some (magicCastFromAE {attributes = attributes,
			       elements   = ()})

  op Magic.magicCastFromAE       : fa (E,X)  {attributes : Attributes, elements : E} -> X   % see /Languages/XML/Handwritten/Lisp/Magic.lisp


  %% op internalize_EmptyElemTag_Attributes    : EmptyElemTag    * SortDescriptor * SortDescriptor * SortDescriptorExpansionTable * Nat -> Attributes
  %% op internalize_PossibleElement_Attributes : PossibleElement * SortDescriptor * SortDescriptor * SortDescriptorExpansionTable * Nat -> Attributes

  def internalize_EmptyElemTag_Attributes (etag  : EmptyElemTag,
					   % sd    : SortDescriptor,
					   % table : SortDescriptorExpansionTable,
					   level : Nat)
    : Attributes =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing attributes for empty xml element " ^ (string etag.name) ^ " as " ^ (print_SortDescriptor sd) ^ "\n") in
    internalize_ElementTag_Attributes (etag, (* sd, table, *) level + 1)

  def internalize_PossibleElement_Attributes (element : PossibleElement,
					      % sd      : SortDescriptor,
					      % table   : SortDescriptorExpansionTable,
					      level   : Nat)
    : Attributes =
    %%% let _ = toScreen ((level_str level) ^ "Internalizing attributes for xml element " ^ (string element.stag.name) ^ " as " ^ (print_SortDescriptor sd) ^ "\n") in
    internalize_ElementTag_Attributes (element.stag, (* sd, table, *) level + 1)

  def internalize_ElementTag_Attributes (tag   : ElementTag,
					 % sd    : SortDescriptor,
					 % table : SortDescriptorExpansionTable,
					 level : Nat)
    : Attributes =
    map (fn (attr : ElementAttribute) -> 
	 %% TODO: be smarter about typing -- not everything is CDATA 
	 (string attr.name, CDATA (string attr.value.value))) 
        tag.attributes


endspec
