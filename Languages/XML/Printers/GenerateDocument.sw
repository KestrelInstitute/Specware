
XML qualifying spec 

  import /Languages/MetaSlang/Specs/Elaborate/SortDescriptor
  import ../XML_Sig
  import ../Utilities/XML_Unicode
  import Make_XML_Things
  import Magic

  sort SortExpansionTable = List (SortDescriptor * SortDescriptor)

  def indentation_chardata (vspacing, indent) : UChars =
    (repeat_char (UChar.newline, vspacing)) ^  (repeat_char (UChar.space, indent))

  def repeat_char (char : UChar, n : Nat) : UChars =
    if n <= 0 then
      []
    else 
      cons (char, repeat_char (char, n - 1))

  def fa (X) generate_Document (datum : X, 
				table as (main_entry as (main_sort, _) :: _) : SortExpansionTable) 
    : Document =
    let Base ((qualifier, main_id), _) = main_sort in
    make_Document (Some standard_XMLDecl,                     % first <?xml version="1.0"?>
		   [],
		   None,
		   [WhiteSpace [UChar.newline, UChar.newline]],   
		   generate_Element (main_id, datum, main_sort, table, 2, 0, true),
		   [])

 def expand_SortDescriptor (sd : SortDescriptor, table : SortExpansionTable) =
   let
      def aux sd =
	let possible_entry = find (fn (x,_) -> x = sd) table in
	case possible_entry of
	  | None -> sd
	  | Some (_, expansion) ->
	    case expansion of
	      | Base     _      -> aux expansion
	      | Subsort  (x, _) -> aux x
	      | Quotient (x, _) -> aux x
	      | _               -> expansion
   in
     aux sd

  def print_qid (qualifier, id) =
    if qualifier = id then
      id
    else if qualifier = "<unqualified>" then
      id
    else
      qualifier ^ "." ^ id	   

  def pp_sort_descriptor_for_xml_attribute (sd : SortDescriptor) : UString =
    let 
       def aux sd = 
	 case sd of
	   | Base (qid, args) ->
	     (case args of
		| []            -> (print_qid qid)
		| [arg]         -> (print_qid qid) ^ " " ^ (aux arg)
		| first :: rest -> ((print_qid qid) ^ " (" ^ 
				    (foldl (fn (arg, result) -> result ^ ", " ^ (aux arg)) 
				           (aux first)
					   rest) ^
				    ")"))
	   | CoProduct sd_options ->
		"[?? CoProduct ??]"
	   | Product fields ->
		"[?? Product ??]"
	   | Quotient _ ->
		"[?? Quotient ??]"
	   | Quotient _ ->
		"[?? Subset ??]"
	   | _ ->
		"[?? Mystery sort ??]"
    in
      ustring (aux sd)

  def fa (X) generate_Element (name     : String,
			       datum    : X,
			       sd       : SortDescriptor,
			       table    : SortExpansionTable,
			       vspacing : Nat,
			       indent   : Nat,
			       show_type? : Boolean)
    : Element =
    let pattern   = expand_SortDescriptor (sd, table) in
    let uname     = ustring name in
    let attributes = (if show_type? then
			let value = {qchar = UChar.apostrophe,
				     items = [NonRef (pp_sort_descriptor_for_xml_attribute sd)]}
			in
			let type_attr : ElementAttribute = {w1    = [UChar.space],
							    name  = ustring "type",
							    w2    = null_whitespace,
							    w3    = null_whitespace,
							    value = value}
			in
			  [type_attr]
		      else
			[])
    in
    case generate_content (datum, sd, pattern, table, vspacing, indent + 2) of
      | None ->
        Empty (make_EmptyElemTag (uname, attributes, []))
      | Some content ->
	let stag = make_STag (uname, attributes, null_whitespace) in
	let etag = make_ETag (uname,             null_whitespace) in
	Full {stag    = stag,
	      content = content,
	      etag    = etag}

  def fa (X) generate_content (datum      : X,
			       sd         : SortDescriptor,
			       sd_pattern : SortDescriptor,
			       table      : SortExpansionTable,
			       vspacing   : Nat,
			       indent     : Nat)
    : Option Content =
    case sd_pattern of
      | Product sd_fields ->
        %% Note that datum_elements is a heterogenous list,
        %%  hence cannot be properly typed in metaslang,
        %%  hence the "magic" here.
        let datum_elements = Magic.magicElements datum in
        let
          def aux (datum_elements, sd_fields, new_items) =
	    case (datum_elements, sd_fields) of

	      | ([], []) -> 
	        Some {items   = rev new_items,
		      trailer = Some (indentation_chardata (vspacing, indent - 2))}

	      | (datum_element :: datum_elements, (sd_field_name, sd_field_pattern) :: sd_fields) ->
	         aux (datum_elements,
		      sd_fields, 
		      cons ((Some (indentation_chardata (vspacing, indent)),
			     Element (generate_Element (sd_field_name, 
							datum_element, 
							sd_field_pattern, 
							table, 
							vspacing,
							indent,
							false))),
			    new_items))
	in
	  aux (datum_elements, sd_fields, [])

      | CoProduct sd_options ->
	let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	let possible_sd_entry = find (fn (x,_) -> constructor_name = x) sd_options in
	(case possible_sd_entry of
	  | None -> (toScreen ("Should never happen!"); None)
	  | Some (sd_constructor_name, possible_sd_sub_pattern) ->
	    case possible_sd_sub_pattern of
	      | None -> 
	        Some {items = [(Some (indentation_chardata (1 (* vspacing*), indent)),
				Element (Empty (make_EmptyElemTag (ustring constructor_name, [], []))))],
		      trailer = Some (indentation_chardata (1 (* vspacing *), indent - 2))}
	      | Some sd_sub_pattern ->
	        case sd_options of
		  | [("None", _), ("Some", _)]  -> 
		    generate_content (sub_datum,
				      sd,
				      expand_SortDescriptor (sd_sub_pattern, table),
				      table,
				      1, % vspacing,
				      indent)
		  | [("Some", _), ("None", _)]-> 
		    generate_content (sub_datum,
				      sd,
				      expand_SortDescriptor (sd_sub_pattern, table),
				      table,
				      1, % vspacing,
				      indent)
		  | _ ->
		    Some {items = [(Some (indentation_chardata (1 (* vspacing *), indent)),
				    Element (generate_Element (constructor_name,
							       sub_datum,
							       sd_sub_pattern,
							       table,
							       1, % vspacing,
							       indent,
							       false)))],
			  trailer = Some (indentation_chardata (1 (* vspacing *), indent - 2))})
	   
      | Base (qid, args) ->
	(case qid of
	  | ("String",  "String") ->
	    let string : String = Magic.magicCastToString datum in
	    indent_ustring (UString.double_quote ^ (ustring string) ^ UString.double_quote)

	  | ("Integer", "Integer") ->
	    let n = Magic.magicCastToInteger datum in
	    indent_ustring (ustring (Integer.toString n))

	  | ("List",    "List") ->
	    (let [element_sd] = args in
	     let new_element_sd = expand_SortDescriptor(element_sd, table) in
	     if new_element_sd = element_sd then
	       let items = Magic.magicCastToList datum in
	       Some {items = rev (foldl (fn (item, items) ->
					 cons (generate_Content_Item (item,
								      element_sd,
								      element_sd,
								      table,
								      2, % vspacing,
								      indent),
					       items))
				        []
					items),
		     trailer = Some (indentation_chardata (2 (* vspacing*), indent - 2))}
	     else
	       generate_content (datum,
				 sd,
				 Base (qid, [new_element_sd]),
				 table,
				 vspacing,
				 indent))

	  | ("Boolean", "Boolean") ->
	    let bool = Magic.magicCastToBoolean datum in
	    indent_ustring (ustring (if bool then "true" else "false"))

	  | ("Char",    "Char") ->
	    let char = Magic.magicCastToChar datum in
	    indent_ustring (ustring ("&#" ^ (Nat.toString (ord char)) ^";"))

	  | ("Option" , "Option") ->
	    (let [sub_sd] = args in
	     let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	     case constructor_name of
	       | "None" -> 
	          None
	       | _ ->
	         generate_content (sub_datum,
				   sd,
				   expand_SortDescriptor (sub_sd, table),
				   table,
				   vspacing,
				   indent))
	  | qid ->
	    indent_ustring (ustring ("?? Base: " ^ (print_qid qid) ^  " ?? ")))

      | _ ->
	indent_ustring (ustring ("?? unrecognized type  ?? "))




  def fa (X) generate_Content_Item (datum      : X,
				    sd         : SortDescriptor,
				    sd_pattern : SortDescriptor,
				    table      : SortExpansionTable,
				    vspacing   : Nat,
				    indent     : Nat)
    : Option CharData * Content_Item =
    case sd_pattern of
      | Product sd_fields ->
        (Some (indentation_chardata (vspacing, indent)),
	 Element (generate_Element ("item", datum, sd_pattern, table, vspacing, indent, false)))

      | CoProduct sd_options ->
	let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	let possible_sd_entry = find (fn (x,_) -> constructor_name = x) sd_options in
        (case possible_sd_entry of
	  | None -> (toScreen ("Should never happen!"); 
		     (Some (indentation_chardata (vspacing, indent)),
		      Element (Empty (make_EmptyElemTag (ustring constructor_name, 
							 [], 
							 [])))))
	  | Some (sd_constructor_name, possible_sd_sub_pattern) ->
	    case possible_sd_sub_pattern of
	      | None -> 
	        (Some (indentation_chardata (vspacing, indent)),
		 Element (Empty (make_EmptyElemTag (ustring constructor_name, [], []))))
	      | Some sd_sub_pattern ->
	        case sd_options of
		  | [("None", _), ("Some", _)]  -> 
		    generate_Content_Item (sub_datum,
					   sd,
					   expand_SortDescriptor (sd_sub_pattern, table),
					   table,
					   1, % vspacing,
					   indent)
		  | [("Some", _), ("None", _)]-> 
		    generate_Content_Item (sub_datum,
					   sd,
					   expand_SortDescriptor (sd_sub_pattern, table),
					   table,
					   1, % vspacing,
					   indent)
		  | _ ->
		    (Some (indentation_chardata (vspacing, indent)),
		     Element (generate_Element (constructor_name,
						sub_datum,
						sd_sub_pattern,
						table,
						1, % vspacing,
						indent,
						false))))

      | Base (qid, args) ->
	(case qid of
	  | ("String",  "String") ->
	    let string : String = Magic.magicCastToString datum in
	    indent_text_item (vspacing, indent, ustring string)

	  | ("Integer", "Integer") ->
	    let n = Magic.magicCastToInteger datum in
	    indent_text_item (vspacing, indent, ustring (Integer.toString n))

	  | ("Boolean", "Boolean") ->
	    let bool = Magic.magicCastToBoolean datum in
	    indent_text_item (vspacing, indent, ustring (if bool then "true" else "false"))

	  | ("Char",    "Char") ->
	    let char = Magic.magicCastToChar datum in
	    indent_text_item (vspacing, indent, ustring ("&#" ^ (Nat.toString (ord char)) ^";"))

	  | ("List",    "List") ->
	    (Some (indentation_chardata (vspacing, indent)),
	     Element (generate_Element ("list", datum, sd_pattern, table, vspacing, indent, true)))

	  | ("Option" , "Option") ->
	    (let [sub_sd] = args in
	     let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	     case constructor_name of
	       | "None" -> 
	         (Some (indentation_chardata (vspacing, indent)),
		  Element (Empty (make_EmptyElemTag (ustring constructor_name, [], []))))
	       | _ ->
		 generate_Content_Item (sub_datum,
					sd,
					expand_SortDescriptor (sub_sd, table),
					table,
					vspacing, 
					indent))

	  | qid ->
	    indent_text_item (vspacing, 
			      indent, 
			      ustring ("?? Base: " ^ (print_qid qid) ^  " ?? ")))

      | _ ->
	indent_text_item (vspacing, 
			  indent, 
			  ustring ("?? unrecognized type  ?? "))
	


  def indent_ustring (ustr : UString) : Option Content =
    Some {items   = [],
	  trailer = Some ((indentation_chardata (0, 1)) ^ 
			  ustr ^ 
			  (indentation_chardata (0, 1)))}

  def indent_text_item (vspacing : Nat, indent : Nat, ustr : UString) 
    : Option CharData * Content_Item =
    (Some ((indentation_chardata (vspacing, indent)) ^ ustr ^ [32]),
     Element (Empty (make_EmptyElemTag (UString.colon, [], []))))



endspec
