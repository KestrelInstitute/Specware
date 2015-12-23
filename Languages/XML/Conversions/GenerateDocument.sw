(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

XML qualifying spec

  import /Languages/MetaSlang/Specs/Elaborate/TypeDescriptor
  import ../XML_Sig
  import ../Utilities/XML_Unicode
  import Make_XML_Things
  import Magic
  import /Library/Legacy/Utilities/System

  def convert_ms_name_to_xml_name (ms_name : String) : UString =
    %% coordinate with convert_xml_name_to_ms_name in InternalizeAux.sw
    %% they should be converses
    let tentative_xml_name = ustring ms_name in
    let reversed_xml_name = reverse tentative_xml_name in
    %% "?" is not allowed in an xml name, and "-" is not allowed in a ms name,
    %% so we convert ms "foo?" to xml "foo-p"
    case reversed_xml_name of
      | 63 (* ? *) :: tail ->
        reverse (Cons (112 (* p *), Cons (45 (* - *), tail)))
      | _ -> 
	tentative_xml_name

  def quote_special_chars (uchars : UChars) : UChars =
    case uchars of
      | [] -> []
      | 38 :: tail (* & *) -> (* &apos; *)
        %      &         a         p         o	       s        ;
        38 :: 97 :: 112 :: 111 :: 115 :: 59 :: quote_special_chars tail
      | 60 :: tail (* < *) -> (* &lt; *)
        %      &          l         t        ;			
        38 :: 108 :: 116 :: 59 :: quote_special_chars tail
      | char :: tail ->
        char :: quote_special_chars tail


  def indentation_chardata (vspacing, indent) : UChars =
    (repeat_char (UChar.newline, vspacing)) ^  (repeat_char (UChar.space, indent))

  def repeat_char (char : UChar, n : Nat) : UChars =
    if n <= 0 then
      []
    else
      char :: repeat_char (char, n - 1)

  def [X] generate_Document (datum : X,
                             table as (main_entry as (main_type, _) :: _) : TypeDescriptorExpansionTable)
    : Document =
    let Base ((qualifier, main_id), _) = main_type in
    let dtd = {internal = None,
	       external = None,
	       entities = []}
    in
    make_Document (Some standard_XMLDecl,                     % first <?xml version="1.0"?>
		   [],
		   dtd,
		   [WhiteSpace [UChar.newline, UChar.newline]],
		   generate_Element (main_id, datum, main_type, table, 2, 0, true),
		   [])

  def print_qid (qualifier, id) =
    if qualifier = id then
      id
    else if qualifier = "<unqualified>" then
      id
    else
      qualifier ^ "." ^ id

  def pp_type_descriptor_for_xml_attribute (sd : TypeDescriptor) : UString =
    let
       def aux sd =
	 case sd of
	   | Boolean -> "Bool"
	   | Base (qid, args) ->
	     (case args of
		| []            -> (print_qid qid)
		| [arg]         -> (print_qid qid) ^ " " ^ (aux arg)
		| first :: rest -> ((print_qid qid) ^ " (" ^
				    (foldl (fn (result, arg) -> result ^ ", " ^ (aux arg))
				           (aux first)
					   rest) ^
				    ")"))
	   | CoProduct sd_options ->
		"[?? CoProduct ??]"
	   | Product fields ->
		"[?? Product ??]"
	   | Quotient _ ->
		"[?? Quotient ??]"
	   | Subtype _ ->
		"[?? Subtype ??]"
	   | _ ->
		"[?? Mystery type ??]"
    in
      ustring (aux sd)

  def [X] generate_Element (name       : String,
                            datum      : X,
                            sd         : TypeDescriptor,
                            table      : TypeDescriptorExpansionTable,
                            vspacing   : Nat,
                            indent     : Nat,
                            show_type? : Bool)
    : Element =
    let pattern   = expand_TypeDescriptor (sd, table) in
    let uname     = convert_ms_name_to_xml_name name in
    let attributes = (if show_type? then
			let value = {qchar = UChar.apostrophe,
				     items = [NonRef (pp_type_descriptor_for_xml_attribute sd)],
				     value = []} % todo
			in
			let type_attr : ElementAttribute = {w1    = [UChar.space],
							    name  = convert_ms_name_to_xml_name "type",
							    w2    = null_whitespace,
							    w3    = null_whitespace,
							    value = value}
			in
			  [type_attr]
		      else
			[])
    in
    case generate_content (datum, (* sd, *) pattern, table, vspacing, indent + 2) of
      | None ->
        Empty (make_EmptyElemTag (uname, attributes, []))
      | Some content ->
	let stag = make_STag (uname, attributes, null_whitespace) in
	let etag = make_ETag (uname,             null_whitespace) in
	Full {stag    = stag,
	      content = content,
	      etag    = etag}

  def [X] generate_content (datum      : X,
                            sd_pattern : TypeDescriptor,
                            table      : TypeDescriptorExpansionTable,
                            vspacing   : Nat,
                            indent     : Nat)
    : Option Content =
    case sd_pattern of
      | Product sd_fields ->
        %% Note that datum_elements is a heterogenous list,
        %%  hence cannot be properly typed in metaslang,
        %%  hence the "magic" here.
        let datum_elements = Magic.magicElements (length sd_fields, datum) in
        let
          def aux (datum_elements, sd_fields, new_items) =
	    case (datum_elements, sd_fields) of

	      | ([], []) ->
	        Some {items   = reverse new_items,
		      trailer = Some (indentation_chardata (vspacing, indent - 2))}

	      | (datum_element :: datum_elements, (sd_field_name, sd_field_pattern) :: sd_fields) ->
	         aux (datum_elements,
		      sd_fields,
		      Cons ((Some (indentation_chardata (vspacing, indent)),
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
	let possible_sd_entry = findLeftmost (fn (x,_) -> constructor_name = x) sd_options in
	(case possible_sd_entry of
	  | None -> (fail ("Should never happen!"); None)
	  | Some (sd_constructor_name, possible_sd_sub_pattern) ->
	    case possible_sd_sub_pattern of
	      | None ->
	        Some {items = [(Some (indentation_chardata (1 (* vspacing*), indent)),
				Element (Empty (make_EmptyElemTag (convert_ms_name_to_xml_name constructor_name, [], []))))],
		      trailer = Some (indentation_chardata (1 (* vspacing *), indent - 2))}
	      | Some sd_sub_pattern ->
	        case sd_options of
		  | [("None", _), ("Some", _)]  ->
		    generate_content (sub_datum,
				      expand_TypeDescriptor (sd_sub_pattern, table),
				      table,
				      1, % vspacing,
				      indent)
		  | [("Some", _), ("None", _)]->
		    generate_content (sub_datum,
				      expand_TypeDescriptor (sd_sub_pattern, table),
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

      | Boolean -> 	   
	let bool = Magic.magicCastToBool datum in
	indent_ustring (ustring (if bool then "true" else "false"))
      | Base (qid, args) ->
	(case qid of
	  | ("String",  "String") ->
	    let string : String = Magic.magicCastToString datum in
	    indent_ustring (UString.double_quote ^ (quote_special_chars (ustring string)) ^ UString.double_quote)

	  | ("Integer", "Int") ->
	    let n = Magic.magicCastToInt datum in
	    indent_ustring (ustring (Integer.show n))

	  | ("List",    "List") ->
	    (let [element_sd] = args in
	     let expanded_element_sd = expand_TypeDescriptor(element_sd, table) in
	     let items = Magic.magicCastToList datum in
	     Some {items = reverse (foldl (fn (items, item) ->
                                             Cons (generate_Content_Item (item,
                                                                          element_sd,
                                                                          expanded_element_sd,
                                                                          table,
                                                                          1, % vspacing,
                                                                          indent),
                                                   items))
                                      []
                                      items),
		   trailer = Some (indentation_chardata (2 (* vspacing*), indent - 2))})
	  | ("Bool", "Bool") ->
	    let bool = Magic.magicCastToBool datum in
	    indent_ustring (ustring (if bool then "true" else "false"))

	  | ("Char",    "Char") ->
	    let char = Magic.magicCastToChar datum in
	    indent_ustring (ustring ("&#" ^ (Nat.show (ord char)) ^";"))

	  | ("Option" , "Option") ->
	    (let [sub_sd] = args in
	     let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	     case constructor_name of
	       | "None" ->
	          None
	       | _ ->
	         generate_content (sub_datum,
				   expand_TypeDescriptor (sub_sd, table),
				   table,
				   vspacing,
				   indent))
	  | qid ->
	    let str = write_ad_hoc_string (sd_pattern, datum) in
	    indent_ustring (quote_special_chars (ustring str)))

      | _ ->
	indent_ustring (ustring ("?? unrecognized type  ?? "))

  op write_ad_hoc_string : [X] TypeDescriptor * X -> String

  def [X] generate_Content_Item (datum      : X,
                                 sd         : TypeDescriptor,
                                 sd_pattern : TypeDescriptor,
                                 table      : TypeDescriptorExpansionTable,
                                 vspacing   : Nat,
                                 indent     : Nat)
    : Option CharData * Content_Item =
    case sd_pattern of
      | Product sd_fields ->
        (let raw_item_name = 
	     case sd of
	       | Boolean -> "Bool"
	       | Base ((q,id), []) -> ((if q = "<unqualified>" then "" else q ^ ".") ^ id)
	       | _ -> "item"
	 in
	 let (item_name, show_type?) = 
	     if xml_prefix? (convert_ms_name_to_xml_name raw_item_name) then
	       ("_" ^ raw_item_name, true)
	     else
	       (raw_item_name, false)
	 in
	   (Some (indentation_chardata (vspacing, indent)),
	    Element (generate_Element (item_name, datum, sd, table, vspacing, indent, show_type?))))

      | CoProduct sd_options ->
	let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	let possible_sd_entry = findLeftmost (fn (x,_) -> constructor_name = x) sd_options in
        (case possible_sd_entry of
	  | None -> (fail ("Should never happen!");
		     (Some (indentation_chardata (vspacing, indent)),
		      Element (Empty (make_EmptyElemTag (convert_ms_name_to_xml_name constructor_name,
							 [],
							 [])))))
	  | Some (sd_constructor_name, possible_sd_sub_pattern) ->
	    case possible_sd_sub_pattern of
	      | None ->
	        (Some (indentation_chardata (vspacing, indent)),
		 Element (Empty (make_EmptyElemTag (convert_ms_name_to_xml_name constructor_name, [], []))))
	      | Some sd_sub_pattern ->
	        case sd_options of
		  | [("None", _), ("Some", _)]  ->
		    generate_Content_Item (sub_datum,
					   sd_sub_pattern,
					   expand_TypeDescriptor (sd_sub_pattern, table),
					   table,
					   1, % vspacing,
					   indent)
		  | [("Some", _), ("None", _)]->
		    generate_Content_Item (sub_datum,
					   sd_sub_pattern,
					   expand_TypeDescriptor (sd_sub_pattern, table),
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

      | Boolean -> 	   
	let bool = Magic.magicCastToBool datum in
	indent_text_item (vspacing, indent, ustring (if bool then "true" else "false"))

      | Base (qid, args) ->
	(case qid of
	  | ("String",  "String") ->
	    let string : String = Magic.magicCastToString datum in
	    indent_text_item (vspacing, indent, quote_special_chars (ustring string))

	  | ("Integer", "Int") ->
	    let n = Magic.magicCastToInt datum in
	    indent_text_item (vspacing, indent, ustring (Integer.show n))

	  | ("Bool", "Bool") ->
	    let bool = Magic.magicCastToBool datum in
	    indent_text_item (vspacing, indent, ustring (if bool then "true" else "false"))

	  | ("Char",    "Char") ->
	    let char = Magic.magicCastToChar datum in
	    indent_text_item (vspacing, indent, ustring ("&#" ^ (Nat.show (ord char)) ^";"))

	  | ("List",    "List") ->
	    (Some (indentation_chardata (vspacing, indent)),
	     Element (generate_Element ("list", datum, sd_pattern, table, vspacing, indent, true)))

	  | ("Option" , "Option") ->
	    (let [sub_sd] = args in
	     let (constructor_name, sub_datum) = Magic.magicConstructorNameAndValue datum in
	     case constructor_name of
	       | "None" ->
	         (Some (indentation_chardata (vspacing, indent)),
		  Element (Empty (make_EmptyElemTag (convert_ms_name_to_xml_name constructor_name, [], []))))
	       | _ ->
		 generate_Content_Item (sub_datum,
					sub_sd,
					expand_TypeDescriptor (sub_sd, table),
					table,
					vspacing,
					indent))

	  | qid ->
	    let str = write_ad_hoc_string (sd_pattern, datum) in
	    indent_text_item (vspacing,
			      indent,
			      quote_special_chars (ustring str)))

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
