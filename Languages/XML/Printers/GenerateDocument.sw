
XML qualifying spec 

  import /Languages/MetaSlang/Specs/Elaborate/SortDescriptor
  import ../XML_Sig
  import ../Utilities/XML_Unicode
  import Make_XML_Things
  import Magic

  op standard_XMLDecl : XMLDecl 

  sort SortExpansionTable = List (SortDescriptor * SortDescriptor)

  def null_whitespace : WhiteSpace = []

  def indentation_chardata (n) : UChars =
    cons (UChar.newline, cons (UChar.newline, whitespace n))

  def whitespace (n : Nat) : UChars =
    if n <= 0 then
      []
    else 
      cons (UChar.space, whitespace (n - 1))

  def fa (X) generate_Document (datum : X, 
				table as (main_entry as (main_sort, _) :: _) : SortExpansionTable) 
    : Document =
    let Base ((qualifier, main_id), _) = main_sort in
    make_Document [XMLDecl    standard_XMLDecl,                     % first <?xml version="1.0"?>
		   WhiteSpace [UChar.newline, UChar.newline],   
		   Element    (generate_Element (main_id, datum, main_sort, table, 0))]

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
	   | _ ->
		"[?? COMPOUND SORT ??]"
    in
      ustring (aux sd)

  def fa (X) generate_Element (name   : String,
			       datum  : X,
			       sd     : SortDescriptor,
			       table  : SortExpansionTable,
			       indent : Nat)
    : Element =
    let pattern   = expand_SortDescriptor (sd, table) in
    let uname     = ustring name in
    let value : QuotedText = {qchar = UChar.apostrophe,
			      text  = pp_sort_descriptor_for_xml_attribute sd}
    in
    let sort_attr : GenericAttribute = {w1    = [UChar.space],
					name  = ustring "type",
					w2    = null_whitespace,
					w3    = null_whitespace,
					value = value}
    in
    let attributes = [sort_attr] in
    %%
    case generate_content (datum, sd, pattern, table, indent + 2) of
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
		      trailer = Some (indentation_chardata (indent - 2))}

	      | (datum_element :: datum_elements, (sd_field_name, sd_field_pattern) :: sd_fields) ->
	         aux (datum_elements,
		      sd_fields, 
		      cons ((Some (indentation_chardata indent),
			     Element (generate_Element (sd_field_name, 
							datum_element, 
							sd_field_pattern, 
							table, 
							indent))),
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
	        Some {items = [(Some (indentation_chardata indent),
				Element (Empty (make_EmptyElemTag (ustring constructor_name, [], []))))],
		      trailer = Some (indentation_chardata (indent - 2))}
	      | Some sd_sub_pattern ->
	        case sd_options of
		  | [("None", _), ("Some", _)]  -> 
		    generate_content (sub_datum,
				      sd,
				      expand_SortDescriptor (sd_sub_pattern, table),
				      table,
				      indent)
		  | [("Some", _), ("None", _)]-> 
		    generate_content (sub_datum,
				      sd,
				      expand_SortDescriptor (sd_sub_pattern, table),
				      table,
				      indent)
		  | _ ->
		    Some {items = [(Some (indentation_chardata indent),
				    Element (generate_Element (constructor_name,
							       sub_datum,
							       sd_sub_pattern,
							       table,
							       indent)))],
			  trailer = Some (indentation_chardata (indent - 2))})

      | Base (qid, args) ->
	(case qid of
	  | ("String",  "String") ->
	    let string : String = Magic.magicCastToString datum in
	    indent_ustring (indent, ustring string)

	  | ("Integer", "Integer") ->
	    let n = Magic.magicCastToInteger datum in
	    indent_ustring (indent, ustring (Integer.toString n))

	  | ("List",    "List") ->
	    (let [element_sd] = args in
	     let new_element_sd = expand_SortDescriptor(element_sd, table) in
	     if new_element_sd = element_sd then
	       let items = Magic.magicCastToList datum in
	       let current_indentation = Some (indentation_chardata indent) in
	       Some {items = rev (foldl (fn (item, items) ->
					 cons ((current_indentation,
						Element (generate_Element ("i",
									   item,
									   element_sd,
									   table,
									   indent + 2))),
					       items))
				        []
					items),
		     trailer = Some (indentation_chardata (indent - 2))}
	     else
	       generate_content (datum,
				 sd,
				 Base (qid, [new_element_sd]),
				 table,
				 indent))

	  | ("Boolean", "Boolean") ->
	    let bool = Magic.magicCastToBoolean datum in
	    indent_ustring (indent, ustring (if bool then "true" else "false"))

	  | ("Char",    "Char") ->
	    let char = Magic.magicCastToChar datum in
	    indent_ustring (indent, ustring ("&#" ^ (Nat.toString (ord char)) ^";"))

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
				   indent))
	  | qid ->
	    indent_ustring (indent, 
			    ustring ("?? Base: " ^ (print_qid qid) ^  " ?? ")))

      | _ ->
	indent_ustring (indent, 
			ustring ("?? unrecognized type  ?? "))


   def indent_ustring (indent : Nat, ustr : UString) : Option Content =
     Some {items   = [],
	   trailer = Some ((indentation_chardata indent) ^ ustr ^ (indentation_chardata (indent - 2)))}

endspec
