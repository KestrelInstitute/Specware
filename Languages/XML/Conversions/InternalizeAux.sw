XML qualifying spec

  import ../XML_Sig
  import ../Printers/XML_Printer % for error messages
  import /Languages/MetaSlang/Specs/Elaborate/SortDescriptor
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

  def element_type_attribute (element : PossibleElement) : Option String =
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

  def etag_type_attribute (etag : EmptyElemTag) : Option String =
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
	  etag.attributes

  def level_str (n) =
    let def aux j =
         if j >= n then 
	   "[" ^ (Nat.toString n) ^ "] "
	 else 
	   "  " ^ (aux (j + 1))
    in
      "\n" ^ (aux 0)

  op read_ad_hoc_string : fa (X) SortDescriptor * Content -> X

  sort ID             = String
  sort Attributes     = List Attribute
  sort Attribute      = AttributeName * AttributeValue
  sort AttributeName  = String
  sort AttributeValue = | ID         ID
                        | IDREF      ID
                        | IDREFS     (List ID)
                        | ENTITY     Name
                        | ENTITIES   (List Name)
                        | NMTOKEN    NmToken
                        | NMTOKENS   (List NmToken)
                        | CDATA      String
                        | Choice     String

endspec