
XML qualifying spec

  import ../XML_Sig

  %% TODO: many tests for legality ...

  def make_Document (items : DocItems) : Document =
    {items = items}

  def standard_XMLDecl : XMLDecl =
    let version_attr = {w1    = UString.space,
			name  = ustring "version",
			w2    = [],
			w3    = [],
			value = {qchar = UChar.double_quote, 
				 text  = ustring "1.0"}}
    in
      {prefix     = UString.question_mark,
       name       = ustring "xml",
       attributes = [version_attr],
       whitespace = [],
       postfix    = UString.question_mark}

  def make_Empty_Element (empty_tag : EmptyElemTag)
    : Element =
    Empty empty_tag

  def make_Full_Element (stag    : STag, 
			 content : Content, 
			 etag    : ETag)
    : Element =
    Full {stag    = stag,
	  content = content,
	  etag    = etag}

  def make_Content (items   : List (Option CharData * Content_Item),
		    trailer : Option CharData)
    : Content =
    {items   = items,
     trailer = trailer}

  def make_Content_Item_from_Element   (element : Element)   : Content_Item =  Element   element
  def make_Content_Item_from_Reference (ref     : Reference) : Content_Item =  Reference ref
  def make_Content_Item_from_PI        (pi      : PI)        : Content_Item =  PI        pi
  def make_Content_Item_from_CDSect    (cd_sect : CDSect)    : Content_Item =  CDSect    cd_sect
  def make_Content_Item_from_Comment   (comment : Comment)   : Content_Item =  Comment   comment 

  def make_STag (name       : UChars,
		 attributes : GenericAttributes,
		 whitespace : WhiteSpace)
    : STag =
    {prefix     = [],
     name       = name,
     attributes = attributes,
     whitespace = whitespace,
     postfix    = []}

  def make_ETag (name       : UChars,
		 whitespace : WhiteSpace)
    : STag =
    {prefix     = UString.back_slash,
     name       = name,
     attributes = [],
     whitespace = whitespace,
     postfix    = []}

  def make_EmptyElemTag (name       : UChars,
			 attributes : GenericAttributes,
			 whitespace : WhiteSpace)
    : STag =
    {prefix     = [],  
     name       = name,
     attributes = attributes,
     whitespace = whitespace,
     postfix    = UString.back_slash}

  def make_GenericAttribute (w1    : WhiteSpace,
			     name  : NmToken,
			     w2    : WhiteSpace,
			     w3    : WhiteSpace,
			     value : QuotedText)
    : GenericAttribute =
    {w1    = w1,
     name  = name,
     w2    = w2,
     w3    = w3,
     value = value}

  def make_QuotedText (qchar : QuoteChar,
		       text  : UString)
    : QuotedText =
    {qchar = qchar,
     text  = text}

endspec
