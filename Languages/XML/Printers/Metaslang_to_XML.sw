
XML qualifying spec

  %% TODO: tests for legality ...
  import ../XML_Sig

  def make_Document (items : DocItems) : Document =
    {items = items}

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

  def make_Content (prelude : Option CharData,
		    items   : List (Content_Item * Option CharData))
    : Content =
    {prelude = prelude,
     items   = items}

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
    {prefix     = [47],  (* '/' *)
     name       = name,
     attributes = [],
     whitespace = whitespace,
     postfix    = []}

  def make_EmptyElemETag (name       : UChars,
			  attributes : GenericAttributes,
			  whitespace : WhiteSpace)
    : STag =
    {prefix     = [],  
     name       = name,
     attributes = attributes,
     whitespace = whitespace,
     postfix    = [47]}  (* '/' *)

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
