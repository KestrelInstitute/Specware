
XML qualifying spec

  import XML_Sig
  import Parser/XML_Parser
  import Printers/XML_Printer
  import Printers/Metaslang_to_XML

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%                 INTERFACE
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op parseXML        : fa (X) String  -> X     % Very tricky -- actual handwritten function takes extra arg depicting X
  op parseUnicodeXML : fa (X) UString -> X     % Very tricky -- actual handwritten function takes extra arg depicting X
  op printXML        : fa (X) X -> String      % Very tricky -- actual handwritten function takes extra arg depicting X
  op printUnicodeXML : fa (X) X -> UString     % Very tricky -- actual handwritten function takes extra arg depicting X

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%                 INPUT
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  sort Filename = String

  op read_unicode_chars_from_file : Filename -> Option UChars

  def read_Document_from_file (filename : Filename) : Option Document =
    let possible_uchars = read_unicode_chars_from_file filename in % handwritten lisp
    case possible_uchars of
      | Some uchars ->
        run_document_monad {
			    (document, uchars) <- parse_Document uchars;
			    return (Some document)
			   }
      | _ -> None

  def read_Document_from_String (str : String) : Option Document =
    run_document_monad {
			(document, uchars) <- parse_Document (ustring str);
			return (Some document)
		       }

  def read_Document_from_UString (uchars : UChars) : Option Document =
    run_document_monad {
			(document, uchars) <- parse_Document uchars;
			return (Some document)
		       }

  def run_document_monad (run : Env (Option Document)) =
    case catch run XML_Handler initialState  of
      | (Ok         possible_doc, newstate) -> 
        let _ = map (fn exception -> toScreen (print_XML_Exception exception))
	            newstate.exceptions
	in
	  possible_doc

      | (Exception  exception,    newstate) -> 
        let _ = map (fn exception -> toScreen (print_XML_Exception exception))
	            newstate.exceptions
	in
	  let _ = toScreen (print_XML_Exception exception) in
	None

  def XML_Handler (except) : Env (Option Document) = 
    let _ = toScreen (print_XML_Exception except) in
    return None

%%% from Specware.sw :
%%%  def toplevelHandler except =
%%%    {cleanupGlobalContext;		% Remove InProcess entries
%%%     saveSpecwareState;			% So work done before error is not lost
%%%     return (gotoErrorLocation except);
%%%     if specwareWizard? then
%%%       fail message
%%%     else
%%%       print message;
%%%     return false}

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%                 OUTPUT 
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  op write_unicode_chars_to_file : UChars * Filename -> ()

  def print_Document_to_String (doc : Document) : String =
    string (print_Document_to_UString doc)

  def print_Document_to_file (doc : Document, filename : Filename) =
    let ustr = print_Document_to_UString doc in
    write_unicode_chars_to_file (ustr, filename) % handwritten lisp


endspec