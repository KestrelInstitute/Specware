
XML qualifying spec

  import /Library/IO/Unicode/UnicodeSig
  import XML_Sig
  import Parser/XML_Parser
  import Printers/GenerateDocument
  import Printers/XML_Printer

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%                 INTERFACE
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  %% These are all very tricky -- actual handwritten function takes extra arg depicting X 
  op parseXML        : fa (X) String  -> X     % Tricky, TODO
  op parseUnicodeXML : fa (X) UString -> X     % Tricky, TODO
  op printXML        : fa (X) X -> String      % Tricky, see Languages/XML/Handwritten/Lisp/Support.lisp
  op printUnicodeXML : fa (X) X -> UString     % Tricky, TODO

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%                 INPUT
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  % sort Filename = String

  % op unicode.read_unicode_chars_from_file : Filename * Decoding -> Option UChars

  def read_Document_from_file (filename : Filename) : Option Document =
    let possible_uchars = read_unicode_chars_from_file (filename, null_decoding) in % handwritten lisp
    case possible_uchars of
      | Some uchars ->
        run_document_monad uchars
	                   {
			    (document, uchars) <- parse_Document uchars;
			    return (Some document)
			   }
      | _ -> None

  def read_Document_from_String (str : String) : Option Document =
    let uchars = ustring str in
    run_document_monad uchars
                       {
			(document, uchars) <- parse_Document uchars;
			return (Some document)
		       }

  def read_Document_from_UString (uchars : UChars) : Option Document =
    run_document_monad uchars
                       {
			(document, uchars) <- parse_Document uchars;
			return (Some document)
		       }

  def run_document_monad (uchars : UChars) (run : Env (Option Document)) =
    let (result, newstate) = catch run XML_Handler (initialState uchars) in
    case (result, newstate.exceptions) of

      | (Ok possible_document, []) -> 
        possible_document

      | _ ->
	let _ = toScreen (print_pending_XML_Exceptions newstate) in
	None

  def XML_Handler _ : Env (Option Document) = 
    %% let _ = toScreen (print_XML_Exception except) in %% catch inserts exception into state
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

  % op write_unicode_chars_to_file : UChars * Filename * Encoding -> ()

  def print_Document_to_String (doc : Document) : String =
    string (print_Document_to_UString doc)

  def print_Document_to_file (doc : Document, filename : Filename) =
    let ustr = print_Document_to_UString doc in
    write_unicode_chars_to_file (ustr, filename, null_encoding) % handwritten lisp


endspec