(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

SpecwareShell qualifying spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

import TypedValues

type Chars = List Char

type Result a = | Good  a
                | Error String
                | NotYetImplemented

type DirectoryName = String
type SearchPath    = List DirectoryName

type CommandContext = {current_dir  : DirectoryName,
                       current_path : SearchPath}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op mkCommandContext (current_dir  : DirectoryName,
                     current_path : SearchPath)
 : CommandContext =
 {current_dir  = current_dir,
  current_path = current_path}

op currentDir  (ctxt : CommandContext) : DirectoryName = ctxt.current_dir
op currentPath (ctxt : CommandContext) : SearchPath    = ctxt.current_path

%% ad-hoc interface to lisp-based command state
%% deprecate when toplevel command processing loop is translated from lisp to specware 

op getCommandContext () : CommandContext
op setCommandContext (ctxt : CommandContext) : CommandContext

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op symbolChar? (c : Char) : Bool =
 isAlphaNum c || 
 %% many special characters, but not quotes, parens, brackets, backslash, colon, semicolon, or comma
 c in? [#~, #!, #@, ##, #$, #%, #^, #&, #*, #_, #-, #+, #=, #|, #:, #<, #>, #., #?, #/]

op unitIdChar? (c : Char) : Bool =
 isAlphaNum c || c in? [#/, #:, ##, #_, #-, #~, #.]

%% this is unused for now, but deprecates cl-user::unitIdString? in toplevel.lisp
op unitIdString? (str) : Bool =
 forall? unitIdChar? (explode str)

op parseCommandArgs (s : String) : Result TypedValues =
 let

   def parse_string (unread_chars, rev_str_chars) =
     case unread_chars of
       | [] -> Error "String not terminated by quote"
       | #" :: chars ->
         Good (chars, String (implode (reverse rev_str_chars)))
       | c :: chars ->
         parse_string (chars, c :: rev_str_chars)

   def parse_symbol (unread_chars, rev_sym_chars) =
     case unread_chars of
       | [] ->
         Good ([], Symbol (implode (reverse rev_sym_chars)))
       | c :: chars ->
         if symbolChar? c then
           parse_symbol (chars, c :: rev_sym_chars)
         else
           Good (unread_chars, Symbol (implode (reverse rev_sym_chars)))

   def parse_integer (unread_chars, rev_int_chars) =
     case unread_chars of
       | [] ->
         let n_str = implode (reverse rev_int_chars) in
         if intConvertible n_str then
           Good (unread_chars, Int (stringToInt n_str))
         else
           Error ("Cannot parse integer: " ^ implode unread_chars)
       | c :: chars ->
         if isNum c then
           parse_integer (chars, c :: rev_int_chars)
         else
           let n_str = implode (reverse rev_int_chars) in
           if intConvertible n_str then
             Good (unread_chars, Int (stringToInt n_str))
           else
             Error ("Cannot parse integer: " ^ implode unread_chars)

   def parse_sw_list (unread_chars, rev_elements) =
     case unread_chars of
       | [] -> Error "List not terminated by closing bracket"
       | #, :: chars ->
         parse_sw_list (chars, rev_elements)
       | #] :: chars ->
         Good (chars, List (reverse rev_elements))
       | _ ->
         case parse_arg unread_chars of
           | Good (unread_chars, element) ->
             parse_sw_list (unread_chars, element :: rev_elements)
           | error ->
             error

   def parse_lisp_list (unread_chars, rev_elements) =
     case unread_chars of
       | [] -> Error "List not terminated by closing bracket"
       | #) :: chars ->
         Good (chars, List (reverse rev_elements))
       | _ ->
         case parse_arg unread_chars of
           | Good (unread_chars, element) ->
             parse_lisp_list (unread_chars, element :: rev_elements)
           | error ->
             error

   def parse_arg unread_chars =
     case unread_chars of
       | [] -> Error "looking for an arg past end of input"
       | c :: chars -> 
         case c of 
           | #\s -> parse_arg chars
           | #" -> parse_string (chars, [])
           | #[ -> parse_sw_list   (chars, [])
           | #( -> parse_lisp_list (chars, [])
           | _ ->
             if isNum c then
               parse_integer (unread_chars, [])
             else if symbolChar? c then
               parse_symbol (unread_chars, [])
             else
               Error ("cannot parse arg: " ^ implode unread_chars)

   def aux (unread_chars, rev_args) =
     case unread_chars of
       | [] -> Good ([], reverse rev_args)
       | _ ->
         case parse_arg unread_chars of
           | Good (unread_chars, arg) ->
             let rev_args = arg :: rev_args in
             aux (unread_chars, rev_args)
           | Error msg -> Error msg
         
 in
 case aux (explode s, []) of
   | Good ([], args) ->
     Good args
   | Error msg ->
     Error msg


end-spec
