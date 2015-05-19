SpecwareShell qualifying spec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type Chars = List Char

type CommandArgs = List CommandArg
type CommandArg  = | String String
                   | UnitId String
                   | Number Integer
                   | List   CommandArgs

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

op unitIdChar? (c : Char) : Bool =
 isAlphaNum c || c in? [#/, #:, ##, #_, #-, #~, #.]

%% this is unused for now, but deprecates cl-user::unitIdString? in toplevel.lisp
op unitIdString? (str) : Bool =
 forall? unitIdChar? (explode str)

op parseCommandArgs (s : String) : Result CommandArgs =
 let

   def parse_string (unread_chars, rev_str_chars) : Result (Chars * CommandArg) =
     case unread_chars of
       | [] -> Error "String not terminated by quote"
       | #" :: chars ->
         Good (chars, String (implode (reverse rev_str_chars)))
       | c :: chars ->
         parse_string (chars, c :: rev_str_chars)

   def parse_uid (unread_chars, rev_uid_chars) =
     case unread_chars of
       | [] ->
         Good ([], UnitId (implode (reverse rev_uid_chars)))
       | c :: chars ->
         if unitIdChar? c then
           parse_uid (chars, c :: rev_uid_chars)
         else
           Good (unread_chars, UnitId (implode (reverse rev_uid_chars)))

   def parse_number (unread_chars, rev_number_chars) =
     case unread_chars of
       | [] ->
         let n_str = implode (reverse rev_number_chars) in
         if intConvertible n_str then
           Good (unread_chars, Number (stringToInt n_str))
         else
           Error ("Cannot parse number: " ^ implode unread_chars)
       | c :: chars ->
         if isNum c then
           parse_number (chars, c :: rev_number_chars)
         else
           let n_str = implode (reverse rev_number_chars) in
           if intConvertible n_str then
             Good (unread_chars, Number (stringToInt n_str))
           else
             Error ("Cannot parse number: " ^ implode unread_chars)

   def parse_list (unread_chars, rev_elements) =
     case unread_chars of
       | [] -> Error "List not terminated by closing bracket"
       | #, :: chars ->
         parse_list (chars, rev_elements)
       | #] :: chars ->
         Good (chars, List (reverse rev_elements))
       | _ ->
         case parse_arg unread_chars of
           | Good (unread_chars, element) ->
             parse_list (unread_chars, element :: rev_elements)
           | error ->
             error

   def parse_arg unread_chars =
     case unread_chars of
       | [] -> Error "looking for an arg past end of input"
       | c :: chars -> 
         case c of 
           | #\s -> parse_arg chars
           | #" -> parse_string (chars, [])
           | #[ -> parse_list   (chars, [])
           | _ ->
             if isNum c then
               parse_number (unread_chars, [])
             else if unitIdChar? c then
               parse_uid (unread_chars, [])
             else
               Error ("cannot parse arg: " ^ implode unread_chars)

   def aux (unread_chars, rev_args) : Result (Chars * CommandArgs) =
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
