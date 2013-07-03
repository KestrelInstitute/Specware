CGen qualifying spec

import /Languages/C/CUtils

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Split the C spec into .c and .h portions and print those two files.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op printCSpec (c_spec       : C_Spec,
               app_name     : String,
               opt_filename : Option String)
 : () =
 let filename =
     case opt_filename of
       | None          -> "cgenout.c"
       | Some filename -> filename
 in
 let len = length filename in
 let basename = if subFromTo (filename, len-2, len) = ".c" then
                  subFromTo (filename, 0, len-2)
                 else
                   filename
  in
  let _ = writeLine (";; writing generated code to " ^ basename ^ ".[ch]...") in

  let c_filename       = basename ^ ".c"    in
  let h_filename       = basename ^ ".h"    in
  let (h_spec, c_spec) = splitCSpec c_spec  in  

  let id_dfn           = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in
  let h_spec           = addHeader    (h_spec, app_name)   in
  let h_spec           = addTrailer   (h_spec, app_name)   in
  let h_spec           = addConstDefn (h_spec, id_dfn)     in  

  let c_spec           = addHeader    (c_spec, app_name)   in
  let c_spec           = addTrailer   (c_spec, app_name)   in
  let c_spec           = addInclude   (c_spec, h_filename) in

  let _ = printCSpecAsHeaderToFile (h_spec, h_filename) in
  let _ = printCSpecToFile         (c_spec, c_filename) in
  ()

end-spec
