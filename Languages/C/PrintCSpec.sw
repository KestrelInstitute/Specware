CGen qualifying spec

import /Languages/C/CUtils
import /Languages/C/CFlatten

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Split the C spec into .c and .h portions and print those two files.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
op flattenSpec?:Bool = true % no good reason to retain complicated comma expressions

op printCSpec (c_spec : C_Spec, filename : String) : () =
 let len = length filename in
 let basename = if (len > 2) && (subFromTo (filename, len-2, len) = ".c") then
                  subFromTo (filename, 0, len-2)
                 else
                   filename
  in
  let _ = writeLine (";; writing generated code to " ^ basename ^ ".[ch]...") in

  let c_filename       = basename ^ ".c"    in
  let h_filename       = basename ^ ".h"    in
  let (h_spec, c_spec) = splitCSpec c_spec  in  

  let id_dfn           = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in

  let h_spec           = addHeader      (h_spec, basename)   in
  let h_spec           = addTrailer     (h_spec, basename)   in
 %let h_spec           = addConstDefn   (h_spec, id_dfn)     in  

  let c_spec           = addHeader      (c_spec, basename)   in
  let c_spec           = addTrailer     (c_spec, basename)   in
  let c_spec           = prefixCInclude (c_spec, h_filename) in  % import of .h file comes first
  let c_spec = if flattenSpec? then flattenSpec c_spec else c_spec in
  let _ = printCSpecAsHeaderToFile (h_spec, h_filename) in
  let _ = printCSpecToFile         (c_spec, c_filename) in
  ()

end-spec
