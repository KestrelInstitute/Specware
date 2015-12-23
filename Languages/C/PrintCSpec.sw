(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CGen qualifying spec

import /Languages/C/CUtils
import /Languages/C/CFlatten

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Split the C spec into .c and .h portions and print those two files.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
op flattenSpec?:Bool = true % no good reason to retain complicated comma expressions

op remove_directory (filename : String) : String =
 let chars = explode filename in
 case findRightmostAndFollowing (fn c -> c = #/) chars of
   | Some (_, _ :: tail) -> implode tail
   | _ -> filename

op printCSpec (c_spec : C_Spec, filename : String) : () =
 let len = length filename in
 let dir_and_basename = if (len > 2) && (subFromTo (filename, len-2, len) = ".c") then
                          subFromTo (filename, 0, len-2)
                        else
                          filename
  in
  let _ = writeLine (";; writing generated code to " ^ dir_and_basename ^ ".[ch]...") in

  let basename         = remove_directory dir_and_basename in
  let c_filename       = dir_and_basename ^ ".c"           in
  let h_filename       = dir_and_basename ^ ".h"           in

  %% segregrate entries for printing in .h or .c file :
  let (h_spec, c_spec) = splitCSpec c_spec                 in  


  let h_spec           = addHeader      (h_spec, dir_and_basename)           in
  let h_spec           = addTrailer     (h_spec, dir_and_basename)           in

 %let id_dfn           = ("Patched_PrismId", C_String, C_Const (C_Str basename)) in
 %let h_spec           = addConstDefn   (h_spec, id_dfn)                         in  

  let c_spec           = addHeader      (c_spec, dir_and_basename)           in
  let c_spec           = addTrailer     (c_spec, dir_and_basename)           in
  let c_spec           = prefixCInclude (c_spec, basename ^ ".h")            in
  let c_spec           = if flattenSpec? then flattenSpec c_spec else c_spec in

  let _ = printCSpecAsHeaderToFile (h_spec, h_filename) in
  let _ = printCSpecToFile         (c_spec, c_filename) in
  ()

end-spec
