GCG qualifying spec

import /Languages/MetaSlang/CodeGen/C/SpecToCSpec  % generateCSpec
import /Languages/C/PrintCSpec                     % printCSpec

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% generateCCode is a side-effecting transform that returns the original spec.
%%
%% It generate C code for the given spec and writes it into the appropriate
%% .h and .c files.
%%
%% (If the filename is None, "cgenout.c" is used.)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.generateCCode (ms_spec      : Spec, 
                                app_name     : String,
                                opt_filename : Option String)
 : Spec =
 % for generation using CTarget, see evaluateGenCThin in Languages/SpecCalculus/Semantics/Specware.sw
 % if importsCTarget? spc then
 %   let _ = writeLine("Spec refers to CTarget, will use new C generator.") in
 %   let filename = case opt_filename of 
 %                    | Some filename -> filename 
 %                    | _ -> "testing" 
 %   in
 %   printSpecAsCToFile (filename, spc)
 % else
 let c_spec = generateCSpec app_name ms_spec              in
 let _      = printCSpec (app_name, c_spec, opt_filename) in
 ms_spec

end-spec
