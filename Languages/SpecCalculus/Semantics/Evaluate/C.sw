(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

(*   wrapper for calling the C generator *)

SpecCalc qualifying spec
{
import UnitId
import /Languages/MetaSlang/CodeGen/C/GenC

op evaluateCGen (value_info as (value,_,_) : ValueInfo, 
                 cterm                     : SCTerm,
                 opt_filename              : Option String)
 : SpecCalc.Env ValueInfo =

 case coerceToSpec value of
   | Spec ms_spec ->
     {cUID <- SpecCalc.getUID cterm;
      print (";;; Generating C files ");
      c_filename <- UIDtoCFile (cUID, opt_filename);
      print (c_filename ^ "\n");
      return (ensureDirectoriesExist c_filename);
      return (generateCFiles (ms_spec, c_filename));
      return value_info}
   | _ -> 
     raise (TypeCheck ((positionOf cterm),
                       "attempting to generate C code from an object that is not a specification"))

op UIDtoCFile (unitId as {path,hashSuffix} : UnitId, opt_filename : Option String) 
 : SpecCalc.Env String =
 case opt_filename of
   | Some fileName -> return fileName
   | _ -> 
     {
      prefix   <- removeLast path;
      mainName <- last path;
      fileName <- return ((uidToFullPath {path=prefix,hashSuffix=None})
                            ^ "/C/" ^ mainName ^ ".c");
      return fileName}
}


