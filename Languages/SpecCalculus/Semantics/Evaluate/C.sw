(*   wrapper for calling the C generator *)

SpecCalc qualifying spec
  import UnitId
  import /Languages/MetaSlang/CodeGen/C/GenC

  op evaluateCGen (app_name                         : String,
                   value_info as (Spec ms_spec,_,_) : ValueInfo, 
                   opt_filename                     : Option String)
   : SpecCalc.Env ValueInfo =
   {
    return (generateCFiles (ms_spec, app_name, opt_filename));
    return value_info
    }
end-spec

