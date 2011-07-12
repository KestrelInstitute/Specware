(*   wrapper for calling the C generator *)

SpecCalc qualifying spec
{
  import UnitId
  import /Languages/MetaSlang/CodeGen/C/CG

  op evaluateCGen (app_name                     : String,
                   value_info as (Spec spc,_,_) : ValueInfo, 
                   opt_filename                 : Option String)
   : SpecCalc.Env ValueInfo =
   {
    (_, base_spec) <- getBase; % ignore unitid
    return (generateCCode (app_name, base_spec, spc, opt_filename));
    return value_info
    }
}
