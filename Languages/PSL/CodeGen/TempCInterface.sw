spec
 type CSpec
 type Id.Id
 type Proc.Procedure
 type Spec.Spec
 type Oscar.Spec

 type SpecCalc.Env a

 type Convert.StructOscarSpec
 type ModeSpec.ModeSpec

 op emptyCSpec : String -> CSpec

 op CInterface.addInclude : CSpec * String -> CSpec 
 op OscarStruct.show : StructOscarSpec -> ModeSpec -> String
 op Convert.convertOscarSpec : Oscar.Spec -> Env StructOscarSpec
 op Convert.structOscarSpec : StructOscarSpec -> Env StructOscarSpec

 op SpecCalc.oscarToC : Oscar.Spec -> Spec.Spec -> Option String -> Env CSpec
 op SpecCalc.generateCProcedure : Spec.Spec -> CSpec -> Id.Id -> Procedure -> Env CSpec
 op CInterface.printToFile : CSpec * Option String -> ()
endspec
 
