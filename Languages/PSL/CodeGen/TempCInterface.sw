spec
 sort CSpec
 sort Id.Id
 sort Proc.Procedure
 sort Spec.Spec
 sort Oscar.Spec

 sort SpecCalc.Env a

 sort Convert.StructOscarSpec
 sort ModeSpec.ModeSpec

 op emptyCSpec : String -> CSpec

 op CInterface.addInclude : CSpec * String -> CSpec 
 op OscarStruct.show : StructOscarSpec -> ModeSpec -> String
 op Convert.convertOscarSpec : Oscar.Spec -> Env StructOscarSpec
 op Convert.structOscarSpec : StructOscarSpec -> Env StructOscarSpec

 op SpecCalc.oscarToC : Oscar.Spec -> Spec.Spec -> Option String -> Env CSpec
 op SpecCalc.generateCProcedure : Spec.Spec -> CSpec -> Id.Id -> Procedure -> Env CSpec
 op CInterface.printToFile : CSpec * Option String -> ()
endspec
 
