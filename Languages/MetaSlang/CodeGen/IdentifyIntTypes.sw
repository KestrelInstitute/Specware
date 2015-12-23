(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

IdentifyIntTypes qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec

op identifyIntTypes : Spec -> Spec
def identifyIntTypes spc =
  let
    def identifyIntType typ =
      case typ of
	| Base (Qualified ("Nat",     "Nat"),       [], b) -> Base (Qualified ("Integer", "Int"), [], b)
	| Base (Qualified ("Nat",     "PosNat"),    [], b) -> Base (Qualified ("Integer", "Int"), [], b)
	| Base (Qualified ("Integer", "NZInteger"), [], b) -> Base (Qualified ("Integer", "Int"), [], b)
	| Base (Qualified ("Integer", "Int"),       [], b) -> Base (Qualified ("Integer", "Int"), [], b)
	| Base (Qualified ("Integer", "Int0"),      [], b) -> Base (Qualified ("Integer", "Int"), [], b)
      %	| Base (Qualified ("??",      "long"),      [], b) -> Base (Qualified ("Integer", "Int"), [], b)
      % ... There was a hack for PSL inserted here ... It also required commenting out the qualifiers in the cases above (ugh).
	| _ -> typ
  in
  let termid = (fn t -> t) in
  let pattid = (fn p -> p) in
  mapSpec (termid, identifyIntType, pattid) spc

end-spec
