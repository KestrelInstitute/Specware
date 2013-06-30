RemoveSubtypes qualifying spec

import /Languages/MetaSlang/Specs/Environment

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Remove subtype predicates, etc. that would not appear in final code.
%% Keep subtypes of Nat, later used to choose among char, short, int, long, etc.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

op SpecTransform.reviseTypesForJava (spc : Spec) : Spec =
 revise_types spc

op SpecTransform.reviseTypesForC (spc : Spec) : Spec =
 revise_types spc

op revise_types (spc : Spec) : Spec =
 let 
   def strip typ =
     case typ of
       %% new case to preserve subtypes of Nat:
       | Subtype (Base (Qualified ("Nat",     "Nat"), [], _), _, _) -> typ
       | Subtype (Base (Qualified ("Integer", "Int"), [], _), _, _) -> typ
       | Subtype (typ, _, _) -> strip typ
       | _ -> typ
 in
 %% Warning: logical mayhem?
 mapSpec (fn t -> t, strip, fn p -> p) spc

end-spec
