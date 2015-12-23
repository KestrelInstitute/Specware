(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

CodeGen qualifying spec

import /Languages/MetaSlang/Specs/Environment

%% TODO: Change this to preserve all subtypes but to canonicalize them in a way
%%       that facilitates code generation.
%%       Revise types to be subtypes of supertypes that have direct 
%%       implmentations in target languages:  Nat8, Int32, etc.

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
 %% Warning: logical mayhem? -- TODO: See note above
 mapSpec (fn t -> t, strip, fn p -> p) spc

end-spec
