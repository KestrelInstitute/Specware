RemoveTheorems qualifying spec 

import /Languages/MetaSlang/Specs/AnnSpec

op SpecTransform.removeTheorems (spc : Spec) : Spec = 
 %% theorems are irrelevant for code generation
 let
   def filter el =
     case el of
       | Property _ -> None
       | _ -> Some el
 in
 setElements (spc, mapPartialSpecElements filter spc.elements)

end-spec
