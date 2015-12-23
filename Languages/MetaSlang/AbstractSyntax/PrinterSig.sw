(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

AnnSpecPrinter qualifying spec
 import /Library/PrettyPrinter/BjornerEspinosa

 type MetaSlang.ATerm b
 type MetaSlang.AType b 
 type MetaSlang.APattern b

 op printTerm   : [a] MetaSlang.ATerm    a -> String 
 op printTermWithTypes: [a] MetaSlang.ATerm a -> String 
 op printTermPP : [a] MetaSlang.ATerm    a -> Pretty
 op printType   : [a] MetaSlang.AType    a -> String 
 op printTypePP : [a] MetaSlang.AType    a -> Pretty
 op printPattern: [a] MetaSlang.APattern a -> String 
end-spec

