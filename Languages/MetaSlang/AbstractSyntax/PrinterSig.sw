AnnSpecPrinter qualifying spec
 type MetaSlang.ATerm b
 type MetaSlang.AType b 
 type MetaSlang.APattern b

 op printTerm   : [a] MetaSlang.ATerm    a -> String 
 op printTermWithTypes: [a] MetaSlang.ATerm a -> String 
 op printType   : [a] MetaSlang.AType    a -> String 
 op printPattern: [a] MetaSlang.APattern a -> String 
end-spec

