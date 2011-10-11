AnnSpecPrinter qualifying spec
{
 type MetaSlang.ATerm b
 type MetaSlang.ASort b 
 type MetaSlang.APattern b

 op printTerm   : [a] MetaSlang.ATerm    a -> String 
 op printSort   : [a] MetaSlang.ASort    a -> String 
 op printPattern: [a] MetaSlang.APattern a -> String 
}
