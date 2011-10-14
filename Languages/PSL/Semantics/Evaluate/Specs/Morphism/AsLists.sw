SpecMorph qualifying spec 
  import ../Morphism
  import OpMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo/AsAssocLists
      by {Elem._ +-> Op._, KeyValue._ +-> OpPair._})
      by {Op.Elem +-> Op.OpInfo})
  
  import TypeMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo/AsAssocLists
      by {Elem._ +-> Type._, KeyValue._ +-> TypePair._})
      by {Type.Elem +-> Type.TypeInfo})
endspec
