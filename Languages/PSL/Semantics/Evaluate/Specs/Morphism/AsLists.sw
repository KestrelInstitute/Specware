SpecMorph qualifying spec 
  import ../Morphism
  import OpMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo/AsAssocLists
      by {Elem._ +-> Op._, KeyValue._ +-> OpPair._})
      by {Op.Elem +-> Op.OpInfo})
  
  import SortMap qualifying
    (translate (translate /Library/Structures/Data/Maps/Endo/AsAssocLists
      by {Elem._ +-> Sort._, KeyValue._ +-> SortPair._})
      by {Sort.Elem +-> Sort.SortInfo})
endspec
