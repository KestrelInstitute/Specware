spec
  import ../Endo
   import translate (translate ../Finite/AsAssocLists
     by {Dom._ +-> Elem._, Cod._ +-> Elem._})
     by {Elem.Dom +-> Elem.Elem, Elem.Cod +-> Elem.Elem}
endspec

