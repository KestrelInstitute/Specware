Finite qualifying spec
  import /Library/PrettyPrinter/WadlerLindig

  import Elem
  
  sort Collection

  op fold : fa (a) (a -> Elem -> a) -> Elem -> Collection -> a
  op pp : Collection -> Doc
endspec
