Position qualifying spec
  import /Library/Structures/Data/Pretty
  import /Languages/MetaSlang/Specs/Position

  op pp : Position -> Doc
  def pp position = pp (show position)
  op show : Position -> String
  def show = print
endspec

  
