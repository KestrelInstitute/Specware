spec
  import /Library/PrettyPrinter/WadlerLindig
  sort Type
  sort TypeVars

  op String.pp : String -> Doc
  def String.pp = ppString  % legacy

  op Nat.pp : Nat -> Doc
  def Nat.pp n = pp (Nat.toString n)

  op Integer.pp : Integer -> Doc
  def Integer.pp n = pp (Integer.toString n)

  op Boolean.pp : Boolean -> Doc
  def Boolean.pp b = pp (Boolean.toString b)

  op Char.pp : Char -> Doc
  def Char.pp c = pp (Char.toString c)
endspec

