spec {
  import Parser/Parse
  import AbstractSyntax/Types
  import AbstractSyntax/SimplePrinter

  op pslTest : String -> ()
  def pslTest file =
    case parseFile file of
      | Some spec_term -> toScreen (ppFormat (ppSpecTerm spec_term))
      | None -> fail "Syntax error"
}
