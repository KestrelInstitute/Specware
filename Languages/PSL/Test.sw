spec {
  import Parser/Parse
  import AbstractSyntax/Types
  import AbstractSyntax/SimplePrinter

  op pslTest : String -> ()
  def pslTest file =
    case parseFile file of
      | Some specFile -> toScreen (ppFormat (ppSpecFile specFile))
      | None -> fail "Syntax error"
}
