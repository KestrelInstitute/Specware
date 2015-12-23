(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec
  import Typedef

  def metakeytab : Map(Name, Name) =
  [ ("as",          "as1")
  , ("axiom",       "axiom1")
  , ("case",        "case1")
  , ("choose",      "choose1")
  , ("colimit",     "colimit1")
  , ("conjecture",  "conjecture1")
  , ("def",         "def1")
  , ("diagram",     "diagram1")
  , ("else",        "else1")
  , ("embed",       "embed1")
  , ("embed?",      "embed?1")
  , ("endspec",     "endspec1")
  , ("ex",          "ex1")
  , ("fa",          "fa1")
  , ("false",       "false1")
  , ("fn",          "fn1")
  , ("from",        "fromm")
  , ("generate",    "generate1")
  , ("if",          "if1")
  , ("import",      "import1")
  , ("in",          "in1")
  , ("infixl",      "infixl1")
  , ("infixr",      "infixr1")
  , ("is",          "is1")
  , ("let",         "let1")
  , ("morphism",    "morphism1")
  , ("obligations", "obligations1")
  , ("of",          "of1")
  , ("op",          "op1")
  , ("project",     "project1")
  , ("prove",       "prove1")
  , ("qualifying",  "qualifying1")
  , ("quotient",    "quotient1")
  , ("relax",       "relax1")
  , ("restrict",    "restrict1")
  , ("spec",        "spec1")
  , ("then",        "then1")
  , ("theorem",     "theorem1")
  , ("translate",   "translate1")
  , ("true",        "true1")
  , ("type",        "tipo")
  , ("where",       "where1")
  ]

  op  metakey : Name -> Name
  def metakey n =
    if dom metakeytab n
    then
      metakeytab@n
    else
      n

endspec
