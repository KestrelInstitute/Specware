(test-directories ".")

(test 

 ("Bug 0106 : Names not disambiguated when printing"
  :show   "AmbiguousRef"
  :output 
  '(";;; Elaborating spec at $TESTDIR/AmbiguousRef"
    (:optional "")
    "spec"
    (:optional "")
    (:alternatives
     "op b : Nat -> String = show"
     "def b : Nat -> String = show"
     ("op  b: Nat -> String"
      "def b: Nat -> String = show")
     ("op  b : Nat -> String"
      "def b : Nat -> String = show")
     ("op  b : Nat -> String"
      "def b = show"))
    (:optional "")
    (:alternatives "endspec" "end-spec")
    (:optional "")
    (:optional "")))

 )
