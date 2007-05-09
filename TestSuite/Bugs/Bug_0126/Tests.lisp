(test-directories ".")

(test 

  ("Bug 0126 : Type comparison of polymorphic ops in translation fails to compare modulo alpha conversion"
   :show  "Alpha#MOR"
   :output '(
	     (:optional ";;; Elaborating spec-morphism at $TESTDIR/Alpha#MOR")
	     (:optional ";;; Elaborating spec at $TESTDIR/Alpha#DOM")
	     (:optional ";;; Elaborating spec at $TESTDIR/Alpha#COD")
	     (:optional "")
	     (:alternatives
	      ("morphism DOM -> COD"
	       "                    {op x +-> y}")
	      ("morphism DOM -> COD {op x +-> y}"))
	     (:optional "")
	     (:optional "")
	     ))
  )
