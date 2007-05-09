(test-directories ".")

(test 

  ("Bug 0124 : Choose prints incorrectly"
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
