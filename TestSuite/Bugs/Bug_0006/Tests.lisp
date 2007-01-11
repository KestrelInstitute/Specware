(test-directories ".")

(test 

 ("Bug 0006 : Pretty printing of digrams should yield something that looks like the starting syntax [D]"
  :show "Diagram#D"
  :output '(
	    (:optional "")
	    ";;; Elaborating diagram-term at $TESTDIR/Diagram#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#D"
	    ";;; Elaborating spec at $TESTDIR/Diagram#R"
	    ";;; Elaborating spec at $TESTDIR/Diagram#S"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#D"
	    ";;; Elaborating spec at $TESTDIR/Diagram#T"
	    (:optional "")
	    "diagram {a : p -> q"
	    "         +->"
	    "         morphism R -> S"
	    "          {type X +-> Y},"
	    "         b : p -> r"
	    "         +->"
	    "         morphism R -> T"
	    "          {type X +-> Z}}"
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0006 : Pretty printing of digrams should yield something that looks like the starting syntax [C1]"
  :show "Diagram#C1"
  :output '(
	    (:optional "")
	    ";;; Elaborating diagram-colimit at $TESTDIR/Diagram#C1"
	    ";;; Elaborating diagram-term at $TESTDIR/Diagram#C1"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#C1"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#C1"
	    (:optional "")
	    "spec  "
	    (:alternatives 
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ))

 ("Bug 0006 : Pretty printing of digrams should yield something that looks like the starting syntax [C2]"
  :show "Diagram#C2"
  :output '(
	    (:optional "")
	    ";;; Elaborating diagram-colimit at $TESTDIR/Diagram#C2"
	    (:optional "")
	    "spec  "
	    (:alternatives 
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    (:optional "")
	    (:optional "")
	    ))

 )
