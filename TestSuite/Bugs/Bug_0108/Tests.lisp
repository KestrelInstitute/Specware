(test-directories ".")

(test 

 ("Bug 0108 : Printing of diagram is atrocious"
  :show   "Diagram#D"
  :output '(";;; Elaborating diagram-term at $TESTDIR/Diagram#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#M"
	    ";;; Elaborating spec at $TESTDIR/Diagram#R"
	    ";;; Elaborating spec at $TESTDIR/Diagram#S"
	    ";;; Elaborating spec-morphism at $TESTDIR/Diagram#N"
	    ";;; Elaborating spec at $TESTDIR/Diagram#T"
	    (:optional "")
            (:alternatives
             "diagram {a : x -> y +-> "
             ("diagram {a : x -> y"
              "         +->"))
            (:alternatives
             "         morphism R -> S {type A1 +-> B1,"
             ("         morphism R -> S"
              "          {type A1 +-> B1,"))
	    (:alternatives
	     ("           type A2 +-> B2,"
	      "           type A3 +-> B3,")
	     ("           type A3 +-> B3,"
	      "           type A2 +-> B2,"))
            (:alternatives
             "           op f +-> g},"
             "           op f +-> g} ,")
	    "         b : x -> z"
	    "         +->"
            (:alternatives
             "         morphism R -> T {type A1 +-> C1,"
             ("         morphism R -> T"
              "          {type A1 +-> C1,"))
	    (:alternatives
	     ("           type A2 +-> C2,"
	      "           type A3 +-> C3,")
	     ("           type A3 +-> C3,"
	      "           type A2 +-> C2,"))
	    (:alternatives
             "           op f +-> h}}"
             "           op f +-> h} }")
	    (:optional "")
	    (:optional "")
	    ))
 )
