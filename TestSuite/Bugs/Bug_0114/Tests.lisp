(test-directories ".")

(test 

 ("Bug 0114 : Equivalence of op decls should be detected"
  :show   "Colimit#C"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Colimit#R"
	    ";;; Elaborating spec-translation at $TESTDIR/Colimit#S"
	    ";;; Elaborating spec-translation at $TESTDIR/Colimit#T"
	    ";;; Elaborating spec-diagram at $TESTDIR/Colimit#D"
	    ";;; Elaborating spec-colimit at $TESTDIR/Colimit#C"
	    ""
	    "spec "
	    " type {X, Y, Z}"
	    " op  {f, g, h} : X"
	    "endspec"
	    ""
	    ""))

 )