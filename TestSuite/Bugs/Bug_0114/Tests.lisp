(test-directories ".")

(test 

 ("Bug 0114 : Equivalence of op decls should be detected"
  :show   "Colimit#C"
  :output '(
	    ";;; Elaborating diagram-colimit at $TESTDIR/Colimit#C"
	    ";;; Elaborating diagram-term at $TESTDIR/Colimit#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/Colimit#D"
	    ";;; Elaborating spec at $TESTDIR/Colimit#R"
	    ";;; Elaborating spec at $TESTDIR/Colimit#S"
	    ";;; Elaborating spec-morphism at $TESTDIR/Colimit#D"
	    ";;; Elaborating spec at $TESTDIR/Colimit#T"
	    ""
	    "spec  "
	    (:alternatives 
	     (" type {X, Y, Z}")
	     (" type {X, X, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    " "
	    (:alternatives
	     (" op  {f, g, h} : X")
	     (" op  {f, h, g} : X")
	     (" op  {g, f, h} : X")
	     (" op  {g, h, f} : X")
	     (" op  {h, f, g} : X")
	     (" op  {h, g, f} : X")

	     (" op  {f, g, h} : Y")
	     (" op  {f, h, g} : Y")
	     (" op  {g, f, h} : Y")
	     (" op  {g, h, f} : Y")
	     (" op  {h, f, g} : Y")
	     (" op  {h, g, f} : Y")

	     (" op  {f, g, h} : Z")
	     (" op  {f, h, g} : Z")
	     (" op  {g, f, h} : Z")
	     (" op  {g, h, f} : Z")
	     (" op  {h, f, g} : Z")
	     (" op  {h, g, f} : Z"))
	    "endspec"
	    ""
	    ""))

 )