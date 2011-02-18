(test-directories ".")

(test 

 ("Bug 0109 : Declarations not printed"
  :show   "DeclsRequired"
  :output '(";;; Elaborating spec at $TESTDIR/DeclsRequired"
	    (:optional "")
	    "spec  "
	    (:optional "")
	    " type YesNo =  | No | Yes"
	    (:optional "")
	    " type Affirm =  | Ok | Sure | Yes"
	    (:optional "")
	    " op  f : Integer"
	    (:optional "")
	    " op  g : Nat"
	    (:optional "")
	    " op  x : List(Char)"
	    (:optional "")
	    " op  y : List(String)"
	    (:optional "")
	    " op  z : Affirm"
	    (:optional "")
	    " def f = 3"
	    (:optional "")
	    " def g = 3"
	    (:optional "")
	    " def x = []"
	    (:optional "")
	    " def y = []"
	    (:optional "")
	    " def z = Yes"
	    (:optional "")
	    "endspec"
	    (:optional "")
	    (:optional "")))
 )
