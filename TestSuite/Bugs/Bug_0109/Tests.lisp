(test-directories ".")

(test 

 ("Bug 0109 : Declarations not printed"
  :show   "DeclsRequired"
  :output '(";;; Elaborating spec at $TESTDIR/DeclsRequired"
	    ""
	    "spec  "
	    " type YesNo =  | No | Yes"
	    " type Affirm =  | Ok | Sure | Yes"
	    " "
	    " op  f : Integer"
	    " op  g : Nat"
	    " op  x : List(Char)"
	    " op  y : List(String)"
	    " "
	    " op  z : Affirm"
	    " "
	    " def f = 3"
	    " "
	    " def g = 3"
	    " "
	    " def x = []"
	    " "
	    " def y = []"
	    " "
	    " def z = Yes"
	    "endspec"

	    ""
	    ""))

 )
