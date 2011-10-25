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
	    (:alternatives
             " def f = 3"
             " def f : Integer = 3")
	    (:optional "")
	    (:alternatives
             " def g = 3"
             " def g : Nat = 3")
	    (:optional "")
	    (:alternatives
             " def x = []"
             " def x : List(Char) = []")
	    (:optional "")
	    (:alternatives
             " def y = []"
             " def y : List(String) = []")
	    (:optional "")
	    (:alternatives
             " def z = Yes"
             " def z : Affirm = Yes")
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
            ))
)
