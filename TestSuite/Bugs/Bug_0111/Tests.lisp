(test-directories ".")

(test 

 ("Bug 0111 : Capture of translated ops by var bindings [Once]"
  :show   "Capture#T"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#T"
	    ";;; Elaborating spec at $TESTDIR/Capture#S"
	    (:optional "")
	    "spec"
	    (:optional "")
	    " op  xx : Nat"
	    (:optional "")
	    " op  ww : Nat -> Nat"
	    (:optional "")
	    " op  ff (xx0 : Nat) : Int = xx0 + xx"
	    (:optional "")
	    " axiom foo is fa(xx0 : Nat) xx0 = xx0 + xx"
	    (:optional "")
	    " op  g (n : Nat) : Int = let xx0 = n in "
	    "                             xx0 + xx"
	    (:optional "")
	    " op  h (n : Nat) : Int  = let def ww0 n = n"
	    "                                  in"
	    "                                  ww0 n + ww n"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))


 ("Bug 0111 : Capture of translated ops by var bindings [Repeated]"
  :show   "Capture#W"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#W"
	    (:optional "")
	    "spec  "
	    (:optional "")
	    " op  aa : Nat"
	    (:optional "")
	    " op  bb : Nat -> Nat"
	    (:optional "")
	    " op  ff (xx0 : Nat) : Int = xx0 + aa"
	    (:optional "")
	    " axiom foo is fa(xx0 : Nat) xx0 = xx0 + aa"
	    (:optional "")
	    " op  g (n : Nat) : Int = let xx0 = n in "
	    "                             xx0 + aa"
	    (:optional "")
	    " op  h (n : Nat) : Int = let def ww0 n = n"
	    "                                 in"
	    "                                 ww0 n + bb n"
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))


 )
