(test-directories ".")

(test 

 ("Bug 0111 : Capture of translated ops by var bindings [Once]"
  :show   "Capture#T"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#T"
	    ";;; Elaborating spec at $TESTDIR/Capture#S"
	    ""
	    "spec  "
	    " "
	    " op  xx : Nat"
	    " "
	    " op  ww : Nat -> Nat"
	    " "
	    " def ff xx0 = xx0 + xx"
	    " axiom foo is fa(xx0 : Nat) xx0 = xx0 + xx"
	    " "
	    " def g n = let xx0 = n in "
	    "           xx0 + xx"
	    " "
	    " def h n = let def ww0 n = n"
	    "           in "
	    "           ww0 n + ww n"
	    "endspec"
	    ""
	    ""))

 ("Bug 0111 : Capture of translated ops by var bindings [Repeated]"
  :show   "Capture#W"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#W"
	    ""
	    "spec  "
	    " "
	    " op  aa : Nat"
	    " "
	    " op  bb : Nat -> Nat"
	    " "
	    " def ff xx0 = xx0 + aa"
	    " axiom foo is fa(xx0 : Nat) xx0 = xx0 + aa"
	    " "
	    " def g n = let xx0 = n in "
	    "           xx0 + aa"
	    " "
	    " def h n = let def ww0 n = n"
	    "           in "
	    "           ww0 n + bb n"
	    "endspec"
	    ""
	    ""))

 )