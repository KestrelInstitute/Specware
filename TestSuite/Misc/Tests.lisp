;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(cl-user::sw-init)
(format t "~%")

(format t "~&Setting swpath to ")
(cl-user::swpath (concatenate 'string (Specware::getenv "SPECWARE4") #+(or mswindows win32)";/" #-(or mswindows win32)":/"))
(format t "~2%")

(test-directories ".")

(test 
 ("NormalFib" 
  :sw "fib"
  :output '(";;; Elaborating spec at $TESTDIR/fib"
	    ""))

 ("CompileFib"
  :swll "fib"
  :output '(";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	    ""))

 ("RunFib" 
  :swe "computeFib 10"
  :swe-spec "fib"
  :value '(:|Int| . 89))

 ("twk message 1/10/03 Reused name leading to circularity."
  :sw "players#twoPlayersLisp"
  :file-goto-error '("$TESTDIR/players.sw" 43 13)
  :output '("ERROR: in specification: Name \"twoPlayers\" defined twice in file."
	    " found in $TESTDIR/players.sw"
	    "43.*-44.*"))

 ("Colimit with no sharing"
  :sw "colimit"
  :output '(";;; Elaborating spec at $TESTDIR/colimit#A"
	    ";;; Elaborating diagram-term at $TESTDIR/colimit#D"
	    ";;; Elaborating diagram-colimit at $TESTDIR/colimit#C"
	    ";;; Elaborating spec at $TESTDIR/colimit#E"
	    ""))

 ("Out of order sub-units"
  :sw "order"
  :output '(";;; Elaborating spec at $TESTDIR/order#order"
	    ";;; Elaborating spec at $TESTDIR/order#B"
	    ";;; Elaborating spec at $TESTDIR/order#C"
	    ""))

 ("Circular sub-unit"
  :sw "genC"
  :output "ERROR: Circular definition: $TESTDIR/genC#GCD")

 ("Implicit polymorphic op defined inferred"
  :sw "ImplPoly"
  :output '(";;; Elaborating spec at $TESTDIR/ImplPoly"
	    ""))

 ("Quotient Pattern"
  :swll "QuotientPattern"
  :output '(";;; Elaborating spec at $TESTDIR/QuotientPattern"
	    ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	    ""))

;;; Restrict is obsolete
;;;  ("Restrict Obligations"
;;;   :show "RestrictObligation#O"
;;;   :output '(";;; Elaborating obligator at $TESTDIR/RestrictObligation#O"
;;; 	    ";;; Elaborating spec at $TESTDIR/RestrictObligation#A"
;;; 	    ";;; Elaborating spec at $SPECWARE/Library/Base/WFO"
;;; 	    ""
;;; 	    "spec  "
;;; 	    ;" import A"
;;; 	    " import /Library/Base/WFO"
;;; 	    " "
;;; 	    " op  nonNeg? : Integer -> Bool"
;;; 	    (:optional "")
;;; 	    " op  f : {p : (Integer * Integer) | p.1 > -(p.2)} -> Nat"
;;; 	    " conjecture f_Obligation_subtype is "
;;; 	    "    fa(y : Integer, x : Integer) x > - y => nonNeg?(x + y)"
;;; 	    " conjecture f_Obligation_subtype0 is "
;;; 	    "    fa(y : Integer, x : Integer) "
;;; 	    "     x > - y && nonNeg?(x + y) => natural?(x + y)"
;;; 	    " "
;;; 	    " def f (x, y) = restrict(nonNeg?)(x + y)"
;;; 	    "end-spec"
;;; 	    ""
;;; 	    ""))

 ("libtest" 
  :swll "libtest"
  :output '(";;; Elaborating spec at $TESTDIR/libtest"
            ";;; Elaborating spec at $SPECWARE/Library/Legacy/Utilities/System"
	    ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	    ""))

 ("Prettyprint Parens"
  :show "PP"
  :output '(";;; Elaborating spec at $TESTDIR/PP"
	    (:optional "")
	    "spec  "
	    (:optional "")
	    " type Injection1(a, b) = ((a -> b) | Function.injective?)"
	    (:optional "")
	    " type T0 =  | Foo | Fum"
	    (:optional "")
	    " type T = (T0 | truep)"
	    (:optional "")
	    " type T1 = {x: T0 | true}"
	    (:optional "")
	    " type T2 = ((T * T1) | truep)"
	    (:optional "")
	    " op [a] truep: a -> Bool"
	    (:optional "")
	    " axiom List.induction1 is [a] "
	    "    fa(p: List(a) -> Bool) "
            "   p [] && (fa(x: a, l: List(a)) (p l => p (x :: l) => (fa(l: List(a)) p l)))"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 ("swe Pattern A"
  :swe "v"
  :swe-spec "SubstRestrictedPat#A"
  :value '(:|Int| . 3))

 ("Simplify Restrict Pattern A"
  :swll "SubstRestrictedPat#A"
  :output '((:optional ";;; Elaborating spec at $TESTDIR/SubstRestrictedPat#A")
	    ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	    (:optional "")))

 ("el Pattern A"
  :lisp "(SW-User::f '(5))"
  :value 5)

 ("swe Pattern B"
  :swe "(g [3])"
  :swe-spec "SubstRestrictedPat#B"
  :value '(:|Int| . 3))

 ("Simplify Restrict Pattern B"
  :swll "SubstRestrictedPat#B"
  :output '((:optional ";;; Elaborating spec at $TESTDIR/SubstRestrictedPat#B")
	    ";;; Generating lisp file /tmp*/lgen_lisp_tmp.lisp"
	    (:optional "")))

 ("el Pattern B"
  :lisp "(SW-User::g '(5))"
  :value 5)
 )

