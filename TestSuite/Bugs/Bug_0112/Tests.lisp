(test-directories ".")

(test 

 ("Bug 0112 : Failure to translate when rule uses unqualified ref [Winner]"
  :show   "Capture#Winner"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#Winner"
	    ";;; Elaborating spec at $TESTDIR/Capture#S"
	    (:optional "") 
	    "spec  "
	    (:optional "") 
	    "type AA"
	    (:optional "") 
	    "axiom foo1 is fa(x: AA) x = x"
	    (:optional "") 
	    "type BB"
	    (:optional "") 
	    "axiom foo2 is fa(x: BB) x = x"
	    (:optional "") 
	    "axiom foo3 is fa(x: BB) x = x"
	    (:optional "") 
	    "type CC"
	    (:optional "") 
	    "type Q.C"
	    (:optional "") 
	    "axiom foo4 is fa(x: CC) x = x"
	    (:optional "") 
	    "axiom foo5 is fa(x: Q.C) x = x"
	    (:optional "") 
	    "type DD"
	    (:optional "") 
	    "type Q2.D"
	    (:optional "") 
	    "axiom foo6 is fa(x: DD) x = x"
	    (:optional "") 
	    "axiom foo7 is fa(x: Q2.D) x = x"
            (:alternatives "endspec" "end-spec")
	    (:optional "") 
	    (:optional "") 
	    ))

 ("Bug 0112 : Failure to translate when rule uses unqualified ref [Loser]"
  :show   "Capture#Loser"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Capture#Loser"
	    "ERROR: Errors in $TESTDIR/Capture.sw"
	    "26.24-26.31	: in translation: Ambiguous source type D"
	    ""))
 
 )
