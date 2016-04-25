(test-directories ".")

(test 

 ("Bug 0022 : Redefined ops processed without giving error message [OpDef]."
  :show "RedefinedOp#OpDef"
  :output '(";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDef"
            (:optional "")
            "spec"
            (:optional "")
            (:alternatives
             "op  f: Nat"
             "op  f : Nat"
             )
            (:alternatives
             " def f: Nat = 3"
             " def f : Nat = 3"
             " def f = 3")
            (:optional "")
	    (:alternatives "endspec" "end-spec")
            (:optional "")
            (:optional "")
            ))

 ("Bug 0022 : Redefined ops processed without giving error message [DefOp]"
  :sw "RedefinedOp#DefOp"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/RedefinedOp#DefOp"
            "ERROR: in specification: Operator f has been redeclared"
            " from 3"
            "   to <anyterm>: Nat"
            " found in $TESTDIR/RedefinedOp.sw"
            "8.1-8.10"
            (:optional "")
            ))

 ("Bug 0022 : Redefined ops processed without giving error message [DefDef]"
  :sw "RedefinedOp#DefDef"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/RedefinedOp#DefDef"
            "ERROR: in specification: Operator f has been redefined"
            " from 3"
            "   to 3"
            " found in $TESTDIR/RedefinedOp.sw"
            "13.1-13.9"
            (:optional "")
            ))

 ("Bug 0022 : Redefined ops processed without giving error message [OpOp]"
  :sw "RedefinedOp#OpOp"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpOp"
            "ERROR: in specification: Operator f has been redeclared"
            " from Nat"
            "   to Nat"
            " found in $TESTDIR/RedefinedOp.sw"
            "18.1-18.10"
            (:optional "")
            ))

 ("Bug 0022 : Redefined ops processed without giving error message [OpDefOp]"
  :sw "RedefinedOp#OpDefOp"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDefOp"
            "ERROR: in specification: Operator f has been redeclared"
            " from 3: Nat"
            "   to <anyterm>: Nat"
            " found in $TESTDIR/RedefinedOp.sw"
            "24.1-24.10"
            (:optional "")
            ))

 ("Bug 0022 : Redefined ops processed without giving error message [OpDefDef]"
  :sw "RedefinedOp#OpDefDef"
  :output '((:optional "")
            ";;; Elaborating spec at $TESTDIR/RedefinedOp#OpDefDef"
            "ERROR: in specification: Operator f has been redefined"
            " from 3: Nat"
            "   to 3"
            " found in $TESTDIR/RedefinedOp.sw"
            "30.1-30.9"
            (:optional "")
            ))

 )
