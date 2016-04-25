(test-directories ".")

(test 

 ("Bug 0068 : Even numbers can be refined to odd numbers"
  :show   "EvenToOdd#O" 
  :output '((:optional "")
            ";;; Elaborating obligator at $TESTDIR/EvenToOdd#O"
            ";;; Elaborating spec-morphism at $TESTDIR/EvenToOdd#M"
            ";;; Elaborating spec at $TESTDIR/EvenToOdd#S1"
            ";;; Elaborating spec at $TESTDIR/EvenToOdd#S2"
            "ERROR: in morphism: Inconsistent type def mapping for Even +-> Odd"
            "The domain type {n : Nat | ex(m : Int) n = 2 * m}"
            "  translates to {n : Nat | ex(m : Int) n = 2 * m}"
            "   which is not {n : Nat | ex(m : Int) n = 2 * m + 1}"
            " found in $TESTDIR/EvenToOdd.sw"
            "9.13-9.14"
            (:optional "")
            ))

 )
