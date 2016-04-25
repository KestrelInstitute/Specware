(test-directories ".")

(test 

 ("Bug 0067 : Signature constraints in spec morphism are not checked"
  :show   "CheckSignature#M" 
  :output '((:optional "")
            ";;; Elaborating spec-morphism at $TESTDIR/CheckSignature#M"
            ";;; Elaborating spec at $TESTDIR/CheckSignature#S1"
            ";;; Elaborating spec at $TESTDIR/CheckSignature#S2"
            "ERROR: in morphism: Inconsistent op type mapping for f +-> g"
            "The domain type A"
            "  translates to B"
            "   which is not C"
            " found in $TESTDIR/CheckSignature.sw"
            "14.13-14.14"
            (:optional "")
            ))

 )
