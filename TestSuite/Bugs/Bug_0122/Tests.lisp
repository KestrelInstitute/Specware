(test-directories ".")

(test 

 ("Bug 0122 : Two constants might be equal [f = f]"
  :swe-spec  "TwoConstants"
  :swe       "f = f"
  :value    '(:|Bool| . t)
  :output '(
	    ";;; Elaborating spec at $TESTDIR/TwoConstants"
	    ""
	    ""))

 ("Bug 0122 : Two constants might be equal [f = g]"
  :swe-spec  "TwoConstants"
  :swe       "(f = g) ~= false"
  ;; Note: equalTerm? ignores locations, so in the pseudo-term for :value, 
  ;; all locations are nil.  (Hence they not are printed at the ends 
  ;; of the expressions they appear in.)
  :value     '(:|Apply|
	      . #((:|Fun|
		   . #((:|NotEquals|)
		       (:|Arrow| . #((:|Product| (("1" :|Boolean|) ("2" :|Boolean|))) 
				     (:|Boolean|))))) 
		  (:|Record|
		   (("1" :|Apply|
		     . #((:|Fun|
			   . #((:|Equals|)
			       (:|Arrow|
				. #((:|Product|
				     (("1" :|Base| . #((:|Qualified| "Nat" . "Nat") NIL))
				      ("2" :|Base| . #((:|Qualified| "Nat" . "Nat") NIL))))
				    (:|Boolean|)))))
			 (:|Record|
			  (("1" :|Fun|
			    . #((:|Op| (:|Qualified| "<unqualified>" . "f") :|Unspecified|)
				(:|Base| . #((:|Qualified| "Nat" . "Nat") NIL))))
			   ("2" :|Fun|
			    . #((:|Op| (:|Qualified| "<unqualified>" . "g") :|Unspecified|)
				(:|Base| . #((:|Qualified| "Nat" . "Nat") NIL))))))
			 ))
		    ("2" :|Fun| . #((:|Bool|) (:|Boolean|)))))))
  :value-predicate #'(lambda (x y) 
		       (and (equal (car x) :|Unevaluated|)
			    (METASLANG::equalTerm?-2 (cdr x) y)))
  :output '(""
	    ""))


 )