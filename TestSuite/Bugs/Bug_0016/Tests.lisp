(test-directories ".")

(test 

 ("Bug 0016 : An incorrect SWPATH produces no error or warning"
  :path "/loser/loser/loser"
  :output '((:alternatives 
	     "Warning: Directory does not exist: /loser/loser/loser"
	     "Warning: Directory does not exist: /loser/loser/loser/")
	    "Keeping old path:"
	    (:alternatives 
	     "/:$SPECWARE/"
	     "$SPECWARE:.:$SPECWARE/"
	     "$SPECWARE/:./:/"
	     "$SPECWARE/:./"
	     "$SPECWARE/:/"
	     "$SPECWARE/"
	     "/:./:$SPECWARE/"
	     )))

 )
