(test-directories ".")

(test 

 ("Bug 0016 : An incorrect SWPATH produces no error or warning"
  :path "/loser/loser/loser"
  :output '("Warning: Directory does not exist: /loser/loser/loser"
	    "Keeping old path:"
	    (:alternatives 
	     ("$SPECWARE:/:$SPECWARE/")
	     ("$SPECWARE:.:$SPECWARE/"))))

 )
