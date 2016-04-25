(test-directories ".")

(test 

 ("Bug 0024 : ':swl'-ing a processed spec causes a stack overflow error "
  :sw "players"
  :output 
  '("ERROR: in specification: Name \"twoPlayers\" defined twice in file."
    "found in $TESTDIR/players.sw"
    "43.13-44.*"))

 )
