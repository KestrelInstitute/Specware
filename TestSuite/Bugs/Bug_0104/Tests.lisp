(test-directories ".")

(test 

 ("Bug 0104 : Erroneous code for non-constructive expression."
  :swe-spec "NonConstructive"
  :swe      "notFalse"
  :value    '(:|Bool| . T)
  )
 
 )
