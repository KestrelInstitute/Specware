(test-directories ".")

(test 

 ("Bug 0015 : Substitute and Translate fail to update the localSorts and localOps"
  :show "subsExample#BB"
  :output '(";;; Elaborating spec-substitution at $TESTDIR/subsExample#BB"
";;; Elaborating spec at $TESTDIR/subsExample#AA"
";;; Elaborating spec at $TESTDIR/subsExample#A"
";;; Elaborating spec-morphism at $TESTDIR/subsExample#M"
";;; Elaborating spec at $TESTDIR/subsExample#B"
""
"spec  "
" import B"
" type Interval = {start : Integer, stop : Integer}"
 (:optional " ")
 " op  isEmptyInterval? : Interval -> Boolean"
" def isEmptyInterval? {start = x, stop = y} = x = y"
"endspec"
""
""
))

 )
