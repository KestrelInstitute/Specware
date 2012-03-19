(test-directories ".")

(test 

 ("Bug 0015 : Substitute and Translate fail to update the localTypes and localOps"
  :show "subsExample#BB"
  :output '(";;; Elaborating spec-substitution at $TESTDIR/subsExample#BB"
	    ";;; Elaborating spec at $TESTDIR/subsExample#AA"
	    ";;; Elaborating spec at $TESTDIR/subsExample#A"
	    ";;; Elaborating spec-morphism at $TESTDIR/subsExample#M"
	    ";;; Elaborating spec at $TESTDIR/subsExample#B"
	    (:optional "")
	    "spec"
	    (:optional "")
	    "import B"
	    (:optional "")
            (:alternatives
             "type Interval = {start: Integer, stop: Integer}"
             "type Interval = {start : Integer, stop : Integer}"
             )
	    (:optional "")
	    "op  isEmptyInterval?: Interval -> Bool"
	    (:optional "")
            (:alternatives
             "def isEmptyInterval?{start = x, stop = y} = x = y"
             "def isEmptyInterval? {start = x, stop = y} = x = y"
             "def isEmptyInterval?{start = x: Integer, stop = y: Integer} = x = y"
             "def isEmptyInterval? {start = x : Integer, stop = y : Integer} = x = y"
             "def isEmptyInterval?{start = x: Integer, stop = y: Integer}: Bool = x = y"
             "def isEmptyInterval? {start = x : Integer, stop = y : Integer} : Bool = x = y"
             ("def isEmptyInterval?{start = x: Integer, stop = y: Integer}: Bool ="
              "x = y")
             ("def isEmptyInterval? {start = x : Integer, stop = y : Integer} : Bool ="
              "x = y")
             ("def isEmptyInterval?{start = x: Integer, stop = y: Integer}: Bool"
              "= x = y")
             ("def isEmptyInterval? {start = x : Integer, stop = y : Integer} : Bool"
              "= x = y")
             )
	    (:optional "")
	    (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))

 )
