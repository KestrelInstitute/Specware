(test-directories ".")

(test 

 ("Bug 0113 : Translate should be mono: {type X +-> Y}"
  :show   "Collision#T1"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T1"
	    ";;; Elaborating spec at $TESTDIR/Collision#S"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {X +-> Y}"
  :show   "Collision#T2"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T2"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {type X +-> Z, type Y +-> Z}"
  :show   "Collision#T3"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T3"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {X +-> Z, Y +-> Z}"
  :show   "Collision#T4"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T4"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {op f +-> g}"
  :show   "Collision#T5"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T5"
	    "<some  kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {f +-> g}"
  :show   "Collision#T6"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T6"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {op f +-> h, op g +-> h}"
  :show   "Collision#T7"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T7"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {f +-> h, g +-> h}"
  :show   "Collision#T8"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T8"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {A._ +-> B._}"
  :show   "Collision#T9"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T9"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {A._ +-> C._, B._ +-> C._}"
  :show   "Collision#T10"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T10"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {D._ +-> E._}"
  :show   "Collision#T11"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T11"
	    "<some kind of error message>"
	    ""))

 ("Bug 0113 : Translate should be mono: {D._ +-> F._, E._ +-> F._}"
  :show   "Collision#T12"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#T12"
	    "<some kind of error message>"
	    ""))


 )