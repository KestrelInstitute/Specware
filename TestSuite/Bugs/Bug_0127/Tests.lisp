(test-directories ".")

(test 

  ("Bug 0127 [A] : Specware can't infer morphism mapping T +-> Q.T automatically"
   :show  "M#M_1_1"
   :output '(
	     (:optional ";;; Elaborating spec-morphism at $TESTDIR/M#M_1_1")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Dom")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Cod_1_1")
	     (:optional "")
             (:alternatives
              "morphism Dom -> Cod_1_1 {type T +-> Q.T,op f +-> Q.f}"
              ("morphism Dom -> Cod_1_1"
               "                    {type T +-> Q.T,"
               "                      op f +-> Q.f}"))
	     (:optional "")
	     (:optional "")
	     ))

  ("Bug 0127 [B] : Specware can't infer morphism mapping T +-> Q.T automatically"
   :show  "M#M_2_1"
   :output '(
	     (:optional ";;; Elaborating spec-morphism at $TESTDIR/M#M_2_1")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Dom")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Cod_2_1")
	     (:alternatives 
	      "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Q.T, Z.T}"
	      "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Z.T, Q.T}")
	     " found in no position"
	     (:optional "")
	     (:optional "")
	     ))

  ("Bug 0127 [C] : Specware can't infer morphism mapping T +-> Q.T automatically"
   :show  "M#M_1_2"
   :output '(
	     (:optional ";;; Elaborating spec-morphism at $TESTDIR/M#M_1_2")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Dom")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Cod_1_2")
	     (:alternatives 
	      "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Q.f, Z.f}"
	      "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Z.f, Q.f}")
	     " found in no position"
	     (:optional "")
	     (:optional "")
	     ))

  ("Bug 0127 [D] : Specware can't infer morphism mapping T +-> Q.T automatically"
   :show  "M#M_2_2"
   :output '(
	     (:optional ";;; Elaborating spec-morphism at $TESTDIR/M#M_2_2")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Dom")
	     (:optional ";;; Elaborating spec at $TESTDIR/M#Cod_2_2")
	     (:alternatives 
	      "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Q.T, Z.T}"
	      "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Z.T, Q.T}"
	      "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Q.f, Z.f}"
	      "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Z.f, Q.f}")
	     " found in no position"
	     ;;
	     (:optional 
	      (:alternatives 
	       "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Q.T, Z.T}"
	       "ERROR: in morphism: No unique mapping for type T -- found 2 candidates: {Z.T, Q.T}"
	       "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Q.f, Z.f}"
	       "ERROR: in morphism: No unique mapping for op f -- found 2 candidates: {Z.f, Q.f}")
	      " found in no position")
	     ;;
	     (:optional "")
	     (:optional "")
	     ))
  )
