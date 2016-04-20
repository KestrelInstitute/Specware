(test-directories ".")

(test 

 ("Bug 0069 : Translate from base"
  :show   "TranslateFromBase#M" 
  :output '(";;; Elaborating spec-translation at $TESTDIR/TranslateFromBase#M"
	    ";;; Elaborating spec at $TESTDIR/TranslateFromBase#S"
	    "ERROR: Errors in $TESTDIR/TranslateFromBase.sw"
	    "3.21-3.33	: in translation: Illegal to translate from base type : Int"
	    ""))

 ("Bug 0069 : Translate into base"
  :show   "TranslateIntoBase#M" 
  :output '(";;; Elaborating spec-translation at $TESTDIR/TranslateIntoBase#M"
	    ";;; Elaborating spec at $TESTDIR/TranslateIntoBase#S"
	    "ERROR: Errors in $TESTDIR/TranslateIntoBase.sw"
	    "7.19-7.40	: in translation: Illegal to translate type MyChar into pre-existing, non-alias, untranslated Char.Char"
	    ""))

 ("Bug 0069 : Morphism from base"
  :show   "MorphismFromBase#M" 
  :output '(";;; Elaborating spec-morphism at $TESTDIR/MorphismFromBase#M"
	    ";;; Elaborating spec at $TESTDIR/MorphismFromBase#S"
	    ";;; Elaborating spec at $TESTDIR/MorphismFromBase#T"
	    "ERROR: Errors in $TESTDIR/MorphismFromBase.sw"
	    "6.21-6.38	: in morphism: Illegal to translate from base type: Integer.Int"
	    ""))

 ("Bug 0069 : Morphism to base"
  :show   "MorphismToBase#M" 
  :output '(";;; Elaborating spec-morphism at $TESTDIR/MorphismToBase#M"
	    ";;; Elaborating spec at $TESTDIR/MorphismToBase#S"
	    ";;; Elaborating spec at $TESTDIR/MorphismToBase#T"
	    (:optional "")
            (:alternatives
             ("morphism S -> T"
              " {type SS +-> Char}")
             "morphism S -> T {type SS +-> Char}")
	    (:optional "")
            ))

 )
