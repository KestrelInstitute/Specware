(test-directories ".")

(test 

 ("Bug 0069 : Translate from base"
  :show   "TranslateFromBase#M" 
  :output '(";;; Elaborating spec-translation at $TESTDIR/TranslateFromBase#M"
	    ";;; Elaborating spec at $TESTDIR/TranslateFromBase#S"
	    "Errors in $TESTDIR/TranslateFromBase.sw"
	    "3.21-3.37	: Error in translation: Illegal to translate from base type : Integer"
	    ""))

 ("Bug 0069 : Translate into base"
  :show   "TranslateIntoBase#M" 
  :output '(";;; Elaborating spec-translation at $TESTDIR/TranslateIntoBase#M"
	    ";;; Elaborating spec at $TESTDIR/TranslateIntoBase#S"
	    "Errors in $TESTDIR/TranslateIntoBase.sw"
	    "7.19-7.40	: Error in translation: Illegal to translate type MyChar into pre-existing, non-alias, untranslated Char.Char"
	    ""))

 ("Bug 0069 : Morphism from base"
  :show   "MorphismFromBase#M" 
  :output '(";;; Elaborating spec-morphism at $TESTDIR/MorphismFromBase#M"
	    ";;; Elaborating spec at $TESTDIR/MorphismFromBase#S"
	    ";;; Elaborating spec at $TESTDIR/MorphismFromBase#T"
	    "Errors in $TESTDIR/MorphismFromBase.sw"
	    "6.21-6.42	: Error in morphism: Illegal to translate from base type: Integer.Integer"
	    ""))

 ("Bug 0069 : Morphism to base"
  :show   "MorphismToBase#M" 
  :output '(";;; Elaborating spec-morphism at $TESTDIR/MorphismToBase#M"
	    ";;; Elaborating spec at $TESTDIR/MorphismToBase#S"
	    ";;; Elaborating spec at $TESTDIR/MorphismToBase#T"
	    ""
	    "morphism S -> T"
	    " {type SS +-> Char}"
	    ""))

 )
