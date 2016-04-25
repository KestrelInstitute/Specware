(test-directories ".")

(test 

 ("Bug 0147 [Type Defs] : Morphisms should not be allowed to map defined types or ops into undefined ones"
  :sw  "BadMorphisms#MissingTypeDef"
  :output '(
	    ";;; Elaborating spec-morphism at $TESTDIR/BadMorphisms#MissingTypeDef"
	    ";;; Elaborating spec at $TESTDIR/BadMorphisms#A"
	    ";;; Elaborating spec at $TESTDIR/BadMorphisms#B"
	    "ERROR: in morphism: Inconsistent type def mapping for A +-> B"
	    "The domain type   A has a definition: Nat"
	    "but translates to B, which does not."
	    " found in $TESTDIR/BadMorphisms.sw"
	    "12.26-12.26"
	    ))

 ("Bug 0147 [Op Defs] : Morphisms should not be allowed to map defined types or ops into undefined ones"
  :sw  "BadMorphisms#MissingOpDef"
  :output '(
	    ";;; Elaborating spec-morphism at $TESTDIR/BadMorphisms#MissingOpDef"
	    ";;; Elaborating spec at $TESTDIR/BadMorphisms#X"
	    ";;; Elaborating spec at $TESTDIR/BadMorphisms#Y"
	    "ERROR: in morphism: Inconsistent op def mapping for f +-> g"
            "The domain op     f has a definition: fn (n: Nat) -> n + n"
	    "but translates to g, which does not."
	    " found in $TESTDIR/BadMorphisms.sw"
	    "27.24-27.24"
	    ))
 )
