(test-directories ".")

(test 

 ("Bug 0147 [Type Defs] : Morphisms should not be allowed to map defined types or ops into undefined ones"
  :sw  "BadMorphisms#MissingTypeDef"
  :output '(";;; Elaborating spec-morphism at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#MissingTypeDef"
	    ";;; Elaborating spec at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#A"
	    ";;; Elaborating spec at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#B"
	    "Error in morphism: Inconsistent type def mapping for A +-> B"
	    "The domain type   A has a definition: Nat"
	    "but translates to B, which does not."
	    " found in /usr/home/kestrel/mcdonald/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms.sw"
	    "12.26-12.26"
	    ""))


 ("Bug 0147 [Op Defs] : Morphisms should not be allowed to map defined types or ops into undefined ones"
  :sw  "BadMorphisms#MissingOpDef"
  :output '(
	    ";;; Elaborating spec-morphism at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#MissingOpDef"
	    ";;; Elaborating spec at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#X"
	    ";;; Elaborating spec at ~/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms#Y"
	    "Error in morphism: Inconsistent op def mapping for f +-> g"
	    "The domain op     f has a definition: (fn n -> n + n)"
	    "but translates to g, which does not."
	    " found in /usr/home/kestrel/mcdonald/Work/Generic/Specware4/TestSuite/Bugs/Bug_0147/BadMorphisms.sw"
	    "27.24-27.24"
	    ""))
 )
