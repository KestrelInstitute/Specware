(test-directories ".")

(test 

 ;; bad translations...

 ("Bug 0113 : Translate should be mono: Bad1: {type X +-> Y}"
  :show   "Collision#Bad1"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad1"
	    ";;; Elaborating spec at $TESTDIR/Collision#S"
	    "Errors in $TESTDIR/Collision.sw"
	    "23.22-23.35	: Error in translation: Illegal to translate type X into pre-existing, non-alias, untranslated Y"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad2: {X +-> Y}"
  :show   "Collision#Bad2"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad2"
	    "Errors in $TESTDIR/Collision.sw"
	    "24.22-24.30	: Error in translation: Illegal to translate type X into pre-existing, non-alias, untranslated Y"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad3: {type X +-> Z, type Y +-> Z}"
  :show   "Collision#Bad3"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad3"
	    "Errors in $TESTDIR/Collision.sw"
	    "27.37-27.48	: Error in translation: Illegal to translate both type Y and type X into Z"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad4: {X +-> Z, Y +-> Z}"
  :show   "Collision#Bad4"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad4"
	    "Errors in $TESTDIR/Collision.sw"
	    "28.32-28.38	: Error in translation: Illegal to translate both type Y and type X into Z"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad5: {op f +-> g}"
  :show   "Collision#Bad5"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad5"
	    "Errors in $TESTDIR/Collision.sw"
	    "32.22-32.33	: Error in translation: Illegal to translate op f into pre-existing, non-alias, untranslated g"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad6: {f +-> g}"
  :show   "Collision#Bad6"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad6"
	    "Errors in $TESTDIR/Collision.sw"
	    "33.22-33.30	: Error in translation: Illegal to translate op f into pre-existing, non-alias, untranslated g"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad7: {op f +-> h, op g +-> h}"
  :show   "Collision#Bad7"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad7"
	    "Errors in $TESTDIR/Collision.sw"
	    "36.35-36.44	: Error in translation: Illegal to translate both op g and op f into h"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad8: {f +-> h, g +-> h}"
  :show   "Collision#Bad8"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad8"
	    "Errors in $TESTDIR/Collision.sw"
	    "37.32-37.38	: Error in translation: Illegal to translate both op g and op f into h"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad9: {A._ +-> B._}"
  :show   "Collision#Bad9"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad9"
	    "Errors in $TESTDIR/Collision.sw"
	    "41.22-41.34	: Error in translation: Illegal to translate type A.T into pre-existing, non-alias, untranslated B.T"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad10: {A._ +-> C._, B._ +-> C._}"
  :show   "Collision#Bad10"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad10"
	    "Errors in $TESTDIR/Collision.sw"
	    "45.37-45.47	: Error in translation: Illegal to translate both type B.T and type A.T into C.T"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad11: {D._ +-> E._}"
  :show   "Collision#Bad11"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad11"
	    "Errors in $TESTDIR/Collision.sw"
	    "49.23-49.35	: Error in translation: Illegal to translate op D.m into pre-existing, non-alias, untranslated E.m"
	    ""))

 ("Bug 0113 : Translate should be mono: Bad12: {D._ +-> F._, E._ +-> F._}"
  :show   "Collision#Bad12"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad12"
	    "Errors in $TESTDIR/Collision.sw"
	    "53.37-53.47	: Error in translation: Illegal to translate both op E.m and op D.m into F.m"
	    ""))

 ;; good, but tricky, translations...

 ("Bug 0113 : Translate should be mono: Ok1: {X +-> Y, Y +-> Z}"
  :show   "Collision#Ok1"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok1"
	    ""
	    "spec  "
	    " type Y"
	    " type Z"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : Y"
	    " "
	    " op  f : Y"
	    " "
	    " op  E.m : Z"
	    " "
	    " op  D.m : Z"
	    " "
	    " op  q : Z"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok2: {Y +-> Z, X +-> Y}"
  :show   "Collision#Ok2"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok2"
	    ""
	    "spec  "
	    " type Y"
	    " type Z"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : Y"
	    " "
	    " op  f : Y"
	    " "
	    " op  E.m : Z"
	    " "
	    " op  D.m : Z"
	    " "
	    " op  q : Z"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok3: {X +-> Y, Y +-> X}"
  :show   "Collision#Ok3"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok3"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : Y"
	    " "
	    " op  f : Y"
	    " "
	    " op  E.m : X"
	    " "
	    " op  D.m : X"
	    " "
	    " op  q : X"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok4: {Y +-> X, X +-> Y}"
  :show   "Collision#Ok4"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok4"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : Y"
	    " "
	    " op  f : Y"
	    " "
	    " op  E.m : X"
	    " "
	    " op  D.m : X"
	    " "
	    " op  q : X"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok5: {p +-> q, q +-> r}"
  :show   "Collision#Ok5"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok5"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  r : Y"
	    " "
	    " op  g : X"
	    " "
	    " op  f : X"
	    " "
	    " op  E.m : Y"
	    " "
	    " op  D.m : Y"
	    " "
	    " op  q : X"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok6: {q +-> r, p +-> q}"
  :show   "Collision#Ok6"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok6"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  r : Y"
	    " "
	    " op  g : X"
	    " "
	    " op  f : X"
	    " "
	    " op  E.m : Y"
	    " "
	    " op  D.m : Y"
	    " "
	    " op  q : X"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok7: {p +-> q, q +-> p}"
  :show   "Collision#Ok7"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok7"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : X"
	    " "
	    " op  f : X"
	    " "
	    " op  E.m : Y"
	    " "
	    " op  D.m : Y"
	    " "
	    " op  q : X"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ("Bug 0113 : Translate should be mono: Ok8: {q +-> p, p +-> q}"
  :show   "Collision#Ok8"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok8"
	    ""
	    "spec  "
	    " type Y"
	    " type X"
	    " type B.T"
	    " type A.T"
	    " "
	    " op  g : X"
	    " "
	    " op  f : X"
	    " "
	    " op  E.m : Y"
	    " "
	    " op  D.m : Y"
	    " "
	    " op  q : X"
	    " "
	    " op  p : Y"
	    "endspec"
	    ""
	    ""))

 ;; translations of synonyms

 ("Bug 0113 : Translate should be mono: colimit"
  :show "TypeColimits#C"
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/TypeColimits#C"
	    ";;; Elaborating diagram-term at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#R"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#S"
	    ";;; Elaborating spec-morphism at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#T"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XX_YY_ZZ"
  :show "TypeColimits#T_XX_YY_ZZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XX_YY_ZZ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {XX, YY, ZZ}")
	     (" type {XX, ZZ, YY}")
	     (" type {YY, XX, ZZ}")
	     (" type {YY, ZZ, XX}")
	     (" type {ZZ, XX, YY}")
	     (" type {ZZ, YY, XX}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY"
  :show "TypeColimits#T_XY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ"
  :show "TypeColimits#T_XZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YX"
  :show "TypeColimits#T_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YZ"
  :show "TypeColimits#T_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_ZX"
  :show "TypeColimits#T_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y}")
	     (" type {Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_ZY"
  :show "TypeColimits#T_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y}")
	     (" type {Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YX"
  :show "TypeColimits#T_XY_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YZ"
  :show "TypeColimits#T_XY_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YP"
  :show "TypeColimits#T_XY_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y, Z}")
	     (" type {P, Z, Y}")
	     (" type {Y, P, Z}")
	     (" type {Y, Z, P}")
	     (" type {Z, P, Y}")
	     (" type {Z, Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_ZX"
  :show "TypeColimits#T_XY_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y}")
	     (" type {Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_ZY"
  :show "TypeColimits#T_XY_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZY"
	    ""
	    "spec  "
	    " type Y"
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_ZP"
  :show "TypeColimits#T_XY_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YX"
  :show "TypeColimits#T_XZ_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YZ"
  :show "TypeColimits#T_XZ_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ"
	    ""
	    "spec  "
	    " type Z"
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YP"
  :show "TypeColimits#T_XZ_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Z}")
	     (" type {Z, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_ZX"
  :show "TypeColimits#T_XZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_ZY"
  :show "TypeColimits#T_XZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_ZP"
  :show "TypeColimits#T_XZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y, Z}")
	     (" type {P, Z, Y}")
	     (" type {Y, P, Z}")
	     (" type {Y, Z, P}")
	     (" type {Z, P, Y}")
	     (" type {Z, Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YX"
  :show "TypeColimits#T_XP_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Z}")
	     (" type {P, Z, X}")
	     (" type {X, P, Z}")
	     (" type {X, Z, P}")
	     (" type {Z, P, X}")
	     (" type {Z, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YZ"
  :show "TypeColimits#T_XP_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Z}")
	     (" type {Z, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YP"
  :show "TypeColimits#T_XP_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Z}")
	     (" type {Z, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ"
  :show "TypeColimits#T_XP_YQ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q, Z}")
	     (" type {P, Z, Q}")
	     (" type {Q, P, Z}")
	     (" type {Q, Z, P}")
	     (" type {Z, P, Q}")
	     (" type {Z, Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_ZX"
  :show "TypeColimits#T_XP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Y}")
	     (" type {P, Y, X}")
	     (" type {X, P, Y}")
	     (" type {X, Y, P}")
	     (" type {Y, P, X}")
	     (" type {Y, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_ZY"
  :show "TypeColimits#T_XP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_ZP"
  :show "TypeColimits#T_XP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZP"
	    ""
	    "spec  "
	    (:alternatives 
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_ZR"
  :show "TypeColimits#T_XP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, Y}")
	     (" type {P, Y, R}")
	     (" type {R, P, Y}")
	     (" type {R, Y, P}")
	     (" type {Y, P, R}")
	     (" type {Y, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YX_ZX"
  :show "TypeColimits#T_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZX"
	    ""
	    "spec  "
	    " type X"
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YX_ZY"
  :show "TypeColimits#T_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y}")
	     (" type {Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YX_ZP"
  :show "TypeColimits#T_YX_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YZ_ZX"
  :show "TypeColimits#T_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZX"
	    ""
	    "spec  "
	    (:alternatives 
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YZ_ZY"
  :show "TypeColimits#T_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YZ_ZP"
  :show "TypeColimits#T_YZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Z}")
	     (" type {P, Z, X}")
	     (" type {X, P, Z}")
	     (" type {X, Z, P}")
	     (" type {Z, P, X}")
	     (" type {Z, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YP_ZX"
  :show "TypeColimits#T_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YP_ZY"
  :show "TypeColimits#T_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Y}")
	     (" type {P, Y, X}")
	     (" type {X, P, Y}")
	     (" type {X, Y, P}")
	     (" type {Y, P, X}")
	     (" type {Y, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YP_ZP"
  :show "TypeColimits#T_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_YP_ZR"
  :show "TypeColimits#T_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, X}")
	     (" type {P, X, R}")
	     (" type {R, P, X}")
	     (" type {R, X, P}")
	     (" type {X, P, R}")
	     (" type {X, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YX_ZX"
  :show "TypeColimits#T_XY_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, X}")
	     (" type {X, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YX_ZY"
  :show "TypeColimits#T_XY_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y}")
	     (" type {Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YX_ZR"
  :show "TypeColimits#T_XY_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {R, X, Y}")
	     (" type {R, Y, X}")
	     (" type {X, R, Y}")
	     (" type {X, Y, R}")
	     (" type {Y, R, X}")
	     (" type {Y, X, R}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YZ_ZX"
  :show "TypeColimits#T_XY_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YZ_ZY"
  :show "TypeColimits#T_XY_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YZ_ZR"
  :show "TypeColimits#T_XY_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {R, Y, Z}")
	     (" type {R, Z, Y}")
	     (" type {Y, R, Z}")
	     (" type {Y, Z, R}")
	     (" type {Z, R, Y}")
	     (" type {Z, Y, R}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YP_ZX"
  :show "TypeColimits#T_XY_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Y}")
	     (" type {P, Y, X}")
	     (" type {X, P, Y}")
	     (" type {X, Y, P}")
	     (" type {Y, P, X}")
	     (" type {Y, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YP_ZY"
  :show "TypeColimits#T_XY_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YP_ZP"
  :show "TypeColimits#T_XY_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XY_YP_ZR"
  :show "TypeColimits#T_XY_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, Y}")
	     (" type {P, Y, R}")
	     (" type {R, P, Y}")
	     (" type {R, Y, P}")
	     (" type {Y, P, R}")
	     (" type {Y, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YX_ZX"
  :show "TypeColimits#T_XZ_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YX_ZY"
  :show "TypeColimits#T_XZ_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Y, Z}")
	     (" type {X, Z, Y}")
	     (" type {Y, X, Z}")
	     (" type {Y, Z, X}")
	     (" type {Z, X, Y}")
	     (" type {Z, Y, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YX_ZR"
  :show "TypeColimits#T_XZ_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {R, X, Z}")
	     (" type {R, Z, X}")
	     (" type {X, R, Z}")
	     (" type {X, Z, R}")
	     (" type {Z, R, X}")
	     (" type {Z, X, R}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YZ_ZX"
  :show "TypeColimits#T_XZ_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {X, Z}")
	     (" type {Z, X}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YZ_ZY"
  :show "TypeColimits#T_XZ_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {Y, Z}")
	     (" type {Z, Y}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YZ_ZR"
  :show "TypeColimits#T_XZ_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {R, Z}")
	     (" type {Z, R}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YP_ZX"
  :show "TypeColimits#T_XZ_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Z}")
	     (" type {P, Z, X}")
	     (" type {X, P, Z}")
	     (" type {X, Z, P}")
	     (" type {Z, P, X}")
	     (" type {Z, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YP_ZY"
  :show "TypeColimits#T_XZ_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y, Z}")
	     (" type {P, Z, Y}")
	     (" type {Y, P, Z}")
	     (" type {Y, Z, P}")
	     (" type {Z, P, Y}")
	     (" type {Z, Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YP_ZP"
  :show "TypeColimits#T_XZ_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Z}")
	     (" type {Z, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XZ_YP_ZR"
  :show "TypeColimits#T_XZ_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, Z}")
	     (" type {P, Z, R}")
	     (" type {R, P, Z}")
	     (" type {R, Z, P}")
	     (" type {Z, P, R}")
	     (" type {Z, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YX_ZX"
  :show "TypeColimits#T_XP_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YX_ZY"
  :show "TypeColimits#T_XP_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Y}")
	     (" type {P, Y, X}")
	     (" type {X, P, Y}")
	     (" type {X, Y, P}")
	     (" type {Y, P, X}")
	     (" type {Y, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YX_ZP"
  :show "TypeColimits#T_XP_YX_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YX_ZR"
  :show "TypeColimits#T_XP_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, X}")
	     (" type {P, X, R}")
	     (" type {R, P, X}")
	     (" type {R, X, P}")
	     (" type {X, P, R}")
	     (" type {X, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YZ_ZX"
  :show "TypeColimits#T_XP_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X, Z}")
	     (" type {P, Z, X}")
	     (" type {X, P, Z}")
	     (" type {X, Z, P}")
	     (" type {Z, P, X}")
	     (" type {Z, X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YZ_ZY"
  :show "TypeColimits#T_XP_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y, Z}")
	     (" type {P, Z, Y}")
	     (" type {Y, P, Z}")
	     (" type {Y, Z, P}")
	     (" type {Z, P, Y}")
	     (" type {Z, Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YZ_ZP"
  :show "TypeColimits#T_XP_YZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Z}")
	     (" type {Z, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YZ_ZR"
  :show "TypeColimits#T_XP_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R, Z}")
	     (" type {P, Z, R}")
	     (" type {R, P, Z}")
	     (" type {R, Z, P}")
	     (" type {Z, P, R}")
	     (" type {Z, R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YP_ZX"
  :show "TypeColimits#T_XP_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, X}")
	     (" type {X, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YP_ZY"
  :show "TypeColimits#T_XP_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Y}")
	     (" type {Y, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YP_ZP"
  :show "TypeColimits#T_XP_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZP"
	    ""
	    "spec  "
	    " type P"
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YP_ZR"
  :show "TypeColimits#T_XP_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, R}")
	     (" type {R, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ_ZX"
  :show "TypeColimits#T_XP_YQ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZX"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q, X}")
	     (" type {P, X, Q}")
	     (" type {Q, P, X}")
	     (" type {Q, X, P}")
	     (" type {X, P, Q}")
	     (" type {X, Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ_ZY"
  :show "TypeColimits#T_XP_YQ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZY"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q, Y}")
	     (" type {P, Y, Q}")
	     (" type {Q, P, Y}")
	     (" type {Q, Y, P}")
	     (" type {Y, P, Q}")
	     (" type {Y, Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ_ZP"
  :show "TypeColimits#T_XP_YQ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZP"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q}")
	     (" type {Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ_ZQ"
  :show "TypeColimits#T_XP_YQ_ZQ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZQ"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q}")
	     (" type {Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 ("Bug 0113:  Translate should be mono: T_XP_YQ_ZR"
  :show "TypeColimits#T_XP_YQ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZR"
	    ""
	    "spec  "
	    (:alternatives
	     (" type {P, Q, R}")
	     (" type {P, R, Q}")
	     (" type {Q, P, R}")
	     (" type {Q, R, P}")
	     (" type {R, P, Q}")
	     (" type {R, Q, P}"))
	    "endspec"
	    ""
	    "")
  )

 )