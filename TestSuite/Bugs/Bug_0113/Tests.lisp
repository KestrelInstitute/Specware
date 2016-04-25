(test-directories ".")

(test 

 ;; bad translations...

 ("Bug 0113 : Translate should be monic: Bad1: {type X +-> Y}"
  :show   "Collision#Bad1"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad1"
	    ";;; Elaborating spec at $TESTDIR/Collision#S"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "23.22-23.35	: in translation: Illegal to translate type X into pre-existing, non-alias, untranslated Y"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad2: {X +-> Y}"
  :show   "Collision#Bad2"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad2"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "24.22-24.30	: in translation: Illegal to translate type X into pre-existing, non-alias, untranslated Y"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad3: {type X +-> Z, type Y +-> Z}"
  :show   "Collision#Bad3"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad3"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "27.37-27.48	: in translation: Illegal to translate both type Y and type X into Z"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad4: {X +-> Z, Y +-> Z}"
  :show   "Collision#Bad4"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad4"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "28.32-28.38	: in translation: Illegal to translate both type Y and type X into Z"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad5: {op f +-> g}"
  :show   "Collision#Bad5"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad5"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "32.22-32.33	: in translation: Illegal to translate op f into pre-existing, non-alias, untranslated g"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad6: {f +-> g}"
  :show   "Collision#Bad6"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad6"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "33.22-33.30	: in translation: Illegal to translate op f into pre-existing, non-alias, untranslated g"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad7: {op f +-> h, op g +-> h}"
  :show   "Collision#Bad7"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad7"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "36.35-36.44	: in translation: Illegal to translate both op g and op f into h"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad8: {f +-> h, g +-> h}"
  :show   "Collision#Bad8"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad8"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "37.32-37.38	: in translation: Illegal to translate both op g and op f into h"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad9: {A._ +-> B._}"
  :show   "Collision#Bad9"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad9"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "41.22-41.34	: in translation: Illegal to translate type A.T into pre-existing, non-alias, untranslated B.T"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad10: {A._ +-> C._, B._ +-> C._}"
  :show   "Collision#Bad10"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad10"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "45.37-45.47	: in translation: Illegal to translate both type B.T and type A.T into C.T"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad11: {D._ +-> E._}"
  :show   "Collision#Bad11"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad11"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "49.23-49.35	: in translation: Illegal to translate op D.m into pre-existing, non-alias, untranslated E.m"
	    ""))

 ("Bug 0113 : Translate should be monic: Bad12: {D._ +-> F._, E._ +-> F._}"
  :show   "Collision#Bad12"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Bad12"
	    "ERROR: Errors in $TESTDIR/Collision.sw"
	    "53.37-53.47	: in translation: Illegal to translate both op E.m and op D.m into F.m"
	    ""))

 ;; good, but tricky, translations...

 ("Bug 0113 : Translate should be monic: Ok1: {X +-> Y, Y +-> Z}"
  :show   "Collision#Ok1"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok1"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Y"
            (:optional "")
	    "type Z"
	    (:optional "")
	    " op  f: Y"
            (:optional "")
	    " op  g: Y"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    " op  q: Z"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Z"
            (:optional "")
	    " op  E.m: Z"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok2: {Y +-> Z, X +-> Y}"
  :show   "Collision#Ok2"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok2"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Y"
            (:optional "")
	    "type Z"
	    (:optional "")
	    " op  f: Y"
            (:optional "")
	    " op  g: Y"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    " op  q: Z"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Z"
            (:optional "")
	    " op  E.m: Z"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok3: {X +-> Y, Y +-> X}"
  :show   "Collision#Ok3"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok3"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Y"
            (:optional "")
	    "type X"
	    (:optional "")
	    " op  f: Y"
            (:optional "")
	    " op  g: Y"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: X"
            (:optional "")
	    " op  E.m: X"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok4: {Y +-> X, X +-> Y}"
  :show   "Collision#Ok4"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok4"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Y"
            (:optional "")
	    "type X"
	    (:optional "")
	    " op  f: Y"
            (:optional "")
	    " op  g: Y"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: X"
            (:optional "")
	    " op  E.m: X"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok5: {p +-> q, q +-> r}"
  :show   "Collision#Ok5"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok5"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type X"
            (:optional "")
	    "type Y"
	    (:optional "")
	    " op  f: X"
            (:optional "")
	    " op  g: X"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    " op  r: Y"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Y"
            (:optional "")
	    " op  E.m: Y"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok6: {q +-> r, p +-> q}"
  :show   "Collision#Ok6"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok6"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type X"
            (:optional "")
	    "type Y"
	    (:optional "")
	    " op  f: X"
            (:optional "")
	    " op  g: X"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    " op  r: Y"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Y"
            (:optional "")
	    " op  E.m: Y"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok7: {p +-> q, q +-> p}"
  :show   "Collision#Ok7"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok7"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type X"
            (:optional "")
	    "type Y"
	    (:optional "")
	    " op  f: X"
            (:optional "")
	    " op  g: X"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Y"
            (:optional "")
	    " op  E.m: Y"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ("Bug 0113 : Translate should be monic: Ok8: {q +-> p, p +-> q}"
  :show   "Collision#Ok8"
  :output '(";;; Elaborating spec-translation at $TESTDIR/Collision#Ok8"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type X"
            (:optional "")
	    "type Y"
	    (:optional "")
	    " op  f: X"
            (:optional "")
	    " op  g: X"
            (:optional "")
	    " op  q: X"
            (:optional "")
	    " op  p: Y"
            (:optional "")
	    "type A.T"
            (:optional "")
	    "type B.T"
	    (:optional "")
	    " op  D.m: Y"
            (:optional "")
	    " op  E.m: Y"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")))

 ;; translations of synonyms

 ("Bug 0113 : Translate should be monic: colimit"
  :show "TypeColimits#C"
  :output '(";;; Elaborating diagram-colimit at $TESTDIR/TypeColimits#C"
	    ";;; Elaborating diagram-term at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec-morphism at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#R"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#S"
	    ";;; Elaborating spec-morphism at $TESTDIR/TypeColimits#D"
	    ";;; Elaborating spec at $TESTDIR/TypeColimits#T"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XX_YY_ZZ"
  :show "TypeColimits#T_XX_YY_ZZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XX_YY_ZZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {XX, YY, ZZ}")
	     ("type {XX, ZZ, YY}")
	     ("type {YY, XX, ZZ}")
	     ("type {YY, ZZ, XX}")
	     ("type {ZZ, XX, YY}")
	     ("type {ZZ, YY, XX}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY"
  :show "TypeColimits#T_XY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ"
  :show "TypeColimits#T_XZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YX"
  :show "TypeColimits#T_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YZ"
  :show "TypeColimits#T_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_ZX"
  :show "TypeColimits#T_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y}")
	     ("type {Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_ZY"
  :show "TypeColimits#T_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y}")
	     ("type {Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YX"
  :show "TypeColimits#T_XY_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YZ"
  :show "TypeColimits#T_XY_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YP"
  :show "TypeColimits#T_XY_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y, Z}")
	     ("type {P, Z, Y}")
	     ("type {Y, P, Z}")
	     ("type {Y, Z, P}")
	     ("type {Z, P, Y}")
	     ("type {Z, Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_ZX"
  :show "TypeColimits#T_XY_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y}")
	     ("type {Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_ZY"
  :show "TypeColimits#T_XY_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Y"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_ZP"
  :show "TypeColimits#T_XY_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YX"
  :show "TypeColimits#T_XZ_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YZ"
  :show "TypeColimits#T_XZ_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type Z"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YP"
  :show "TypeColimits#T_XZ_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Z}")
	     ("type {Z, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_ZX"
  :show "TypeColimits#T_XZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_ZY"
  :show "TypeColimits#T_XZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_ZP"
  :show "TypeColimits#T_XZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y, Z}")
	     ("type {P, Z, Y}")
	     ("type {Y, P, Z}")
	     ("type {Y, Z, P}")
	     ("type {Z, P, Y}")
	     ("type {Z, Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YX"
  :show "TypeColimits#T_XP_YX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Z}")
	     ("type {P, Z, X}")
	     ("type {X, P, Z}")
	     ("type {X, Z, P}")
	     ("type {Z, P, X}")
	     ("type {Z, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YZ"
  :show "TypeColimits#T_XP_YZ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Z}")
	     ("type {Z, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YP"
  :show "TypeColimits#T_XP_YP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Z}")
	     ("type {Z, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ"
  :show "TypeColimits#T_XP_YQ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q, Z}")
	     ("type {P, Z, Q}")
	     ("type {Q, P, Z}")
	     ("type {Q, Z, P}")
	     ("type {Z, P, Q}")
	     ("type {Z, Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_ZX"
  :show "TypeColimits#T_XP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Y}")
	     ("type {P, Y, X}")
	     ("type {X, P, Y}")
	     ("type {X, Y, P}")
	     ("type {Y, P, X}")
	     ("type {Y, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_ZY"
  :show "TypeColimits#T_XP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_ZP"
  :show "TypeColimits#T_XP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives 
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_ZR"
  :show "TypeColimits#T_XP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, Y}")
	     ("type {P, Y, R}")
	     ("type {R, P, Y}")
	     ("type {R, Y, P}")
	     ("type {Y, P, R}")
	     ("type {Y, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YX_ZX"
  :show "TypeColimits#T_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type X"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YX_ZY"
  :show "TypeColimits#T_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y}")
	     ("type {Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YX_ZP"
  :show "TypeColimits#T_YX_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YX_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YZ_ZX"
  :show "TypeColimits#T_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives 
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YZ_ZY"
  :show "TypeColimits#T_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YZ_ZP"
  :show "TypeColimits#T_YZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YZ_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Z}")
	     ("type {P, Z, X}")
	     ("type {X, P, Z}")
	     ("type {X, Z, P}")
	     ("type {Z, P, X}")
	     ("type {Z, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YP_ZX"
  :show "TypeColimits#T_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YP_ZY"
  :show "TypeColimits#T_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Y}")
	     ("type {P, Y, X}")
	     ("type {X, P, Y}")
	     ("type {X, Y, P}")
	     ("type {Y, P, X}")
	     ("type {Y, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YP_ZP"
  :show "TypeColimits#T_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_YP_ZR"
  :show "TypeColimits#T_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_YP_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, X}")
	     ("type {P, X, R}")
	     ("type {R, P, X}")
	     ("type {R, X, P}")
	     ("type {X, P, R}")
	     ("type {X, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YX_ZX"
  :show "TypeColimits#T_XY_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, X}")
	     ("type {X, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YX_ZY"
  :show "TypeColimits#T_XY_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y}")
	     ("type {Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YX_ZR"
  :show "TypeColimits#T_XY_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YX_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {R, X, Y}")
	     ("type {R, Y, X}")
	     ("type {X, R, Y}")
	     ("type {X, Y, R}")
	     ("type {Y, R, X}")
	     ("type {Y, X, R}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YZ_ZX"
  :show "TypeColimits#T_XY_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YZ_ZY"
  :show "TypeColimits#T_XY_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YZ_ZR"
  :show "TypeColimits#T_XY_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YZ_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {R, Y, Z}")
	     ("type {R, Z, Y}")
	     ("type {Y, R, Z}")
	     ("type {Y, Z, R}")
	     ("type {Z, R, Y}")
	     ("type {Z, Y, R}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YP_ZX"
  :show "TypeColimits#T_XY_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Y}")
	     ("type {P, Y, X}")
	     ("type {X, P, Y}")
	     ("type {X, Y, P}")
	     ("type {Y, P, X}")
	     ("type {Y, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YP_ZY"
  :show "TypeColimits#T_XY_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YP_ZP"
  :show "TypeColimits#T_XY_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XY_YP_ZR"
  :show "TypeColimits#T_XY_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XY_YP_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, Y}")
	     ("type {P, Y, R}")
	     ("type {R, P, Y}")
	     ("type {R, Y, P}")
	     ("type {Y, P, R}")
	     ("type {Y, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YX_ZX"
  :show "TypeColimits#T_XZ_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YX_ZY"
  :show "TypeColimits#T_XZ_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Y, Z}")
	     ("type {X, Z, Y}")
	     ("type {Y, X, Z}")
	     ("type {Y, Z, X}")
	     ("type {Z, X, Y}")
	     ("type {Z, Y, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YX_ZR"
  :show "TypeColimits#T_XZ_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YX_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {R, X, Z}")
	     ("type {R, Z, X}")
	     ("type {X, R, Z}")
	     ("type {X, Z, R}")
	     ("type {Z, R, X}")
	     ("type {Z, X, R}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YZ_ZX"
  :show "TypeColimits#T_XZ_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {X, Z}")
	     ("type {Z, X}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YZ_ZY"
  :show "TypeColimits#T_XZ_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {Y, Z}")
	     ("type {Z, Y}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YZ_ZR"
  :show "TypeColimits#T_XZ_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YZ_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {R, Z}")
	     ("type {Z, R}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YP_ZX"
  :show "TypeColimits#T_XZ_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Z}")
	     ("type {P, Z, X}")
	     ("type {X, P, Z}")
	     ("type {X, Z, P}")
	     ("type {Z, P, X}")
	     ("type {Z, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YP_ZY"
  :show "TypeColimits#T_XZ_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y, Z}")
	     ("type {P, Z, Y}")
	     ("type {Y, P, Z}")
	     ("type {Y, Z, P}")
	     ("type {Z, P, Y}")
	     ("type {Z, Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YP_ZP"
  :show "TypeColimits#T_XZ_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Z}")
	     ("type {Z, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XZ_YP_ZR"
  :show "TypeColimits#T_XZ_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XZ_YP_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, Z}")
	     ("type {P, Z, R}")
	     ("type {R, P, Z}")
	     ("type {R, Z, P}")
	     ("type {Z, P, R}")
	     ("type {Z, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YX_ZX"
  :show "TypeColimits#T_XP_YX_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YX_ZY"
  :show "TypeColimits#T_XP_YX_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Y}")
	     ("type {P, Y, X}")
	     ("type {X, P, Y}")
	     ("type {X, Y, P}")
	     ("type {Y, P, X}")
	     ("type {Y, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YX_ZP"
  :show "TypeColimits#T_XP_YX_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YX_ZR"
  :show "TypeColimits#T_XP_YX_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YX_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, X}")
	     ("type {P, X, R}")
	     ("type {R, P, X}")
	     ("type {R, X, P}")
	     ("type {X, P, R}")
	     ("type {X, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YZ_ZX"
  :show "TypeColimits#T_XP_YZ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X, Z}")
	     ("type {P, Z, X}")
	     ("type {X, P, Z}")
	     ("type {X, Z, P}")
	     ("type {Z, P, X}")
	     ("type {Z, X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YZ_ZY"
  :show "TypeColimits#T_XP_YZ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y, Z}")
	     ("type {P, Z, Y}")
	     ("type {Y, P, Z}")
	     ("type {Y, Z, P}")
	     ("type {Z, P, Y}")
	     ("type {Z, Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YZ_ZP"
  :show "TypeColimits#T_XP_YZ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Z}")
	     ("type {Z, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YZ_ZR"
  :show "TypeColimits#T_XP_YZ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YZ_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R, Z}")
	     ("type {P, Z, R}")
	     ("type {R, P, Z}")
	     ("type {R, Z, P}")
	     ("type {Z, P, R}")
	     ("type {Z, R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YP_ZX"
  :show "TypeColimits#T_XP_YP_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, X}")
	     ("type {X, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YP_ZY"
  :show "TypeColimits#T_XP_YP_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Y}")
	     ("type {Y, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YP_ZP"
  :show "TypeColimits#T_XP_YP_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    "type P"
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YP_ZR"
  :show "TypeColimits#T_XP_YP_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YP_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, R}")
	     ("type {R, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ_ZX"
  :show "TypeColimits#T_XP_YQ_ZX"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZX"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q, X}")
	     ("type {P, X, Q}")
	     ("type {Q, P, X}")
	     ("type {Q, X, P}")
	     ("type {X, P, Q}")
	     ("type {X, Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ_ZY"
  :show "TypeColimits#T_XP_YQ_ZY"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZY"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q, Y}")
	     ("type {P, Y, Q}")
	     ("type {Q, P, Y}")
	     ("type {Q, Y, P}")
	     ("type {Y, P, Q}")
	     ("type {Y, Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ_ZP"
  :show "TypeColimits#T_XP_YQ_ZP"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZP"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q}")
	     ("type {Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ_ZQ"
  :show "TypeColimits#T_XP_YQ_ZQ"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZQ"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q}")
	     ("type {Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 ("Bug 0113:  Translate should be monic: T_XP_YQ_ZR"
  :show "TypeColimits#T_XP_YQ_ZR"
  :output '(";;; Elaborating spec-translation at $TESTDIR/TypeColimits#T_XP_YQ_ZR"
	    (:optional "")
	    "spec"
            (:optional "")
	    (:alternatives
	     ("type {P, Q, R}")
	     ("type {P, R, Q}")
	     ("type {Q, P, R}")
	     ("type {Q, R, P}")
	     ("type {R, P, Q}")
	     ("type {R, Q, P}"))
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional ""))
  )

 )
