;;;(test-files "proveOblig.sw" "simple.sw" "fib.sw"
;;;	    "colimit.sw"
;;;	    "tw-0103-1.sw" "tw-0103-2.sw" "tw-0103-3.sw"
;;;	    "players.sw")

(cl-user::sw-init)
(cl-user::swpath (concatenate 'string (specware::getenv "SPECWARE4") #+mswindows";/" #-mswindows":/"))

(test-directories ".")

(test ("NormalFib" :sw "fib"
		   :output ";;; Elaborating spec at $TESTDIR/fib
")
      ("CompileFib" :swll "fib"
		    :output ";;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")
      ("RunFib" :swe "computeFib 10"
		:swe-spec "fib"
		:value '(:|Int| . 89))
      ("twk message 1/10/03 Reused name leading to circularity."
       :sw "players#twoPlayersLisp"
       :file-goto-error '("$TESTDIR/players.sw" 43 13)
       :output "Error in specification: Name \"twoPlayers\" defined twice in file.
 found in $TESTDIR/players.sw
43.13-44.52")
      ("Colimit with no sharing"
       :sw "colimit"
       :output ";;; Elaborating spec at $TESTDIR/colimit#A
;;; Elaborating diagram-term at $TESTDIR/colimit#D
;;; Elaborating diagram-colimit at $TESTDIR/colimit#C
;;; Elaborating spec at $TESTDIR/colimit#E
")
      ("Out of order sub-units"
       :sw "order"
       :output ";;; Elaborating spec at $TESTDIR/order#order
;;; Elaborating spec at $TESTDIR/order#B
;;; Elaborating spec at $TESTDIR/order#C
")
      ("Circular sub-unit"
       :sw "genC"
       :output "Circular definition: $TESTDIR/genC#GCD")
      ("Implicit polymorphic op defined inferred"
       :sw "ImplPoly"
       :output ";;; Elaborating spec at $TESTDIR/ImplPoly
")
      ("Quotient Pattern"
       :swll "QuotientPattern"
       :output ";;; Elaborating spec at $TESTDIR/QuotientPattern
;;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")
      ("Restrict Obligations"
       :show "RestrictObligation#O"
       :output ";;; Elaborating obligator at $TESTDIR/RestrictObligation#O
;;; Elaborating spec at $TESTDIR/RestrictObligation#A
;;; Elaborating spec at $SPECWARE/Library/Base/WFO

spec  
 import A
 import /Library/Base/WFO
 conjecture f_Obligation is 
    fa(y : Integer, x : Integer) x > - y => nonNeg?(x + y)
 conjecture f_Obligation0 is 
    fa(y : Integer, x : Integer) 
     x > - y && nonNeg?(x + y) => natural?(x + y)
endspec

"
)
      ("libtest" :swll "libtest"
		 :output ";;; Elaborating spec at $TESTDIR/libtest
;;; Generating lisp file /tmp/lgen_lisp_tmp.lisp
")
      ("Prettyprint Parens"
       :show "PP"
       :output ";;; Elaborating spec at $TESTDIR/PP

spec  
 type T = (( | Foo | Fum) | truep)
 type Injection1(a, b) = ((a -> b) | Functions.injective?)
 type T1 = {x : ( | Foo | Fum) | true}
 type T2 = ((T * T1) | truep)
 
 op  truep : [a] a -> Boolean
 axiom List.induction1 is [a] 
    fa(p : List(a) -> Boolean) 
     p([]) 
     && (fa(x : a, l : List(a)) 
          (p l => p(Cons(x, l)) => (fa(l : List(a)) p l)))
endspec

")
      )
