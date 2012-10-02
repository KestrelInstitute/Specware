(test-directories ".")

(test 
 ("Bug 0085 : Proof obligations for quotient pattern are now generated"
  :show   "quotpat#O"
  :output '(";;; Elaborating obligator at $TESTDIR/quotpat#O"
	    ";;; Elaborating spec at $TESTDIR/quotpat#S"
	    (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/WFO")
	    (:optional "")
	    "spec"
	    (:optional "import /Library/Base/WFO")
	    (:optional "")
            (:alternatives 
             "op  eq_mod10: Nat * Nat -> Bool"
             "op  eq_mod10 : Nat * Nat -> Bool")
	    (:optional "")
            (:alternatives 
             "def eq_mod10 (n1, n2) = n1 mod 10 = n2 mod 10"
             "def eq_mod10(n1: Nat, n2: Nat): Bool = n1 mod 10 = n2 mod 10"
             "def eq_mod10 (n1 : Nat, n2 : Nat) : Bool = n1 mod 10 = n2 mod 10")
	    (:optional "")
            "conjecture eq_mod10_transitive is"
            "fa(x: Nat, y: Nat, z: Nat) eq_mod10(x, y) && eq_mod10(y, z) => eq_mod10(x, z)"
	    (:optional "")
            "conjecture eq_mod10_symmetric is fa(x: Nat, y: Nat) eq_mod10(x, y) => eq_mod10(y, x)"
	    (:optional "")
            (:alternatives 
             "conjecture eq_mod10_reflexive is fa(x: Nat) eq_mod10(x, x)"
             "conjecture eq_mod10_reflexive is fa(x : Nat) eq_mod10(x, x)")
	    (:optional "")
            "type Q = (Nat / eq_mod10)"
	    (:optional "")
            (:alternatives 
             "op f: Q -> Nat"
             "op f : Q -> Nat")
	    (:optional "")
            "conjecture f_Obligation_subtype is"
	    (:alternatives
	     ("fa(x: Q, y: Int)"
	      "natural? y && x = quotient[Q]  y => natural?(y + 1)")
	     ("fa(x : Q, y : Int)"
	      "natural? y && x = quotient[Q]  y => natural?(y + 1)")
	     "fa(x: Q, y: Int) y >= 0 && x = quotient[Q]  y => y + 1 >= 0"
	     "fa(x : Q, y : Int) y >= 0 && x = quotient[Q]  y => y + 1 >= 0")
	    (:optional "")
            "conjecture f_Obligation_quotient is"
	    (:alternatives
             "fa(y__1: Nat, y__2: Nat)"
             "fa(y__1 : Nat, y__2 : Nat)")
            "quotient[Q]  y__1 = quotient[Q]  y__2 => y__1 + 1 = y__2 + 1"
	    (:optional "")
            (:alternatives
             "def f x = let quotient[Q] y = x in"
             "def f(x: Q): Nat = let (quotient[Q] y) = x in"
             "def f (x : Q) : Nat = let (quotient[Q] y) = x in")
            "y + 1"
	    (:optional "")
            (:alternatives
             " op g: Q -> Nat"
             " op g : Q -> Nat")
	    (:optional "")
	    (:alternatives
	     "conjecture g_Obligation_subtype0 is fa(y: Nat) natural?(y + 1)"
	     "conjecture g_Obligation_subtype0 is fa(y : Nat) natural?(y + 1)"
	     "conjecture g_Obligation_subtype0 is fa(y: Nat) y + 1 >= 0"
	     "conjecture g_Obligation_subtype0 is fa(y : Nat) y + 1 >= 0")
            (:optional "")
            "conjecture g_Obligation_subtype is fa(m: Nat, n: Nat) eq_mod10(m, n) => m + 1 = n + 1"
            (:optional "")
            (:alternatives
             "def g x = choose[Q] ((fn y: Nat -> y + 1)) x"
             "def g x = choose[Q] ((fn y : Nat -> y + 1)) x"
             "def g(x: Q): Nat = choose[Q]  (fn (y: Nat) -> y + 1) x"
             "def g (x : Q) : Nat = choose[Q]  (fn (y : Nat) -> y + 1) x")
            (:optional "")
            (:alternatives
             "op f2: Q -> List(Nat)"
             "op f2 : Q -> List(Nat)")
            (:optional "")
            "conjecture f2_Obligation_subtype is fa(B: Int) B >= 0"
	    (:optional "")
            "conjecture f2_Obligation_quotient is"
	    (:alternatives
             "fa(y__1: Nat, y__2: Nat)"
             "fa(y__1 : Nat, y__2 : Nat)")
            (:alternatives
             "quotient[Q]  y__1 = quotient[Q]  y__2 => [y__1 + 1] = [y__2 + 1]"
             "quotient[Q]  y__1 = quotient[Q]  y__2 => y__1 + 1 = y__2 + 1 && [] = []")
	    (:optional "")
            (:alternatives
             "def f2 x = let quotient[Q] y = x in"
             "def f2(x: Q): List(Nat) = let (quotient[Q] y) = x in"
             "def f2 (x : Q) : List(Nat) = let (quotient[Q] y) = x in")
            "[y + 1]"
	    (:optional "")
	    (:alternatives
             "op g2: Q -> List(Nat)"
             "op g2 : Q -> List(Nat)")
	    (:optional "")
            "conjecture g2_Obligation_subtype0 is fa(B: Int) B >= 0"
	    (:optional "")
            "conjecture g2_Obligation_subtype is"
            (:alternatives
             "fa(m: Nat, n: Nat) eq_mod10(m, n) => [m + 1] = [n + 1]"
             "fa(m : Nat, n : Nat) eq_mod10(m, n) => [m + 1] = [n + 1]"
             "fa(m: Nat, n: Nat) eq_mod10(m, n) => (m + 1, []) = (n + 1, [])"
             "fa(m : Nat, n : Nat) eq_mod10(m, n) => (m + 1, []) = (n + 1, [])")
	    (:optional "")
            (:alternatives
             "def g2 x = choose[Q] ((fn y: Nat -> [y + 1])) x"
             "def g2 x = choose[Q] ((fn y : Nat -> [y + 1])) x"
             "def g2(x: Q): List(Nat) = choose[Q]  (fn (y: Nat) -> [y + 1]) x"
             ("def g2 (x : Q) : List(Nat)"
              "= choose[Q]  (fn (y : Nat) -> [y + 1]) x"))
	    (:optional "")
            (:alternatives "endspec" "end-spec")
	    (:optional "")
	    (:optional "")
	    ))
 )
