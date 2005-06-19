(cl-user::sw-init)

(test-directories ".")

;;; OWL example
(test 

 ("OWL: prwb" 
  :swprb NIL
  :output '((:optional "NIL") ""))

 ("OWL: theorem_one_gtq" 
  :sw "axioms#theorem_one_gtq"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#owlnat"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_one_gtq"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String"
	    ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System"
	    ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite"
	    ";; ensure-directories-exist: creating $TESTDIR/Snark/axioms/theorem_one_gtq.log"
	    ";; Directory $TESTDIR/Snark/ does not exist, will create."
	    ";; Directory $TESTDIR/Snark/axioms/ does not exist, will create."
	    ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_one_gtq.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_one_gtq.log"
	    "theorem_one_gtq: Conjecture theorem_one_gtq in owlnat is Proved! using simple inequality reasoning."
	    ""))

 ("OWL: theorem_reflexivity_of_equivalentClass" 
  :sw "axioms#theorem_reflexivity_of_equivalentClass"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#owl_core"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_reflexivity_of_equivalentClass"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentClass.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentClass.log"
	    "theorem_reflexivity_of_equivalentClass: Conjecture theorem_reflexivity_of_equivalentClass in owl_core is Proved! using Snark."
	    ""))

 ("OWL: theorem_not_AllDifferent_cons_xx" 
  :sw "axioms#theorem_not_AllDifferent_cons_xx"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_not_AllDifferent_cons_xx"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_not_AllDifferent_cons_xx.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_not_AllDifferent_cons_xx.log"
	    "theorem_not_AllDifferent_cons_xx: Conjecture theorem_not_AllDifferent_cons_xx in owl_core is Proved! using Snark."
	    ""))

 ("OWL: theorem_type_identity" 
  :sw "axioms#theorem_type_identity"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_identity"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_identity.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_identity.log"
	    "theorem_type_identity: Conjecture theorem_type_identity in owl_core is Proved! using Snark."
	    ""))

 ("OWL: theorem_reflexivity_of_sameAs" 
  :sw "axioms#theorem_reflexivity_of_sameAs"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_reflexivity_of_sameAs"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_sameAs.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_sameAs.log"
	    "theorem_reflexivity_of_sameAs: Conjecture theorem_reflexivity_of_sameAs in owl_core is Proved! using Snark."
	    ""))

 ("OWL: theorem_singleton" 
  :sw "axioms#theorem_singleton"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_singleton"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_singleton.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_singleton.log"
	    "theorem_singleton: Conjecture theorem_singleton in owl_core is Proved! using Snark."
	    ""))

 ("OWL: theorem_type_choice" 
  :sw "axioms#theorem_type_choice"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#cardinality_core"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_choice"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_choice.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_choice.log"
	    "theorem_type_choice: Conjecture theorem_type_choice in cardinality_core is Proved! using Snark."
	    ""))

 ("OWL: not_theorem_someValuesFrom_Thing" 
  :sw "axioms#not_theorem_someValuesFrom_Thing"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#property_restriction"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#not_theorem_someValuesFrom_Thing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/not_theorem_someValuesFrom_Thing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/not_theorem_someValuesFrom_Thing.log"
	    "not_theorem_someValuesFrom_Thing: Conjecture not_theorem_someValuesFrom_Thing in property_restriction is Proved! using Snark."
	    ""))

 ("OWL: theorem_type_someValuesFrom_Thing" 
  :sw "axioms#theorem_type_someValuesFrom_Thing"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_someValuesFrom_Thing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_someValuesFrom_Thing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_someValuesFrom_Thing.log"
	    "theorem_type_someValuesFrom_Thing: Conjecture theorem_type_someValuesFrom_Thing in property_restriction is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_1" 
  :sw "axioms#theorem_card_1"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#cardinality"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_1"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_1.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_1.log"
	    "theorem_card_1: Conjecture theorem_card_1 in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_one_not_Nothing" 
  :sw "axioms#theorem_card_one_not_Nothing"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_one_not_Nothing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_one_not_Nothing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_one_not_Nothing.log"
	    "theorem_card_one_not_Nothing: Conjecture theorem_card_one_not_Nothing in cardinality is Proved! using Snark."
	    ""))

 ;;      ("theorem_card_one_choice" :sw "axioms#theorem_card_one_choice"
 ;;       :output ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_one_choice
 ;;    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_one_choice.sw
 ;;    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_one_choice.log
 ;;theorem_card_one_choice: Conjecture theorem_card_one_choice in cardinality is Proved! using Snark.
 ;;")
 ;;
 ;;      ("theorem_card_zero_remove_is_nothing" :sw "axioms#theorem_card_zero_remove_is_nothing"
 ;;       :output ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_zero_remove_is_nothing
 ;;    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_zero_remove_is_nothing.sw
 ;;    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_zero_remove_is_nothing.log
 ;;theorem_card_zero_remove_is_nothing: Conjecture theorem_card_zero_remove_is_nothing in cardinality is Proved! using Snark.
 ;;")

 ("OWL: theorem_one_gtq_card_remove_is_nothing" 
  :sw "axioms#theorem_one_gtq_card_remove_is_nothing"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_one_gtq_card_remove_is_nothing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_one_gtq_card_remove_is_nothing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_one_gtq_card_remove_is_nothing.log"
	    "theorem_one_gtq_card_remove_is_nothing: Conjecture theorem_one_gtq_card_remove_is_nothing in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_cardone" 
  :sw "axioms#theorem_cardone"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_cardone"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_cardone.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_cardone.log"
	    "theorem_cardone: Conjecture theorem_cardone in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_gtq_choice" 
  :sw "axioms#theorem_card_gtq_choice"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_gtq_choice"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_gtq_choice.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_gtq_choice.log"
	    "theorem_card_gtq_choice: Conjecture theorem_card_gtq_choice in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_two_not_nothing" 
  :sw "axioms#theorem_card_two_not_nothing"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_nothing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_nothing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_nothing.log"
	    "theorem_card_two_not_nothing: Conjecture theorem_card_two_not_nothing in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_two_remove_has_card_one" 
  :sw "axioms#theorem_card_two_remove_has_card_one"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_remove_has_card_one"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_remove_has_card_one.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_remove_has_card_one.log"
	    "theorem_card_two_remove_has_card_one: Conjecture theorem_card_two_remove_has_card_one in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_two_not_same" 
  :sw "axioms#theorem_card_two_not_same"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_same"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_same.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_same.log"
	    "theorem_card_two_not_same: Conjecture theorem_card_two_not_same in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_two_not_three" 
  :sw "axioms#theorem_card_two_not_three"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_three"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_three.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_three.log"
	    "theorem_card_two_not_three: Conjecture theorem_card_two_not_three in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_of_Nothing_is_zero" 
  :sw "axioms#theorem_card_of_Nothing_is_zero"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_of_Nothing_is_zero"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_of_Nothing_is_zero.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_of_Nothing_is_zero.log"
	    "theorem_card_of_Nothing_is_zero: Conjecture theorem_card_of_Nothing_is_zero in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_card_of_Thing_not_zero" 
  :sw "axioms#theorem_card_of_Thing_not_zero"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_of_Thing_not_zero"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_of_Thing_not_zero.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_of_Thing_not_zero.log"
	    "theorem_card_of_Thing_not_zero: Conjecture theorem_card_of_Thing_not_zero in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_subClass_of_image" 
  :sw "axioms#theorem_subClass_of_image"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_subClass_of_image"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_subClass_of_image.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_subClass_of_image.log"
	    "theorem_subClass_of_image: Conjecture theorem_subClass_of_image in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_one" 
  :sw "axioms#theorem_Cardinality_one"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_one"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_one.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_one.log"
	    "theorem_Cardinality_one: Conjecture theorem_Cardinality_one in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_maxCardinality_one" 
  :sw "axioms#theorem_maxCardinality_one"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_maxCardinality_one"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_maxCardinality_one.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_maxCardinality_one.log"
	    "theorem_maxCardinality_one: Conjecture theorem_maxCardinality_one in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_minCardinality_one" 
  :sw "axioms#theorem_minCardinality_one"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_one"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_one.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_one.log"
	    "theorem_minCardinality_one: Conjecture theorem_minCardinality_one in cardinality is Proved! using Snark."
	    ""))

 ("OWL: theorem_minCardinality_zero" 
  :sw "axioms#theorem_minCardinality_zero"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_zero"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_zero.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_zero.log"
	    "theorem_minCardinality_zero: Conjecture theorem_minCardinality_zero in cardinality is Proved! using Snark."
	    ""))

 ("OWL: testcase_cardinality_002" 
  :sw "axioms#testcase_cardinality_002"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#cardinality_test"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#testcase_cardinality_002"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/testcase_cardinality_002.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/testcase_cardinality_002.log"
	    "testcase_cardinality_002: Conjecture testcase_cardinality_002 in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_two_not_same" 
  :sw "axioms#theorem_Cardinality_two_not_same"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_not_same"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_same.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_same.log"
	    "theorem_Cardinality_two_not_same: Conjecture theorem_Cardinality_two_not_same in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_two_not_three" 
  :sw "axioms#theorem_Cardinality_two_not_three"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_not_three"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_three.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_three.log"
	    "theorem_Cardinality_two_not_three: Conjecture theorem_Cardinality_two_not_three in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_not_same_zero" 
  :sw "axioms#theorem_Cardinality_not_same_zero"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_zero"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_zero.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_zero.log"
	    "theorem_Cardinality_not_same_zero: Conjecture theorem_Cardinality_not_same_zero in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_not_same_one" 
  :sw "axioms#theorem_Cardinality_not_same_one"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_one"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_one.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_one.log"
	    "theorem_Cardinality_not_same_one: Conjecture theorem_Cardinality_not_same_one in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_minCardinality_not_same_n" 
  :sw "axioms#theorem_minCardinality_not_same_n"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_not_same_n"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_not_same_n.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_not_same_n.log"
	    "theorem_minCardinality_not_same_n: Conjecture theorem_minCardinality_not_same_n in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_not_same_n" 
  :sw "axioms#theorem_Cardinality_not_same_n"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_n"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_n.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_n.log"
	    "theorem_Cardinality_not_same_n: Conjecture theorem_Cardinality_not_same_n in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_maxCardinality_not_different_n" 
  :sw "axioms#theorem_maxCardinality_not_different_n"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_maxCardinality_not_different_n"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_maxCardinality_not_different_n.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_maxCardinality_not_different_n.log"
	    "theorem_maxCardinality_not_different_n: Conjecture theorem_maxCardinality_not_different_n in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_not_different_n" 
  :sw "axioms#theorem_Cardinality_not_different_n"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_different_n"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_different_n.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_different_n.log"
	    "theorem_Cardinality_not_different_n: Conjecture theorem_Cardinality_not_different_n in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_Cardinality_two_Alldifferent" 
  :sw "axioms#theorem_Cardinality_two_Alldifferent"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_Alldifferent"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_Alldifferent.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_Alldifferent.log"
	    "theorem_Cardinality_two_Alldifferent: Conjecture theorem_Cardinality_two_Alldifferent in cardinality_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_unionOf_Nothing" 
  :sw "axioms#theorem_unionOf_Nothing"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#owl_class_ops"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_unionOf_Nothing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_unionOf_Nothing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_unionOf_Nothing.log"
	    "theorem_unionOf_Nothing: Conjecture theorem_unionOf_Nothing in owl_class_ops is Proved! using Snark."
	    ""))

 ("OWL: theorem_unionOf_Thing" 
  :sw "axioms#theorem_unionOf_Thing"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_unionOf_Thing"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_unionOf_Thing.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_unionOf_Thing.log"
	    "theorem_unionOf_Thing: Conjecture theorem_unionOf_Thing in owl_class_ops is Proved! using Snark."
	    ""))

 ("OWL: test_complementOf_001" 
  :sw "axioms#test_complementOf_001"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#owl_class_ops_test"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#test_complementOf_001"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/test_complementOf_001.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/test_complementOf_001.log"
	    "test_complementOf_001: Conjecture test_complementOf_001 in owl_class_ops_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_oneOf_vs_addOne" 
  :sw "axioms#theorem_oneOf_vs_addOne"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_oneOf_vs_addOne"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_oneOf_vs_addOne.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_oneOf_vs_addOne.log"
	    "theorem_oneOf_vs_addOne: Conjecture theorem_oneOf_vs_addOne in owl_class_ops_test is Proved! using Snark."
	    ""))

 ("OWL: theorem_inverseOf_Functional_is_InverseFunctional" 
  :sw "axioms#theorem_inverseOf_Functional_is_InverseFunctional"
  :output '(";;; Elaborating spec at $TESTDIR/axioms#properties"
	    ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_inverseOf_Functional_is_InverseFunctional"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_inverseOf_Functional_is_InverseFunctional.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_inverseOf_Functional_is_InverseFunctional.log"
	    "theorem_inverseOf_Functional_is_InverseFunctional: Conjecture theorem_inverseOf_Functional_is_InverseFunctional in properties is Proved! using Snark."
	    ""))

 ("OWL: theorem_domain_and_range_of_symmetric_are_the_same" 
  :sw "axioms#theorem_domain_and_range_of_symmetric_are_the_same"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#theorem_domain_and_range_of_symmetric_are_the_same"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_domain_and_range_of_symmetric_are_the_same.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/theorem_domain_and_range_of_symmetric_are_the_same.log"
	    "theorem_domain_and_range_of_symmetric_are_the_same: Conjecture theorem_domain_and_range_of_symmetric_are_the_same in properties is Proved! using Snark."
	    ""))

 ("OWL: example_chianti" 
  :sw "axioms#example_chianti"
  :output '(";;; Elaborating proof-term at $TESTDIR/axioms#example_chianti"
	    "    Expanded spec file: $TESTDIR/Snark/axioms/example_chianti.sw"
	    "    Snark Log file: $TESTDIR/Snark/axioms/example_chianti.log"
	    "example_chianti: Conjecture example_chianti in properties is Proved! using Snark."
	    ""))
 ;;      ("contradictory" :sw "axioms#contradictory"
 ;;       :output ";;; Elaborating proof-term at $TESTDIR/axioms#contradictory"
 ;;    Expanded spec file: $TESTDIR/Snark/axioms/contradictory.sw
 ;;    Snark Log file: $TESTDIR/Snark/axioms/contradictory.log
 ;;contradictory: Conjecture contradictory in properties is Proved! using Snark.
 ;;")

 )

#||
("Owl axioms"
       
 :sw "axioms#"
       :output
       '(";;; Elaborating spec at $TESTDIR/axioms#owl_core"
	 ";;; Elaborating spec at $TESTDIR/axioms#owl_core_test"
	 ";;; Elaborating spec at $TESTDIR/axioms#owl_class_ops"
	 ";;; Elaborating spec at $TESTDIR/axioms#owl_class_ops_test"
	 ";;; Elaborating spec at $TESTDIR/axioms#property_restriction"
	 ";;; Elaborating spec at $TESTDIR/axioms#cardinality_core"
	 ";;; Elaborating spec at $TESTDIR/axioms#owlnat"
	 ";;; Elaborating spec at $TESTDIR/axioms#cardinality"
	 ";;; Elaborating spec at $TESTDIR/axioms#cardinality_test"
	 ";;; Elaborating spec at $TESTDIR/axioms#properties"
	 ";;; Elaborating spec at $TESTDIR/axioms#properties_test"
	 ";;; Elaborating spec at $TESTDIR/axioms#owl"
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_one_gtq"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Top"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Char"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/List"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/Option"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/String"
	 ";;; Elaborating spec at $SPECWARE/Library/ProverBase/System"
	 ";;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite"
	 (:alternatives
	  ()
	  (";; ensure-directories-exist: creating $TESTDIR/Snark/axioms/theorem_one_gtq.log")
	  (";; ensure-directories-exist: creating"
	   ";;   $TESTDIR/Snark/axioms/theorem_one_gtq.log"))
	 (:optional ";; Directory $TESTDIR/Snark/ does not exist, will create.")
	 (:optional ";; Directory $TESTDIR/Snark/axioms/ does not exist, will create.")
	 (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_one_gtq.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_one_gtq.log"
	 (:optional ";;; Elaborating spec at $SPECWARE/Library/Base/ProverBase")
	 "theorem_one_gtq: Conjecture theorem_one_gtq in owlnat is Proved! using simple inequality reasoning."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_reflexivity_of_equivalentClass"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentClass.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentClass.log"
	 "theorem_reflexivity_of_equivalentClass: Conjecture theorem_reflexivity_of_equivalentClass in owl_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_not_AllDifferent_cons_xx"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_not_AllDifferent_cons_xx.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_not_AllDifferent_cons_xx.log"
	 "theorem_not_AllDifferent_cons_xx: Conjecture theorem_not_AllDifferent_cons_xx in owl_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_identity"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_identity.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_identity.log"
	 "theorem_type_identity: Conjecture theorem_type_identity in owl_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_reflexivity_of_sameAs"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_sameAs.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_sameAs.log"
	 "theorem_reflexivity_of_sameAs: Conjecture theorem_reflexivity_of_sameAs in owl_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_singleton"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_singleton.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_singleton.log"
	 "theorem_singleton: Conjecture theorem_singleton in owl_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#testcase_AllDifferent_Manifest_test"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/testcase_AllDifferent_Manifest_test.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/testcase_AllDifferent_Manifest_test.log"
	 "testcase_AllDifferent_Manifest_test: Conjecture testcase_AllDifferent_Manifest_test in owl_core_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_choice"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_choice.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_choice.log"
	 "theorem_type_choice: Conjecture theorem_type_choice in cardinality_core is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_subclass_Nothing_allValuesFrom_Nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_subclass_Nothing_allValuesFrom_Nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_subclass_Nothing_allValuesFrom_Nothing.log"
	 "theorem_subclass_Nothing_allValuesFrom_Nothing: Conjecture theorem_subclass_Nothing_allValuesFrom_Nothing in property_restriction is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#not_theorem_someValuesFrom_Thing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/not_theorem_someValuesFrom_Thing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/not_theorem_someValuesFrom_Thing.log"
	 "not_theorem_someValuesFrom_Thing: Conjecture not_theorem_someValuesFrom_Thing in property_restriction is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_type_someValuesFrom_Thing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_type_someValuesFrom_Thing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_type_someValuesFrom_Thing.log"
	 "theorem_type_someValuesFrom_Thing: Conjecture theorem_type_someValuesFrom_Thing in property_restriction is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_1"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_1.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_1.log"
	 "theorem_card_1: Conjecture theorem_card_1 in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_one_not_Nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_one_not_Nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_one_not_Nothing.log"
	 "theorem_card_one_not_Nothing: Conjecture theorem_card_one_not_Nothing in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_zero_remove_is_nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_zero_remove_is_nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_zero_remove_is_nothing.log"
	 "theorem_card_zero_remove_is_nothing: Conjecture theorem_card_zero_remove_is_nothing in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#lemma_not_nothing_card_addone_plus"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/lemma_not_nothing_card_addone_plus.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/lemma_not_nothing_card_addone_plus.log"
	 "lemma_not_nothing_card_addone_plus: Conjecture lemma_not_nothing_card_addone_plus in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_one_remove"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_one_remove.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_one_remove.log"
	 "theorem_card_one_remove: Conjecture theorem_card_one_remove in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_one_gtq_card_remove_is_nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_one_gtq_card_remove_is_nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_one_gtq_card_remove_is_nothing.log"
	 "theorem_one_gtq_card_remove_is_nothing: Conjecture theorem_one_gtq_card_remove_is_nothing in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_cardone"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_cardone.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_cardone.log"
	 "theorem_cardone: Conjecture theorem_cardone in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_gtq_choice"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_gtq_choice.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_gtq_choice.log"
	 "theorem_card_gtq_choice: Conjecture theorem_card_gtq_choice in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_nothing.log"
	 "theorem_card_two_not_nothing: Conjecture theorem_card_two_not_nothing in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_remove_has_card_one"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_remove_has_card_one.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_remove_has_card_one.log"
	 "theorem_card_two_remove_has_card_one: Conjecture theorem_card_two_remove_has_card_one in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_same"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_same.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_same.log"
	 "theorem_card_two_not_same: Conjecture theorem_card_two_not_same in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_two_not_three"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_two_not_three.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_two_not_three.log"
	 "theorem_card_two_not_three: Conjecture theorem_card_two_not_three in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_of_Nothing_is_zero"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_of_Nothing_is_zero.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_of_Nothing_is_zero.log"
	 "theorem_card_of_Nothing_is_zero: Conjecture theorem_card_of_Nothing_is_zero in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_card_of_Thing_not_zero"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_card_of_Thing_not_zero.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_card_of_Thing_not_zero.log"
	 "theorem_card_of_Thing_not_zero: Conjecture theorem_card_of_Thing_not_zero in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_subClass_of_image"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_subClass_of_image.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_subClass_of_image.log"
	 "theorem_subClass_of_image: Conjecture theorem_subClass_of_image in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_one"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_one.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_one.log"
	 "theorem_Cardinality_one: Conjecture theorem_Cardinality_one in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_subClass_maxCardinality"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_subClass_maxCardinality.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_subClass_maxCardinality.log"
	 "theorem_Cardinality_subClass_maxCardinality: Conjecture theorem_Cardinality_subClass_maxCardinality in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_subClass_minCardinality"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_subClass_minCardinality.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_subClass_minCardinality.log"
	 "theorem_Cardinality_subClass_minCardinality: Conjecture theorem_Cardinality_subClass_minCardinality in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_maxCardinality_one"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_maxCardinality_one.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_maxCardinality_one.log"
	 "theorem_maxCardinality_one: Conjecture theorem_maxCardinality_one in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_one"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_one.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_one.log"
	 "theorem_minCardinality_one: Conjecture theorem_minCardinality_one in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_zero"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_zero.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_zero.log"
	 "theorem_minCardinality_zero: Conjecture theorem_minCardinality_zero in cardinality is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#testcase_cardinality_002"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/testcase_cardinality_002.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/testcase_cardinality_002.log"
	 "testcase_cardinality_002: Conjecture testcase_cardinality_002 in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_not_same"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_same.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_same.log"
	 "theorem_Cardinality_two_not_same: Conjecture theorem_Cardinality_two_not_same in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_not_three"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_three.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_not_three.log"
	 "theorem_Cardinality_two_not_three: Conjecture theorem_Cardinality_two_not_three in cardinality_test is NOT proved using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_zero"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_zero.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_zero.log"
	 "theorem_Cardinality_not_same_zero: Conjecture theorem_Cardinality_not_same_zero in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_one"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_one.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_one.log"
	 "theorem_Cardinality_not_same_one: Conjecture theorem_Cardinality_not_same_one in cardinality_test is NOT proved using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_minCardinality_not_same_n"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_minCardinality_not_same_n.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_minCardinality_not_same_n.log"
	 "theorem_minCardinality_not_same_n: Conjecture theorem_minCardinality_not_same_n in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_same_n"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_n.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_same_n.log"
	 "theorem_Cardinality_not_same_n: Conjecture theorem_Cardinality_not_same_n in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_maxCardinality_not_different_n"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_maxCardinality_not_different_n.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_maxCardinality_not_different_n.log"
	 "theorem_maxCardinality_not_different_n: Conjecture theorem_maxCardinality_not_different_n in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_not_different_n"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_different_n.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_not_different_n.log"
	 "theorem_Cardinality_not_different_n: Conjecture theorem_Cardinality_not_different_n in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_Cardinality_two_Alldifferent"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_Alldifferent.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_Cardinality_two_Alldifferent.log"
	 "theorem_Cardinality_two_Alldifferent: Conjecture theorem_Cardinality_two_Alldifferent in cardinality_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_intersectionOf_Nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_intersectionOf_Nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_intersectionOf_Nothing.log"
	 "theorem_intersectionOf_Nothing: Conjecture theorem_intersectionOf_Nothing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_intersectionOf_Thing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_intersectionOf_Thing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_intersectionOf_Thing.log"
	 "theorem_intersectionOf_Thing: Conjecture theorem_intersectionOf_Thing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_unionOf_Nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_unionOf_Nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_unionOf_Nothing.log"
	 "theorem_unionOf_Nothing: Conjecture theorem_unionOf_Nothing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_unionOf_Thing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_unionOf_Thing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_unionOf_Thing.log"
	 "theorem_unionOf_Thing: Conjecture theorem_unionOf_Thing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_complementOf_Nothing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_complementOf_Nothing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_complementOf_Nothing.log"
	 "theorem_complementOf_Nothing: Conjecture theorem_complementOf_Nothing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_complementOf_Thing"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_complementOf_Thing.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_complementOf_Thing.log"
	 "theorem_complementOf_Thing: Conjecture theorem_complementOf_Thing in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_complements_are_disjoint"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_complements_are_disjoint.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_complements_are_disjoint.log"
	 "theorem_complements_are_disjoint: Conjecture theorem_complements_are_disjoint in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#test_complementOf_001"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/test_complementOf_001.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/test_complementOf_001.log"
	 "test_complementOf_001: Conjecture test_complementOf_001 in owl_class_ops_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#lemma_oneOf_vs_addOne"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/lemma_oneOf_vs_addOne.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/lemma_oneOf_vs_addOne.log"
	 "lemma_oneOf_vs_addOne: Conjecture lemma_oneOf_vs_addOne in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_oneOf_vs_addOne"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_oneOf_vs_addOne.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_oneOf_vs_addOne.log"
	 "theorem_oneOf_vs_addOne: Conjecture theorem_oneOf_vs_addOne in owl_class_ops is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_reflexivity_of_equivalentProperty"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentProperty.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_reflexivity_of_equivalentProperty.log"
	 "theorem_reflexivity_of_equivalentProperty: Conjecture theorem_reflexivity_of_equivalentProperty in properties is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_inverseOf_is_symmetric"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_inverseOf_is_symmetric.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_inverseOf_is_symmetric.log"
	 "theorem_inverseOf_is_symmetric: Conjecture theorem_inverseOf_is_symmetric in properties is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#testcase_FunctionalProperty_Manifest001_test"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/testcase_FunctionalProperty_Manifest001_test.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/testcase_FunctionalProperty_Manifest001_test.log"
	 "testcase_FunctionalProperty_Manifest001_test: Conjecture testcase_FunctionalProperty_Manifest001_test in properties_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#testcase_FunctionalProperty_Manifest002_test"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/testcase_FunctionalProperty_Manifest002_test.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/testcase_FunctionalProperty_Manifest002_test.log"
	 "testcase_FunctionalProperty_Manifest002_test: Conjecture testcase_FunctionalProperty_Manifest002_test in properties_test is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_inverseOf_Functional_is_InverseFunctional"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_inverseOf_Functional_is_InverseFunctional.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_inverseOf_Functional_is_InverseFunctional.log"
	 "theorem_inverseOf_Functional_is_InverseFunctional: Conjecture theorem_inverseOf_Functional_is_InverseFunctional in properties is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#theorem_domain_and_range_of_symmetric_are_the_same"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/theorem_domain_and_range_of_symmetric_are_the_same.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/theorem_domain_and_range_of_symmetric_are_the_same.log"
	 "theorem_domain_and_range_of_symmetric_are_the_same: Conjecture theorem_domain_and_range_of_symmetric_are_the_same in properties is Proved! using Snark."
	 ";;; Elaborating proof-term at $TESTDIR/axioms#example_chianti"
	 (:optional "    Expanded spec file: $TESTDIR/Snark/axioms/example_chianti.sw")
	 "    Snark Log file: $TESTDIR/Snark/axioms/example_chianti.log"
	 "example_chianti: Conjecture example_chianti in properties is Proved! using Snark."
	 "================================================================================"
	 ))
      )

||#