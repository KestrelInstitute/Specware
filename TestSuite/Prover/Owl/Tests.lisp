(cl-user::sw-init)
(cl-user::swprb NIL)
(terpri)

;;; OWL example
(test ("Owl axioms" :sw "/TestSuite/Prover/Owl/axioms"
                    :output ";;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owl_core
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owl_core_test
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owl_class_ops
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owl_class_ops_test
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#property_restriction
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#cardinality_core
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owlnat
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#cardinality
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#cardinality_test
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#properties
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#properties_test
;;; Elaborating spec at $SPECWARE/TestSuite/Prover/Owl/axioms#owl
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_one_gtq
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Top
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Char
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Compare
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Functions
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Integer
;;; Elaborating spec at $SPECWARE/Library/ProverBase/List
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Nat
;;; Elaborating spec at $SPECWARE/Library/ProverBase/Option
;;; Elaborating spec at $SPECWARE/Library/ProverBase/String
;;; Elaborating spec at $SPECWARE/Library/ProverBase/System
;;; Elaborating spec at $SPECWARE/Library/Base/ProverRewrite
;;; Elaborating spec at $SPECWARE/Library/Base/ProverBase
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_one_gtq.log
theorem_one_gtq: Conjecture theorem_one_gtq in owlnat is Proved! using simple inequality reasoning.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_reflexivity_of_equivalentClass
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_reflexivity_of_equivalentClass.log
theorem_reflexivity_of_equivalentClass: Conjecture theorem_reflexivity_of_equivalentClass in owl_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_not_AllDifferent_cons_xx
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_not_AllDifferent_cons_xx.log
theorem_not_AllDifferent_cons_xx: Conjecture theorem_not_AllDifferent_cons_xx in owl_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_type_identity
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_type_identity.log
theorem_type_identity: Conjecture theorem_type_identity in owl_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_reflexivity_of_sameAs
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_reflexivity_of_sameAs.log
theorem_reflexivity_of_sameAs: Conjecture theorem_reflexivity_of_sameAs in owl_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_singleton
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_singleton.log
theorem_singleton: Conjecture theorem_singleton in owl_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#testcase_AllDifferent_Manifest_test
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/testcase_AllDifferent_Manifest_test.log
testcase_AllDifferent_Manifest_test: Conjecture testcase_AllDifferent_Manifest_test in owl_core_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_type_choice
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_type_choice.log
theorem_type_choice: Conjecture theorem_type_choice in cardinality_core is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_subclass_Nothing_allValuesFrom_Nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_subclass_Nothing_allValuesFrom_Nothing.log
theorem_subclass_Nothing_allValuesFrom_Nothing: Conjecture theorem_subclass_Nothing_allValuesFrom_Nothing in property_restriction is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#not_theorem_someValuesFrom_Thing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/not_theorem_someValuesFrom_Thing.log
not_theorem_someValuesFrom_Thing: Conjecture not_theorem_someValuesFrom_Thing in property_restriction is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_type_someValuesFrom_Thing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_type_someValuesFrom_Thing.log
theorem_type_someValuesFrom_Thing: Conjecture theorem_type_someValuesFrom_Thing in property_restriction is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_1
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_1.log
theorem_card_1: Conjecture theorem_card_1 in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_one_not_Nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_one_not_Nothing.log
theorem_card_one_not_Nothing: Conjecture theorem_card_one_not_Nothing in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_zero_remove_is_nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_zero_remove_is_nothing.log
theorem_card_zero_remove_is_nothing: Conjecture theorem_card_zero_remove_is_nothing in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#lemma_not_nothing_card_addone_plus
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/lemma_not_nothing_card_addone_plus.log
lemma_not_nothing_card_addone_plus: Conjecture lemma_not_nothing_card_addone_plus in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_one_remove
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_one_remove.log
theorem_card_one_remove: Conjecture theorem_card_one_remove in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_one_gtq_card_remove_is_nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_one_gtq_card_remove_is_nothing.log
theorem_one_gtq_card_remove_is_nothing: Conjecture theorem_one_gtq_card_remove_is_nothing in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_cardone
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_cardone.log
theorem_cardone: Conjecture theorem_cardone in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_gtq_choice
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_gtq_choice.log
theorem_card_gtq_choice: Conjecture theorem_card_gtq_choice in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_two_not_nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_two_not_nothing.log
theorem_card_two_not_nothing: Conjecture theorem_card_two_not_nothing in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_two_remove_has_card_one
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_two_remove_has_card_one.log
theorem_card_two_remove_has_card_one: Conjecture theorem_card_two_remove_has_card_one in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_two_not_same
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_two_not_same.log
theorem_card_two_not_same: Conjecture theorem_card_two_not_same in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_two_not_three
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_two_not_three.log
theorem_card_two_not_three: Conjecture theorem_card_two_not_three in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_of_Nothing_is_zero
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_of_Nothing_is_zero.log
theorem_card_of_Nothing_is_zero: Conjecture theorem_card_of_Nothing_is_zero in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_card_of_Thing_not_zero
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_card_of_Thing_not_zero.log
theorem_card_of_Thing_not_zero: Conjecture theorem_card_of_Thing_not_zero in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_subClass_of_image
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_subClass_of_image.log
theorem_subClass_of_image: Conjecture theorem_subClass_of_image in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_one
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_one.log
theorem_Cardinality_one: Conjecture theorem_Cardinality_one in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_subClass_maxCardinality
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_subClass_maxCardinality.log
theorem_Cardinality_subClass_maxCardinality: Conjecture theorem_Cardinality_subClass_maxCardinality in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_subClass_minCardinality
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_subClass_minCardinality.log
theorem_Cardinality_subClass_minCardinality: Conjecture theorem_Cardinality_subClass_minCardinality in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_maxCardinality_one
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_maxCardinality_one.log
theorem_maxCardinality_one: Conjecture theorem_maxCardinality_one in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_minCardinality_one
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_minCardinality_one.log
theorem_minCardinality_one: Conjecture theorem_minCardinality_one in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_minCardinality_zero
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_minCardinality_zero.log
theorem_minCardinality_zero: Conjecture theorem_minCardinality_zero in cardinality is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#testcase_cardinality_002
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/testcase_cardinality_002.log
testcase_cardinality_002: Conjecture testcase_cardinality_002 in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_two_not_same
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_two_not_same.log
theorem_Cardinality_two_not_same: Conjecture theorem_Cardinality_two_not_same in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_two_not_three
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_two_not_three.log
theorem_Cardinality_two_not_three: Conjecture theorem_Cardinality_two_not_three in cardinality_test is NOT proved using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_not_same_zero
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_not_same_zero.log
theorem_Cardinality_not_same_zero: Conjecture theorem_Cardinality_not_same_zero in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_not_same_one
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_not_same_one.log
theorem_Cardinality_not_same_one: Conjecture theorem_Cardinality_not_same_one in cardinality_test is NOT proved using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_minCardinality_not_same_n
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_minCardinality_not_same_n.log
theorem_minCardinality_not_same_n: Conjecture theorem_minCardinality_not_same_n in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_not_same_n
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_not_same_n.log
theorem_Cardinality_not_same_n: Conjecture theorem_Cardinality_not_same_n in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_maxCardinality_not_different_n
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_maxCardinality_not_different_n.log
theorem_maxCardinality_not_different_n: Conjecture theorem_maxCardinality_not_different_n in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_not_different_n
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_not_different_n.log
theorem_Cardinality_not_different_n: Conjecture theorem_Cardinality_not_different_n in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_Cardinality_two_Alldifferent
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_Cardinality_two_Alldifferent.log
theorem_Cardinality_two_Alldifferent: Conjecture theorem_Cardinality_two_Alldifferent in cardinality_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_intersectionOf_Nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_intersectionOf_Nothing.log
theorem_intersectionOf_Nothing: Conjecture theorem_intersectionOf_Nothing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_intersectionOf_Thing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_intersectionOf_Thing.log
theorem_intersectionOf_Thing: Conjecture theorem_intersectionOf_Thing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_unionOf_Nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_unionOf_Nothing.log
theorem_unionOf_Nothing: Conjecture theorem_unionOf_Nothing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_unionOf_Thing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_unionOf_Thing.log
theorem_unionOf_Thing: Conjecture theorem_unionOf_Thing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_complementOf_Nothing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_complementOf_Nothing.log
theorem_complementOf_Nothing: Conjecture theorem_complementOf_Nothing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_complementOf_Thing
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_complementOf_Thing.log
theorem_complementOf_Thing: Conjecture theorem_complementOf_Thing in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_complements_are_disjoint
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_complements_are_disjoint.log
theorem_complements_are_disjoint: Conjecture theorem_complements_are_disjoint in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#test_complementOf_001
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/test_complementOf_001.log
test_complementOf_001: Conjecture test_complementOf_001 in owl_class_ops_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#lemma_oneOf_vs_addOne
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/lemma_oneOf_vs_addOne.log
lemma_oneOf_vs_addOne: Conjecture lemma_oneOf_vs_addOne in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_oneOf_vs_addOne
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_oneOf_vs_addOne.log
theorem_oneOf_vs_addOne: Conjecture theorem_oneOf_vs_addOne in owl_class_ops is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_reflexivity_of_equivalentProperty
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_reflexivity_of_equivalentProperty.log
theorem_reflexivity_of_equivalentProperty: Conjecture theorem_reflexivity_of_equivalentProperty in properties is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_inverseOf_is_symmetric
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_inverseOf_is_symmetric.log
theorem_inverseOf_is_symmetric: Conjecture theorem_inverseOf_is_symmetric in properties is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#testcase_FunctionalProperty_Manifest001_test
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/testcase_FunctionalProperty_Manifest001_test.log
testcase_FunctionalProperty_Manifest001_test: Conjecture testcase_FunctionalProperty_Manifest001_test in properties_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#testcase_FunctionalProperty_Manifest002_test
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/testcase_FunctionalProperty_Manifest002_test.log
testcase_FunctionalProperty_Manifest002_test: Conjecture testcase_FunctionalProperty_Manifest002_test in properties_test is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_inverseOf_Functional_is_InverseFunctional
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_inverseOf_Functional_is_InverseFunctional.log
theorem_inverseOf_Functional_is_InverseFunctional: Conjecture theorem_inverseOf_Functional_is_InverseFunctional in properties is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#theorem_domain_and_range_of_symmetric_are_the_same
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/theorem_domain_and_range_of_symmetric_are_the_same.log
theorem_domain_and_range_of_symmetric_are_the_same: Conjecture theorem_domain_and_range_of_symmetric_are_the_same in properties is Proved! using Snark.
;;; Elaborating proof-term at $SPECWARE/TestSuite/Prover/Owl/axioms#example_chianti
    Snark Log file: $SPECWARE/TestSuite/Prover/Owl/Snark/axioms/example_chianti.log
example_chianti: Conjecture example_chianti in properties is Proved! using Snark.
")
      )

