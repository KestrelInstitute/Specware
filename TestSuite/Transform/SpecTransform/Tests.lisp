
(cl-user::sw-init)

(test-directories ".")

(test 

  ("Spec Transform: unknown command (1 of 2)" 
   :sw "unknown#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: unknown command (2 of 2)"
   :sw "unknown#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: doNothing (1 of 4)"
   :sw "doNothing#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: doNothing (2 of 4)"
   :sw "doNothing#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: doNothing (3 of 4)"
   :sw "doNothing#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: doNothing (4 of 4)"
   :sw "doNothing#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: trace (1 of 5)"
   :sw "trace#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: trace (2 of 5)"
   :sw "trace#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: trace (3 of 5)"
   :sw "trace#TF_Bad_3"
   :use-goal-file t)

  ("Spec Transform: trace (4 of 5)"
   :sw "trace#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: trace (5 of 5)"
   :sw "trace#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: showSpec (1 of 4)"
   :sw "showSpec#TF_WasBad_1"
   :use-goal-file t)

  ("Spec Transform: showSpec (2 of 4)"
   :sw "showSpec#TF_WasBad_2"
   :use-goal-file t)

  ("Spec Transform: showSpec (3 of 4)"
   :sw "showSpec#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: showSpec (4 of 4)"
   :sw "showSpec#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: showElements (1 of 7)"
   :sw "showElements#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: showElements (2 of 7)"
   :sw "showElements#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: showElements (3 of 7)"
   :sw "showElements#TF_Bad_3"
   :use-goal-file t)

  ("Spec Transform: showElements (4 of 7)"
   :sw "showElements#TF_Bad_4"
   :use-goal-file t)

  ("Spec Transform: showElements (5 of 7)"
   :sw "showElements#TF_Bad_5"
   :use-goal-file t)

  ("Spec Transform: showElements (6 of 7)"
   :sw "showElements#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: showElements (7 of 7)"
   :sw "showElements#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: makeImportingSpec (1 of 2)"
   :sw "makeImportingSpec#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: makeImportingSpec (2 of 2)"
   :sw "makeImportingSpec#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: copySpec (1 of 4)"
   :sw "copySpec#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: copySpec (2 of 4)"
   :sw "copySpec#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: copySpec (3 of 4)"
   :sw "copySpec#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: copySpec (4 of 4)"
   :sw "copySpec#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: copyOp (1 of 4)"
   :sw "copyOp#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: copyOp (2 of 4)"
   :sw "copyOp#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: copyOp (3 of 4)"
   :sw "copyOp#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: copyOp (4 of 4)"
   :sw "copyOp#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (1 of 11)"
   :sw "isomorphism_BitBool#TF_Bad_1"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (2 of 11)"
   :sw "isomorphism_BitBool#TF_Bad_2"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (3 of 11)"
   :sw "isomorphism_BitBool#TF_Bad_3"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (4 of 11)"
   :sw "isomorphism_BitBool#TF_Bad_4"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (5 of 11)"
   :sw "isomorphism_BitBool#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (6 of 11)"
   :sw "isomorphism_BitBool#TF_Good_2"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (7 of 11)"
   :sw "isomorphism_BitBool#TF_Good_3"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (8 of 11)"
   :sw "isomorphism_BitBool#TF_Good_4"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (9 of 11)"
   :sw "isomorphism_BitBool#TF_Good_5"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (10 of 11)"
   :sw "isomorphism_BitBool#TF_Good_7"
   :use-goal-file t)

  ("Spec Transform: isomorphism - BitBool (11 of 11)"
   :sw "isomorphism_BitBool#TF_Good_6"
   :use-goal-file t)

  ("Spec Transform: isomorphism - IsoMap (1 of 2)"
   :sw "isomorphism_IsoMap#TF_Good_1"
   :use-goal-file t)

  ("Spec Transform: isomorphism - IsoMap (2 of 2)"
   :sw "isomorphism_IsoMap#TF_Good_2"
   :use-goal-file t)

  )
