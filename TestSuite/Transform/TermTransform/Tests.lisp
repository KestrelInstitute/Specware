
(cl-user::sw-init)

(test-directories ".")

(test

  ("Term Transform: unknown (1 of 2)"
   :sw "unknown#TF_Bad_1"
   :use-goal-file t)

  ("Term Transform: unknown (2 of 2)"
   :sw "unknown#TF_Bad_2"
   :use-goal-file t)

  ("Term Transform: syntax"
   :sw "syntax"
   :use-goal-file t)

  ("Term Transform: at (1 of 2)"
   :sw "at#TF_Bad_1"
   :use-goal-file t)

  ("Term Transform: at (2 of 2)"
   :sw "at#TF_Good_1"
   :use-goal-file t)

  ("Term Transform: lr (1 of 4)"
   :sw "lr#TF_Bad_1"
   :use-goal-file t)

  ("Term Transform: lr (2 of 4)"
   :sw "lr#TF_Bad_2"
   :use-goal-file t)

  ("Term Transform: lr (3 of 4)"
   :sw "lr#TF_Good_1"
   :use-goal-file t)

  ("Term Transform: lr (4 of 4)"
   :sw "lr#TF_Good_2"
   :use-goal-file t)

  ("Term Transform: simpIf (1 of 8)"
   :sw "simpIf#TF_Bad_1"
   :use-goal-file t)

  ("Term Transform: simpIf (2 of 8)"
   :sw "simpIf#TF_Bad_2"
   :use-goal-file t)

  ("Term Transform: simpIf (3 of 8)"
   :sw "simpIf#TF_Good_1"
   :use-goal-file t)

  ("Term Transform: simpIf (4 of 8)"
   :sw "simpIf#TF_Good_2"
   :use-goal-file t)

  ("Term Transform: simpIf (5 of 8)"
   :sw "simpIf#TF_Good_3"
   :use-goal-file t)

  ("Term Transform: simpIf (6 of 8)"
   :sw "simpIf#TF_Good_4"
   :use-goal-file t)

  ("Term Transform: simpIf (7 of 8)"
   :sw "simpIf#TF_Good_5"
   :use-goal-file t)

  ("Term Transform: simpIf (8 of 8)"
   :sw "simpIf#TF_Good_6"
   :use-goal-file t)

  ("Term Transform: structureEx (1 of 6)"
   :sw "structureEx#TF_Good_1"
   :use-goal-file t)

  ("Term Transform: structureEx (2 of 6)"
   :sw "structureEx#TF_Good_2"
   :use-goal-file t)

  ("Term Transform: structureEx (3 of 6)"
   :sw "structureEx#TF_Good_3"
   :use-goal-file t)

  ("Term Transform: structureEx (4 of 6)"
   :sw "structureEx#TF_Good_4"
   :use-goal-file t)

  ("Term Transform: structureEx (5 of 6)"
   :sw "structureEx#TF_Good_5"
   :use-goal-file t)

  ("Term Transform: structureEx (6 of 6)"
   :sw "structureEx#TF_Good_6"
   :use-goal-file t)

  ("Term Transform: move (1 of 9)"
   :sw "move#TF_Bad_1"
   :use-goal-file t)

  ("Term Transform: move (2 of 9)"
   :sw "move#TF_Bad_2"
   :use-goal-file t)

  ("Term Transform: move (3 of 9)"
   :sw "move#TF_Bad_3"
   :use-goal-file t)

  ("Term Transform: move (4 of 9)"
   :sw "move#TF_Bad_4"
   :use-goal-file t)

  ("Term Transform: move (5 of 9)"
   :sw "move#TF_Good_1"
   :use-goal-file t)

  ("Term Transform: move (6 of 9)"
   :sw "move#TF_Good_2"
   :use-goal-file t)

  ("Term Transform: move (7 of 9)"
   :sw "move#TF_Good_3"
   :use-goal-file t)

  ("Term Transform: move (8 of 9)"
   :sw "move#TF_Good_4"
   :use-goal-file t)

  ("Term Transform: move (9 of 9)"
   :sw "move#TF_Good_5"
   :use-goal-file t)

  )
