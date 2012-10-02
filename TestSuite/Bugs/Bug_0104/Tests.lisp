(test-directories ".")

(test 

 ("Bug 0104 : Erroneous code for non-constructive expression."
  :swe-spec "NonConstructive"
  :swe      "notFalse"
  ;; another option is to look for '(:|Bool| . T), which is what a very
  ;; smart evaluator could return
  :value    '(:|Apply|
              . #((:|Fun|
                   . #((:|Equals|)
                       (:|Arrow|
                        . #((:|Product|
                             (("1" :|Arrow|
                                   . #((:|Base| . #((:|Qualified| "Nat" . "Nat") NIL (:|Internal| . "")))
                                       (:|Base| . #((:|Qualified| "Nat" . "Nat") NIL (:|Internal| . "")))
                                       (:|Internal| . "")))
                              ("2" :|Arrow|
                                   . #((:|Base| . #((:|Qualified| "Nat" . "Nat") NIL (:|Internal| . "")))
                                       (:|Base| . #((:|Qualified| "Nat" . "Nat") NIL (:|Internal| . "")))
                                       (:|Internal| . ""))))
                             :|Internal| . "")
                            (:|Boolean| :|Internal| . "no position")
                            (:|Internal| . "")))
                       (:|Internal| . "")))
                  (:|Record|
                   (("1" :|Lambda|
                         (#((:|VarPat| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")
                            (:|Fun| . #((:|Bool| . T) (:|Boolean| :|Internal| . "no position")
                                        (:|Internal| . "no position")))
                            (:|Var| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")))
                         :|Internal| . "no position")
                    ("2" :|Let|
                         . #((((:|VarPat|
                                 ("f" :|Arrow|
                                      . #((:|TyVar| "a" :|Internal| . "")
                                          (:|TyVar| "b" :|Internal| . "")
                                          (:|Internal| . "")))
                                 :|Internal| . "no position")
                               :|Lambda|
                               (#((:|VarPat| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")
                                  (:|Fun| . #((:|Bool| . T) (:|Boolean| :|Internal| . "no position")
                                              (:|Internal| . "no position")))
                                  (:|Var| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")))
                               :|Internal| . "no position")
                              ((:|VarPat|
                                 ("g" :|Arrow|
                                      . #((:|TyVar| "b" :|Internal| . "")
                                          (:|TyVar| "c" :|Internal| . "")
                                          (:|Internal| . "")))
                                 :|Internal| . "no position")
                               :|Lambda|
                               (#((:|VarPat| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")
                                  (:|Fun| . #((:|Bool| . T) (:|Boolean| :|Internal| . "no position")
                                              (:|Internal| . "no position")))
                                  (:|Var| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")))
                               :|Internal| . "no position"))
                             (:|Lambda|
                              (#((:|VarPat| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")
                                 (:|Fun| . #((:|Bool| . T) (:|Boolean| :|Internal| . "no position")
                                             (:|Internal| . "no position")))
                                 (:|Apply| . #((:|Var|
                                                ("g" :|Arrow|
                                                 . #((:|TyVar| "b" :|Internal| . "")
                                                     (:|TyVar| "c" :|Internal| . "")
                                                     (:|Internal| . "")))
                                                :|Internal| . "")
                                               (:|Apply|
                                                . #((:|Var| ("f" :|Arrow| . #((:|TyVar| "a" :|Internal| . "")
                                                                              (:|TyVar| "b" :|Internal| . "")
                                                                              (:|Internal| . "")))
                                                     :|Internal| . "")
                                                    (:|Var| ("x" :|TyVar| "a" :|Internal| . "") :|Internal| . "")
                                                    (:|Internal| . "")))
                                               (:|Internal| . "")))))
                              :|Internal| . "no position")
                             (:|Internal| . "no position"))))
                   :|Internal| . "no position")
                  (:|Internal| . "no position")))
  :value-predicate #'(lambda (x y) 
		       (and (equal (car x) :|Unevaluated|)
			    (METASLANG::equalTerm?-2 (cdr x) y)))
  )
 )
