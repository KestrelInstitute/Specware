(in-package "ANNSPEC")

(defun SPECCALC::mergeOpInfo-1 (newPOpInfo) 
  #'(lambda (optOldPOpInfo) 
     #'(lambda (|!position|) 
        (block 
         nil 
         (if (eq (car optOldPOpInfo) :|None|) 
             (return (SPECCALC::|!return| newPOpInfo))) 
         (let ((pV39 (svref newPOpInfo 3))
               (pV38 (svref newPOpInfo 2))
               (pV37 (svref newPOpInfo 1))) 
           (if (eq (car optOldPOpInfo) :|Some|) 
               (let ((pV40 (cdr optOldPOpInfo))) 
                 (let ((pV44 (svref pV40 3))
                       (pV43 (svref pV40 2))) 
                   (return 
                    (let ((op_names 
                           (LISTUTILITIES::listUnion 
                            (svref pV40 0) 
                            (svref newPOpInfo 0)))) 
                      (if (BOOLEAN-SPEC::~ 
                           (slang-built-in::slang-term-equals 
                            pV37 
                            (svref pV40 1))) 
                          (SPECCALC::raise 
                           (cons 
                            :|SpecError| 
                            (cons 
                             |!position| 
                             (STRING-SPEC::^ 
                              (STRING-SPEC::^ 
                               "Merged versions of Op " 
                               (SPECCALC::printAliases op_names)) 
                              " have different fixity")))) 
                          (let ((happy? 
                                 (block 
                                  nil 
                                  (if (null (car pV43)) 
                                      (if (eq (car (cdr pV43)) :|MetaTyVar|) 
                                          (return t))) 
                                  (if (null (car pV38)) 
                                      (if (eq (car (cdr pV38)) :|MetaTyVar|) 
                                          (return t))) 
                                  (return 
                                   (slang-built-in::slang-term-equals 
                                    (car pV38) 
                                    (car pV43))) 
                                  (return t)))) 
                            (if (BOOLEAN-SPEC::~ happy?) 
                                (SPECCALC::raise 
                                 (cons 
                                  :|SpecError| 
                                  (cons 
                                   |!position| 
                                   (STRING-SPEC::^ 
                                    (STRING-SPEC::^ 
                                     (STRING-SPEC::^ 
                                      (STRING-SPEC::^ 
                                       (STRING-SPEC::^ 
                                        (STRING-SPEC::^ 
                                         "Merged versions of Op " 
                                         (SPECCALC::printAliases op_names)) 
                                        " have incompatible sorts:") 
                                       "
 ") 
                                      (ANNSPECPRINTER::printSortScheme-1 pV38)) 
                                     "
 ") 
                                    (ANNSPECPRINTER::printSortScheme-1 pV43))))) 
                                (block 
                                 nil 
                                 (if (null pV44) 
                                     (if (null pV39) 
                                         (return 
                                          (SPECCALC::|!return| 
                                           (vector op_names pV37 pV38 nil))) 
                                         (if (consp pV39) 
                                             (return 
                                              (SPECCALC::|!return| 
                                               (vector op_names pV37 pV38 pV39))))) 
                                     (if (consp pV44) 
                                         (if (null pV39) 
                                             (return 
                                              (SPECCALC::|!return| 
                                               (vector op_names pV37 pV38 pV44)))))) 
                                 (return 
                                  (let ((combined_defs 
                                         (LIST-SPEC::foldl-1-1-1 
                                          #'(lambda (x) 
                                             (let ((result_defs (cdr x))
                                                   (new_def (car x))) 
                                               (if (LIST-SPEC::|!exists|-1-1 
                                                    #'(lambda (old_def) 
                                                       (METASLANG::equalTerm? 
                                                        (cdr new_def) 
                                                        (cdr old_def))) 
                                                    result_defs) 
                                                   result_defs 
                                                   (LIST-SPEC::|!cons| 
                                                    new_def 
                                                    result_defs)))) 
                                          pV44 
                                          pV39))) 
                                    (SPECCALC::|!return| 
                                     (vector op_names pV37 pV38 combined_defs)))))))))))))) 
         (error "Nonexhaustive match failure in mergeOpInfo")))))

(defun SPECCALC::mergeSortInfo-1 (newPSortInfo) 
  #'(lambda (optOldPSortInfo) 
     #'(lambda (|!position|) 
        (block 
         nil 
         (if (eq (car optOldPSortInfo) :|None|) 
             (return (SPECCALC::|!return| newPSortInfo))) 
         (let ((pV19 (svref newPSortInfo 2))
               (pV18 (svref newPSortInfo 1))) 
           (if (eq (car optOldPSortInfo) :|Some|) 
               (let ((pV20 (cdr optOldPSortInfo))) 
                 (let ((pV23 (svref pV20 2))
                       (pV22 (svref pV20 1))) 
                   (return 
                    (let ((sort_names 
                           (LISTUTILITIES::listUnion 
                            (svref pV20 0) 
                            (svref newPSortInfo 0)))) 
                      (if (BOOLEAN-SPEC::~ 
                           (slang-built-in::slang-term-equals pV18 pV22)) 
                          (SPECCALC::raise 
                           (cons 
                            :|SpecError| 
                            (cons 
                             |!position| 
                             (STRING-SPEC::^ 
                              (STRING-SPEC::^ 
                               (STRING-SPEC::^ 
                                (STRING-SPEC::^ 
                                 (STRING-SPEC::^ 
                                  (STRING-SPEC::^ 
                                   "Merged versions of Sort " 
                                   (SPECCALC::printAliases sort_names)) 
                                  " have differing type variables:") 
                                 "
 ") 
                                (SPECCALC::printTypeVars pV22)) 
                               "
 ") 
                              (SPECCALC::printTypeVars pV18))))) 
                          (block 
                           nil 
                           (if (null pV23) 
                               (if (null pV19) 
                                   (return 
                                    (SPECCALC::|!return| 
                                     (vector sort_names pV18 nil))) 
                                   (if (consp pV19) 
                                       (return 
                                        (SPECCALC::|!return| 
                                         (vector sort_names pV18 pV19))))) 
                               (if (consp pV23) 
                                   (if (null pV19) 
                                       (return 
                                        (SPECCALC::|!return| 
                                         (vector sort_names pV22 pV23)))))) 
                           (return 
                            (let ((combined_defs 
                                   (LIST-SPEC::foldl-1-1-1 
                                    #'(lambda (x) 
                                       (let ((combined_defs (cdr x))
                                             (new_def (car x))) 
                                         (if (LIST-SPEC::|!exists|-1-1 
                                              #'(lambda (old_def) 
                                                 (equalSortScheme? 
                                                  new_def 
                                                  old_def)) 
                                              combined_defs) 
                                             combined_defs 
                                             (LIST-SPEC::|!cons| 
                                              new_def 
                                              combined_defs)))) 
                                    pV23 
                                    pV19))) 
                              (SPECCALC::|!return| 
                               (vector sort_names pV22 combined_defs)))))))))))) 
         (error "Nonexhaustive match failure in mergeSortInfo")))))

(defun SPECUNION::unionOpMaps (old_op_map) 
  #'(lambda (new_op_map) 
     (labels 
       ((augmentOpMap (new_qualifier new_id new_info merged_op_map) 
         (let ((pV5 (LIST-SPEC::hd (svref new_info 0)))) 
           (block 
            nil 
            (if (eq (car pV5) :|Qualified|) 
                (let ((pV6 (cdr pV5))) 
                  (return 
                   (if (lisp::and 
                        (string=  new_qualifier (car pV6)) 
                        (string=  new_id (cdr pV6))) 
                       (let ((optional_old_info 
                              (findAQualifierMap 
                               merged_op_map 
                               new_qualifier 
                               new_id))) 
                         (SPECCALC::monadBind 
                          (funcall (funcall (SPECCALC::mergeOpInfo-1 new_info) 
                                            optional_old_info) 
                                   POSITION-SPEC::noPos) 
                          #'(lambda (merged_info) 
                             (SPECCALC::monadBind 
                              (SPECCALC::|!return| (svref merged_info 0)) 
                              #'(lambda (all_names) 
                                 (funcall (funcall (SPECCALC::foldM 
                                                    #'(lambda (merged_op_map) 
                                                       #'(lambda (pV1) 
                                                          (block 
                                                           nil 
                                                           (if (eq 
                                                                (car pV1) 
                                                                :|Qualified|) 
                                                               (let ((pV2 
                                                                      (cdr pV1))) 
                                                                 (return 
                                                                  (SPECCALC::|!return| 
                                                                   (insertAQualifierMap 
                                                                    merged_op_map 
                                                                    (car pV2) 
                                                                    (cdr pV2) 
                                                                    merged_info))))) 
                                                           (error 
                                                            "Nonexhaustive match failure in unionOpMaps"))))) 
                                                   merged_op_map) 
                                          all_names)))))) 
                       (SPECCALC::|!return| merged_op_map))))) 
            (error "Nonexhaustive match failure in unionOpMaps"))))) 
       (funcall (funcall (SPECCALC::foldOverQualifierMap 
                          #'(lambda (x) 
                             (augmentOpMap 
                              (svref x 0) 
                              (svref x 1) 
                              (svref x 2) 
                              (svref x 3)))) 
                         old_op_map) 
                new_op_map))))

(defun SPECUNION::unionSortMaps (old_sort_map) 
  #'(lambda (new_sort_map) 
     (labels 
       ((augmentSortMap (new_qualifier new_id new_info merged_sort_map) 
         (let ((pV5 (LIST-SPEC::hd (svref new_info 0)))) 
           (block 
            nil 
            (if (eq (car pV5) :|Qualified|) 
                (let ((pV6 (cdr pV5))) 
                  (return 
                   (if (lisp::and 
                        (string=  new_qualifier (car pV6)) 
                        (string=  new_id (cdr pV6))) 
                       (let ((optional_old_info 
                              (findAQualifierMap 
                               merged_sort_map 
                               new_qualifier 
                               new_id))) 
                         (SPECCALC::monadBind 
                          (funcall (funcall (SPECCALC::mergeSortInfo-1 new_info) 
                                            optional_old_info) 
                                   POSITION-SPEC::noPos) 
                          #'(lambda (merged_info) 
                             (SPECCALC::monadBind 
                              (SPECCALC::|!return| (svref merged_info 0)) 
                              #'(lambda (all_names) 
                                 (funcall (funcall (SPECCALC::foldM 
                                                    #'(lambda (merged_sort_map) 
                                                       #'(lambda (pV1) 
                                                          (block 
                                                           nil 
                                                           (if (eq 
                                                                (car pV1) 
                                                                :|Qualified|) 
                                                               (let ((pV2 
                                                                      (cdr pV1))) 
                                                                 (return 
                                                                  (SPECCALC::|!return| 
                                                                   (insertAQualifierMap 
                                                                    merged_sort_map 
                                                                    (car pV2) 
                                                                    (cdr pV2) 
                                                                    merged_info))))) 
                                                           (error 
                                                            "Nonexhaustive match failure in unionSortMaps"))))) 
                                                   merged_sort_map) 
                                          all_names)))))) 
                       (SPECCALC::|!return| merged_sort_map))))) 
            (error "Nonexhaustive match failure in unionSortMaps"))))) 
       (funcall (funcall (SPECCALC::foldOverQualifierMap 
                          #'(lambda (x) 
                             (augmentSortMap 
                              (svref x 0) 
                              (svref x 1) 
                              (svref x 2) 
                              (svref x 3)))) 
                         old_sort_map) 
                new_sort_map))))

(defun SPECCALC::complainIfAmbiguous-1 (spc) 
  #'(lambda (|!position|) 
     (let ((ambiguous_sorts 
            (foldriAQualifierMap-1-1-1 
             #'(lambda (x) 
                (let ((pV14 (svref x 3))
                      (pV13 (svref x 2))) 
                  (block 
                   nil 
                   (let ((pV17 (svref pV13 2))) 
                     (return 
                      (block 
                       nil 
                       (if (null pV17) 
                           (return pV14) 
                           (if (consp pV17) (if (null (cdr pV17)) (return pV14)))) 
                       (return (LISTUTILITIES::insert pV13 pV14))))) 
                   (error "Nonexhaustive match failure in complainIfAmbiguous")))) 
             nil 
             (svref spc 3)))) 
       (let ((ambiguous_ops 
              (foldriAQualifierMap-1-1-1 
               #'(lambda (x) 
                  (let ((pV32 (svref x 3))
                        (pV31 (svref x 2))) 
                    (block 
                     nil 
                     (let ((pV36 (svref pV31 3))) 
                       (return 
                        (block 
                         nil 
                         (if (null pV36) 
                             (return pV32) 
                             (if (consp pV36) 
                                 (if (null (cdr pV36)) (return pV32)))) 
                         (return (LISTUTILITIES::insert pV31 pV32))))) 
                     (error "Nonexhaustive match failure in complainIfAmbiguous")))) 
               nil 
               (svref spc 1)))) 
         (if (lisp::and 
              (slang-built-in::slang-term-equals ambiguous_sorts nil) 
              (slang-built-in::slang-term-equals ambiguous_ops nil)) 
             (SPECCALC::|!return| spc) 
             (labels 
               ((print_qid (pV37) 
                 (block 
                  nil 
                  (if (eq (car pV37) :|Qualified|) 
                      (let ((pV38 (cdr pV37))) 
                        (let ((pV40 (cdr pV38))
                              (pV39 (car pV38))) 
                          (return 
                           (if (string=  pV39 METASLANG::UnQualified) 
                               pV40 
                               (STRING-SPEC::^ (STRING-SPEC::^ pV39 ".") pV40)))))) 
                  (error "Nonexhaustive match failure in complainIfAmbiguous")))) 
               (let ((sort_msg 
                      (block 
                       nil 
                       (if (null ambiguous_sorts) 
                           (return "") 
                           (if (consp ambiguous_sorts) 
                               (let ((pV59 (svref (car ambiguous_sorts) 0))) 
                                 (if (consp pV59) 
                                     (return 
                                      (STRING-SPEC::^ 
                                       (LIST-SPEC::foldl-1-1-1 
                                        #'(lambda (x) 
                                           (block 
                                            nil 
                                            (let ((pV49 (svref (car x) 0))) 
                                              (if (consp pV49) 
                                                  (return 
                                                   (STRING-SPEC::^ 
                                                    (STRING-SPEC::^ (cdr x) ", ") 
                                                    (print_qid (car pV49)))))) 
                                            (error 
                                             "Nonexhaustive match failure in complainIfAmbiguous"))) 
                                        (STRING-SPEC::^ 
                                         "Ambiguous sorts: " 
                                         (print_qid (car pV59))) 
                                        (cdr ambiguous_sorts)) 
                                       "
")))))) 
                       (error 
                        "Nonexhaustive match failure in complainIfAmbiguous")))) 
                 (let ((op_msg 
                        (block 
                         nil 
                         (if (null ambiguous_ops) 
                             (return "") 
                             (if (consp ambiguous_ops) 
                                 (let ((pV86 (svref (car ambiguous_ops) 0))) 
                                   (if (consp pV86) 
                                       (return 
                                        (STRING-SPEC::^ 
                                         (LIST-SPEC::foldl-1-1-1 
                                          #'(lambda (x) 
                                             (block 
                                              nil 
                                              (let ((pV75 (svref (car x) 0))) 
                                                (if (consp pV75) 
                                                    (return 
                                                     (STRING-SPEC::^ 
                                                      (STRING-SPEC::^ 
                                                       (cdr x) 
                                                       ", ") 
                                                      (print_qid (car pV75)))))) 
                                              (error 
                                               "Nonexhaustive match failure in complainIfAmbiguous"))) 
                                          (STRING-SPEC::^ 
                                           "Ambiguous ops: " 
                                           (print_qid (car pV86))) 
                                          (cdr ambiguous_ops)) 
                                         "
")))))) 
                         (error 
                          "Nonexhaustive match failure in complainIfAmbiguous")))) 
                   (let ((spc_msg 
                          (STRING-SPEC::^ 
                           "
 in following spec: 
" 
                           (ANNSPECPRINTER::printSpec-1 spc)))) 
                     (SPECCALC::raise 
                      (cons 
                       :|SpecError| 
                       (cons 
                        |!position| 
                        (STRING-SPEC::^ 
                         (STRING-SPEC::^ (STRING-SPEC::^ "
" sort_msg) op_msg) 
                         spc_msg)))))))))))))

(defparameter SPECCALC::declare_proposition_symbol 
  (LISP-SPEC::|!symbol| "SNARK" "DECLARE-PROPOSITION-SYMBOL"))

(defun SPECCALC::snarkBaseSort (spc s rng?) 
  (block 
   nil 
   (if (eq (car s) :|Base|) 
       (let ((pV21 (svref (cdr s) 0))) 
         (if (eq (car pV21) :|Qualified|) 
             (let ((pV24 (cdr pV21))) 
               (let ((pV26 (cdr pV24))
                     (pV25 (car pV24))) 
                 (progn (if (string=  "Nat" pV25) 
                            (if (string=  "Nat" pV26) 
                                (return (LISP-SPEC::|!symbol| "SNARK" "NATURAL"))) 
                            (if (string=  "Integer" pV25) 
                                (if (string=  "Integer" pV26) 
                                    (return 
                                     (LISP-SPEC::|!symbol| "SNARK" "INTEGER"))) 
                                (if (string=  "Boolean" pV25) 
                                    (if (string=  "Boolean" pV26) 
                                        (return 
                                         (if rng? 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "BOOLEAN") 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "TRUE"))))))) 
                        (return 
                         (let ((res 
                                (SPECCALC::findBuiltInSort 
                                 spc 
                                 (cons :|Qualified| (cons pV25 pV26)) 
                                 rng?))) res)) 
                        (return 
                         (if rng? 
                             (LISP-SPEC::|!symbol| "SNARK" pV26) 
                             (LISP-SPEC::|!symbol| "SNARK" pV26)))))))) 
       (if (eq (car s) :|Product|) 
           (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
           (if (eq (car s) :|Arrow|) 
               (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
               (if (eq (car s) :|TyVar|) 
                   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")))))) 
   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE"))))

(defun SPECCALC::snarkPropositionSymbolDecl (name) 
  (LISP-SPEC::|!list| 
   (cons 
    SPECCALC::declare_proposition_symbol 
    (cons (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) nil))))

(defun SPECCALC::snarkFunctionNoArityDecl (spc name srt) 
  (block 
   nil 
   (if (eq (car srt) :|Base|) 
       (let ((pV8 (svref (cdr srt) 0))) 
         (if (eq (car pV8) :|Qualified|) 
             (progn (if (string=  "Boolean" (cdr (cdr pV8))) 
                        (return (SPECCALC::snarkPropositionSymbolDecl name))) 
                    (return 
                     (LISP-SPEC::|!list| 
                      (cons 
                       SPECCALC::declare_constant 
                       (cons 
                        (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) 
                        (cons 
                         (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                         (cons 
                          (LISP-SPEC::|!quote| (SPECCALC::snarkBaseSort srt t)) 
                          nil)))))))))) 
   (return (LISP-SPEC::|!nil|))))

(defun SPECCALC::snarkFunctionCurryNoArityDecl (spc name srt) 
  (SPECCALC::snarkFunctionNoArityDecl spc name srt))

(defparameter SPECCALC::baseSorts 
  (cons 
   (LISP-SPEC::|!list| 
    (cons 
     SPECCALC::declare_sort 
     (cons (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" "Option")) nil))) 
   (cons 
    (LISP-SPEC::|!list| 
     (cons 
      SPECCALC::declare_sort 
      (cons (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" "List")) nil))) 
    nil)))

(defun SPECCALC::snarkVar-1 (v) 
  (LISP-SPEC::|!symbol| "SNARK" (STRING-SPEC::^ "?" (car v))))

(defun SPECCALC::mkNewSnarkTerm (context term) 
  (let ((vars (UTILITIES::freeVars term))) 
    (let ((newFun (SPECCALC::mkNewSnarkOp context))) 
      (let ((snarkVars 
             (LIST-SPEC::|!map|-1-1 
              #'(lambda (v) (SPECCALC::snarkVar-1 v)) 
              vars))) 
        (block 
         nil 
         (if (null snarkVars) (return newFun)) 
         (return (LISP-SPEC::|!cons| newFun (LISP-SPEC::|!list| snarkVars))))))))

(defun SPECCALC::mkSnarkTermApp (context sp dpn vars f arg) 
  (let ((args 
         (block 
          nil 
          (if (eq (car arg) :|Record|) 
              (return 
               (LIST-SPEC::|!map|-1-1 #'(lambda (x) (cdr x)) (car (cdr arg))))) 
          (return (cons arg nil))))) 
    (block 
     nil 
     (if (eq (car f) :|Op|) 
         (let ((pV15 (car (cdr f)))) 
           (if (eq (car pV15) :|Qualified|) 
               (let ((pV17 (cdr pV15))) 
                 (return 
                  (let ((snarkArgs 
                         (LIST-SPEC::|!map|-1-1 
                          #'(lambda (arg) 
                             (SPECCALC::mkSnarkTerm context sp dpn vars arg)) 
                          args))) 
                    (LISP-SPEC::|!cons| 
                     (LISP-SPEC::|!symbol| 
                      "SNARK" 
                      (SPECCALC::mkSnarkName (car pV17) (cdr pV17))) 
                     (LISP-SPEC::|!list| snarkArgs))))))) 
         (if (eq (car f) :|Project|) 
             (return 
              (let ((snarkArgs 
                     (LIST-SPEC::|!map|-1-1 
                      #'(lambda (arg) 
                         (SPECCALC::mkSnarkTerm context sp dpn vars arg)) 
                      args))) 
                (LISP-SPEC::|!cons| 
                 (LISP-SPEC::|!symbol| 
                  "SNARK" 
                  (SPECCALC::mkSnarkName "" (STRING-SPEC::^ "project_" (cdr f)))) 
                 (LISP-SPEC::|!list| snarkArgs)))) 
             (if (eq (car f) :|Embed|) 
                 (return 
                  (let ((snarkArgs 
                         (LIST-SPEC::|!map|-1-1 
                          #'(lambda (arg) 
                             (SPECCALC::mkSnarkTerm context sp dpn vars arg)) 
                          args))) 
                    (LISP-SPEC::|!cons| 
                     (LISP-SPEC::|!symbol| 
                      "SNARK" 
                      (SPECCALC::mkSnarkName 
                       "" 
                       (STRING-SPEC::^ "embed_" (car (cdr f))))) 
                     (LISP-SPEC::|!list| snarkArgs))))))) 
     (error "Nonexhaustive match failure in mkSnarkTermApp"))))

(defun SPECCALC::mkSnarkTerm (context sp dpn vars term) 
  (block 
   nil 
   (if (eq (car term) :|Apply|) 
       (let ((pV14 (cdr term))) 
         (let ((pV31 (svref pV14 0))) 
           (if (eq (car pV31) :|Fun|) 
               (return 
                (SPECCALC::mkSnarkTermApp 
                 context 
                 sp 
                 dpn 
                 vars 
                 (svref (cdr pV31) 0) 
                 (svref pV14 1)))))) 
       (if (eq (car term) :|IfThenElse|) 
           (let ((pV13 (cdr term))) 
             (return 
              (LISP-SPEC::|!list| 
               (cons 
                (LISP-SPEC::|!symbol| "SNARK" "IF") 
                (cons 
                 (SPECCALC::mkSnarkTerm context sp dpn vars (svref pV13 0)) 
                 (cons 
                  (SPECCALC::mkSnarkTerm context sp dpn vars (svref pV13 1)) 
                  (cons 
                   (SPECCALC::mkSnarkTerm context sp dpn vars (svref pV13 2)) 
                   nil))))))) 
           (if (eq (car term) :|Fun|) 
               (let ((pV17 (svref (cdr term) 0))) 
                 (if (eq (car pV17) :|Op|) 
                     (let ((pV22 (car (cdr pV17)))) 
                       (if (eq (car pV22) :|Qualified|) 
                           (let ((pV24 (cdr pV22))) 
                             (return 
                              (LISP-SPEC::|!symbol| 
                               "SNARK" 
                               (SPECCALC::mkSnarkName (car pV24) (cdr pV24))))))) 
                     (if (eq (car pV17) :|Nat|) 
                         (return (LISP-SPEC::|!nat| (cdr pV17)))))) 
               (if (eq (car term) :|Var|) 
                   (return (SPECCALC::snarkVar-1 (car (cdr term)))))))) 
   (return (SPECCALC::mkNewSnarkTerm context term))))

(defun SPECCALC::mkSnarkFmlaApp (context sp dpn vars f srt arg) 
  (let ((args 
         (block 
          nil 
          (if (eq (car arg) :|Record|) 
              (return 
               (LIST-SPEC::|!map|-1-1 #'(lambda (x) (cdr x)) (car (cdr arg))))) 
          (return (cons arg nil))))) 
    (block 
     nil 
     (if (eq (car f) :|Op|) 
         (let ((pV72 (car (cdr f)))) 
           (if (eq (car pV72) :|Qualified|) 
               (let ((pV74 (cdr pV72))) 
                 (let ((pV76 (cdr pV74))
                       (pV75 (car pV74))) 
                   (progn (if (string=  "Boolean" pV75) 
                              (return 
                               (let ((snarkArgs 
                                      (LIST-SPEC::|!map|-1-1 
                                       #'(lambda (arg) 
                                          (SPECCALC::mkSnarkFmla 
                                           context 
                                           sp 
                                           dpn 
                                           vars 
                                           nil 
                                           arg)) 
                                       args))) 
                                 (LISP-SPEC::|!cons| 
                                  (SPECCALC::snarkBoolOp pV76) 
                                  (LISP-SPEC::|!list| snarkArgs))))) 
                          (return 
                           (let ((snarkArgs 
                                  (LIST-SPEC::|!map|-1-1 
                                   #'(lambda (arg) 
                                      (SPECCALC::mkSnarkTerm 
                                       context 
                                       sp 
                                       dpn 
                                       vars 
                                       arg)) 
                                   args))) 
                             (LISP-SPEC::|!cons| 
                              (LISP-SPEC::|!symbol| 
                               "SNARK" 
                               (SPECCALC::mkSnarkName pV75 pV76)) 
                              (LISP-SPEC::|!list| snarkArgs))))))))) 
         (if (eq (car f) :|Embedded|) 
             (let ((pV70 (cdr f))) 
               (return 
                (labels 
                  ((boolArgp (srt) 
                    (block 
                     nil 
                     (if (eq (car srt) :|Base|) 
                         (let ((pV15 (svref (cdr srt) 0))) 
                           (if (eq (car pV15) :|Qualified|) 
                               (let ((pV18 (cdr pV15))) 
                                 (return 
                                  (lisp::or 
                                   (string=  (car pV18) "Boolean") 
                                   (string=  (cdr pV18) "Boolean"))))))) 
                     (return nil)))) 
                  (block 
                   nil 
                   (if (eq (car srt) :|Arrow|) 
                       (return 
                        (let ((isfmla (boolArgp (svref (cdr srt) 0)))) 
                          (let ((snarkArg 
                                 (if isfmla 
                                     (SPECCALC::mkSnarkFmla 
                                      context 
                                      sp 
                                      dpn 
                                      vars 
                                      nil 
                                      arg) 
                                     (SPECCALC::mkSnarkTerm 
                                      context 
                                      sp 
                                      dpn 
                                      vars 
                                      arg)))) 
                            (LISP-SPEC::|!cons| 
                             (LISP-SPEC::|!symbol| "SNARK" "embed?") 
                             (LISP-SPEC::|!list| 
                              (cons 
                               (LISP-SPEC::|!symbol| "SNARK" pV70) 
                               (cons snarkArg nil)))))))) 
                   (error "Nonexhaustive match failure in mkSnarkFmlaApp"))))) 
             (if (eq (car f) :|Equals|) 
                 (return 
                  (labels 
                    ((boolArgp (srt) 
                      (block 
                       nil 
                       (if (eq (car srt) :|Base|) 
                           (let ((pV32 (svref (cdr srt) 0))) 
                             (if (eq (car pV32) :|Qualified|) 
                                 (let ((pV35 (cdr pV32))) 
                                   (return 
                                    (lisp::or 
                                     (string=  (car pV35) "Boolean") 
                                     (string=  (cdr pV35) "Boolean"))))))) 
                       (return nil)))) 
                    (block 
                     nil 
                     (if (consp args) 
                         (let ((pV65 (cdr args))
                               (pV64 (car args))) 
                           (if (consp pV65) 
                               (let ((pV67 (car pV65))) 
                                 (if (null (cdr pV65)) 
                                     (return 
                                      (block 
                                       nil 
                                       (if (eq (car srt) :|Arrow|) 
                                           (let ((pV59 (svref (cdr srt) 0))) 
                                             (return 
                                              (block 
                                               nil 
                                               (if (eq (car pV59) :|Product|) 
                                                   (let ((pV55 (car (cdr pV59)))) 
                                                     (return 
                                                      (block 
                                                       nil 
                                                       (if (consp pV55) 
                                                           (let ((pV45 
                                                                  (cdr pV55))) 
                                                             (if (consp pV45) 
                                                                 (if (null 
                                                                      (cdr pV45)) 
                                                                     (return 
                                                                      (let ((isfmla 
                                                                             (lisp::or 
                                                                              (boolArgp 
                                                                               (cdr 
                                                                                (car 
                                                                                 pV55))) 
                                                                              (boolArgp 
                                                                               (cdr 
                                                                                (car 
                                                                                 pV45)))))) 
                                                                        (let ((snarkArg1 
                                                                               (if isfmla 
                                                                                   (SPECCALC::mkSnarkFmla 
                                                                                    context 
                                                                                    sp 
                                                                                    dpn 
                                                                                    vars 
                                                                                    nil 
                                                                                    pV64) 
                                                                                   (SPECCALC::mkSnarkTerm 
                                                                                    context 
                                                                                    sp 
                                                                                    dpn 
                                                                                    vars 
                                                                                    pV64)))) 
                                                                          (let ((snarkArg2 
                                                                                 (if isfmla 
                                                                                     (SPECCALC::mkSnarkFmla 
                                                                                      context 
                                                                                      sp 
                                                                                      dpn 
                                                                                      vars 
                                                                                      nil 
                                                                                      pV67) 
                                                                                     (SPECCALC::mkSnarkTerm 
                                                                                      context 
                                                                                      sp 
                                                                                      dpn 
                                                                                      vars 
                                                                                      pV67)))) 
                                                                            (if isfmla 
                                                                                (LISP-SPEC::|!cons| 
                                                                                 (LISP-SPEC::|!symbol| 
                                                                                  "SNARK" 
                                                                                  "IFF") 
                                                                                 (LISP-SPEC::|!list| 
                                                                                  (cons 
                                                                                   snarkArg1 
                                                                                   (cons 
                                                                                    snarkArg2 
                                                                                    nil)))) 
                                                                                (LISP-SPEC::|!cons| 
                                                                                 (LISP-SPEC::|!symbol| 
                                                                                  "SNARK" 
                                                                                  "=") 
                                                                                 (LISP-SPEC::|!list| 
                                                                                  (cons 
                                                                                   snarkArg1 
                                                                                   (cons 
                                                                                    snarkArg2 
                                                                                    nil))))))))))))) 
                                                       (error 
                                                        "Nonexhaustive match failure in mkSnarkFmlaApp"))))) 
                                               (error 
                                                "Nonexhaustive match failure in mkSnarkFmlaApp"))))) 
                                       (error 
                                        "Nonexhaustive match failure in mkSnarkFmlaApp")))))))) 
                     (error "Nonexhaustive match failure in mkSnarkFmlaApp"))))))) 
     (error "Nonexhaustive match failure in mkSnarkFmlaApp"))))

(defun SPECCALC::findPBuiltInSort (pV60 pV61 pV62) 
  (block 
   nil 
   (if (eq (car pV61) :|Qualified|) 
       (let ((pV65 (cdr (cdr pV61)))) 
         (return 
          (let ((|!optSrt| (STANDARDSPEC::findTheSort pV60 pV61))) 
            (block 
             nil 
             (if (eq (car |!optSrt|) :|Some|) 
                 (let ((pV59 (svref (cdr |!optSrt|) 2))) 
                   (return 
                    (labels 
                      ((builtinSort? (s) 
                        (block 
                         nil 
                         (if (eq (car s) :|Base|) 
                             (let ((pV11 (svref (cdr s) 0))) 
                               (if (eq (car pV11) :|Qualified|) 
                                   (let ((pV14 (cdr pV11))) 
                                     (let ((pV16 (cdr pV14))
                                           (pV15 (car pV14))) 
                                       (if (string=  "Nat" pV15) 
                                           (if (string=  "Nat" pV16) (return t)) 
                                           (if (string=  "Integer" pV15) 
                                               (if (string=  "Integer" pV16) 
                                                   (return t)) 
                                               (if (string=  "Boolean" pV15) 
                                                   (if (string=  "Boolean" pV16) 
                                                       (return t)))))))))) 
                         (return nil)))) 
                      (labels 
                        ((builtinSnarkSort (s) 
                          (block 
                           nil 
                           (if (eq (car s) :|Base|) 
                               (let ((pV25 (svref (cdr s) 0))) 
                                 (if (eq (car pV25) :|Qualified|) 
                                     (let ((pV28 (cdr pV25))) 
                                       (let ((pV30 (cdr pV28))
                                             (pV29 (car pV28))) 
                                         (if (string=  "Nat" pV29) 
                                             (if (string=  "Nat" pV30) 
                                                 (return 
                                                  (LISP-SPEC::|!symbol| 
                                                   "SNARK" 
                                                   "NATURAL"))) 
                                             (if (string=  "Integer" pV29) 
                                                 (if (string=  "Integer" pV30) 
                                                     (return 
                                                      (LISP-SPEC::|!symbol| 
                                                       "SNARK" 
                                                       "INTEGER"))) 
                                                 (if (string=  "Boolean" pV29) 
                                                     (if (string=  
                                                          "Boolean" 
                                                          pV30) 
                                                         (return 
                                                          (if pV62 
                                                              (LISP-SPEC::|!symbol| 
                                                               "SNARK" 
                                                               "BOOLEAN") 
                                                              (LISP-SPEC::|!symbol| 
                                                               "SNARK" 
                                                               "TRUE")))))))))))) 
                           (error 
                            "Nonexhaustive match failure in findPBuiltInSort")))) 
                        (let ((builtinScheme 
                               (LIST-SPEC::|!find|-1-1 
                                #'(lambda (x) (builtinSort? (cdr x))) 
                                pV59))) 
                          (block 
                           nil 
                           (if (eq (car builtinScheme) :|Some|) 
                               (return 
                                (builtinSnarkSort (cdr (cdr builtinScheme))))) 
                           (return 
                            (block 
                             nil 
                             (if (consp pV59) 
                                 (let ((pV49 (cdr (car pV59)))) 
                                   (if (null (cdr pV59)) 
                                       (return 
                                        (block 
                                         nil 
                                         (if (eq (car pV49) :|Subsort|) 
                                             (return 
                                              (LISP-SPEC::|!symbol| "SNARK" pV65))) 
                                         (return 
                                          (SPECCALC::snarkPBaseSort 
                                           pV60 
                                           pV49 
                                           pV62))))))) 
                             (return (LISP-SPEC::|!symbol| "SNARK" pV65))))))))))) 
             (return (LISP-SPEC::|!symbol| "SNARK" pV65))))))) 
   (error "Nonexhaustive match failure in findPBuiltInSort")))

(defparameter SPECCALC::specwareDebug? nil)

(defun SPECCALC::snarkPBaseSort (spc s rng?) 
  (block 
   nil 
   (if (eq (car s) :|Base|) 
       (let ((pV21 (svref (cdr s) 0))) 
         (if (eq (car pV21) :|Qualified|) 
             (let ((pV24 (cdr pV21))) 
               (let ((pV26 (cdr pV24))
                     (pV25 (car pV24))) 
                 (progn (if (string=  "Nat" pV25) 
                            (if (string=  "Nat" pV26) 
                                (return (LISP-SPEC::|!symbol| "SNARK" "NATURAL"))) 
                            (if (string=  "Integer" pV25) 
                                (if (string=  "Integer" pV26) 
                                    (return 
                                     (LISP-SPEC::|!symbol| "SNARK" "INTEGER"))) 
                                (if (string=  "Boolean" pV25) 
                                    (if (string=  "Boolean" pV26) 
                                        (return 
                                         (if rng? 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "BOOLEAN") 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "TRUE"))))))) 
                        (return 
                         (let ((res 
                                (SPECCALC::findPBuiltInSort 
                                 spc 
                                 (cons :|Qualified| (cons pV25 pV26)) 
                                 rng?))) res)) 
                        (return 
                         (if rng? 
                             (LISP-SPEC::|!symbol| "SNARK" pV26) 
                             (LISP-SPEC::|!symbol| "SNARK" pV26)))))))) 
       (if (eq (car s) :|Product|) 
           (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
           (if (eq (car s) :|Arrow|) 
               (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
               (if (eq (car s) :|TyVar|) 
                   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")))))) 
   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE"))))

(defun SPECCALC::snarkBndVar (sp var globalVars) 
  (block 
   nil 
   (let ((pV4 (cdr var))
         (pV3 (car var))) 
     (return 
      (if (LIST-SPEC::|!exists|-1-1 
           #'(lambda (x) (string=  pV3 (car x))) 
           globalVars) 
          (LISP-SPEC::|!list| 
           (cons 
            (SPECCALC::snarkVar-1 var) 
            (cons 
             (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
             (cons 
              (SPECCALC::snarkPBaseSort sp pV4 nil) 
              (cons 
               (LISP-SPEC::|!symbol| "KEYWORD" "GLOBAL") 
               (cons (LISP-SPEC::|!symbol| "SNARK" "T") nil)))))) 
          (LISP-SPEC::|!list| 
           (cons 
            (SPECCALC::snarkVar-1 var) 
            (cons 
             (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
             (cons (SPECCALC::snarkPBaseSort sp pV4 nil) nil))))))) 
   (error "Nonexhaustive match failure in snarkBndVar")))

(defun SPECCALC::snarkBndVars (sp vars globalVars) 
  (let ((snarkVarList 
         (LIST-SPEC::|!map|-1-1 
          #'(lambda (var) (SPECCALC::snarkBndVar sp var globalVars)) 
          vars))) (let ((res (LISP-SPEC::|!list| snarkVarList))) res)))

(defun SPECCALC::mkSnarkFmla (context sp dpn vars globalVars fmla) 
  (block 
   nil 
   (if (eq (car fmla) :|Bind|) 
       (let ((pV12 (cdr fmla))) 
         (let ((pV29 (svref pV12 1))) 
           (return 
            (let ((snarkBndList (SPECCALC::snarkBndVars sp pV29 globalVars))) 
              (let ((newVars 
                     (LIST-SPEC::|!map|-1-1 
                      #'(lambda (x) (SPECTOLISP::specId (car x))) 
                      pV29))) 
                (let ((snarkFmla 
                       (SPECCALC::mkSnarkFmla 
                        context 
                        sp 
                        dpn 
                        (STRINGSET::addList vars newVars) 
                        globalVars 
                        (svref pV12 2)))) 
                  (LISP-SPEC::|!list| 
                   (cons 
                    (LISP-SPEC::|!symbol| 
                     "SNARK" 
                     (SPECCALC::bndrString (svref pV12 0))) 
                    (cons snarkBndList (cons snarkFmla nil)))))))))) 
       (if (eq (car fmla) :|Apply|) 
           (let ((pV11 (cdr fmla))) 
             (let ((pV21 (svref pV11 0))) 
               (if (eq (car pV21) :|Fun|) 
                   (let ((pV24 (cdr pV21))) 
                     (return 
                      (SPECCALC::mkSnarkFmlaApp 
                       context 
                       sp 
                       dpn 
                       vars 
                       (svref pV24 0) 
                       (svref pV24 1) 
                       (svref pV11 1))))))) 
           (if (eq (car fmla) :|IfThenElse|) 
               (let ((pV10 (cdr fmla))) 
                 (return 
                  (LISP-SPEC::|!list| 
                   (cons 
                    (LISP-SPEC::|!symbol| "SNARK" "IF") 
                    (cons 
                     (SPECCALC::mkSnarkFmla 
                      context 
                      sp 
                      dpn 
                      vars 
                      globalVars 
                      (svref pV10 0)) 
                     (cons 
                      (SPECCALC::mkSnarkFmla 
                       context 
                       sp 
                       dpn 
                       vars 
                       globalVars 
                       (svref pV10 1)) 
                      (cons 
                       (SPECCALC::mkSnarkFmla 
                        context 
                        sp 
                        dpn 
                        vars 
                        globalVars 
                        (svref pV10 2)) 
                       nil))))))) 
               (if (eq (car fmla) :|Fun|) 
                   (let ((pV13 (svref (cdr fmla) 0))) 
                     (if (eq (car pV13) :|Bool|) 
                         (let ((pV16 (cdr pV13))) 
                           (if (eq t pV16) 
                               (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
                               (if (eq nil pV16) 
                                   (return 
                                    (LISP-SPEC::|!symbol| "SNARK" "FALSE"))))))))))) 
   (return (SPECCALC::mkSnarkTerm context sp dpn vars fmla))))

(defun SPECCALC::snarkConjecture (pV1 pV2 pV3) 
  (block 
   nil 
   (return 
    (let ((snarkFmla 
           (SPECCALC::mkSnarkFmla 
            pV1 
            pV2 
            "SNARK" 
            STRINGSET::empty 
            nil 
            (svref pV3 3)))) 
      (LISP-SPEC::|!list| 
       (cons 
        SPECCALC::snark_prove 
        (cons 
         (LISP-SPEC::|!quote| snarkFmla) 
         (cons 
          (LISP-SPEC::|!symbol| "KEYWORD" "NAME") 
          (cons (LISP-SPEC::|!symbol| "KEYWORD" (svref pV3 1)) nil))))))) 
   (error "Nonexhaustive match failure in snarkConjecture")))

(defun SPECCALC::snarkFunctionCurryDecl () (LISP-SPEC::|!nil|))

(defun SPECCALC::findBuiltInSort (pV60 pV61 pV62) 
  (block 
   nil 
   (if (eq (car pV61) :|Qualified|) 
       (let ((pV65 (cdr (cdr pV61)))) 
         (return 
          (let ((|!optSrt| (STANDARDSPEC::findTheSort pV60 pV61))) 
            (block 
             nil 
             (if (eq (car |!optSrt|) :|Some|) 
                 (let ((pV59 (svref (cdr |!optSrt|) 2))) 
                   (return 
                    (labels 
                      ((builtinSort? (s) 
                        (block 
                         nil 
                         (if (eq (car s) :|Base|) 
                             (let ((pV11 (svref (cdr s) 0))) 
                               (if (eq (car pV11) :|Qualified|) 
                                   (let ((pV14 (cdr pV11))) 
                                     (let ((pV16 (cdr pV14))
                                           (pV15 (car pV14))) 
                                       (if (string=  "Nat" pV15) 
                                           (if (string=  "Nat" pV16) (return t)) 
                                           (if (string=  "Integer" pV15) 
                                               (if (string=  "Integer" pV16) 
                                                   (return t)) 
                                               (if (string=  "Boolean" pV15) 
                                                   (if (string=  "Boolean" pV16) 
                                                       (return t)))))))))) 
                         (return nil)))) 
                      (labels 
                        ((builtinSnarkSort (s) 
                          (block 
                           nil 
                           (if (eq (car s) :|Base|) 
                               (let ((pV25 (svref (cdr s) 0))) 
                                 (if (eq (car pV25) :|Qualified|) 
                                     (let ((pV28 (cdr pV25))) 
                                       (let ((pV30 (cdr pV28))
                                             (pV29 (car pV28))) 
                                         (if (string=  "Nat" pV29) 
                                             (if (string=  "Nat" pV30) 
                                                 (return 
                                                  (LISP-SPEC::|!symbol| 
                                                   "SNARK" 
                                                   "NATURAL"))) 
                                             (if (string=  "Integer" pV29) 
                                                 (if (string=  "Integer" pV30) 
                                                     (return 
                                                      (LISP-SPEC::|!symbol| 
                                                       "SNARK" 
                                                       "INTEGER"))) 
                                                 (if (string=  "Boolean" pV29) 
                                                     (if (string=  
                                                          "Boolean" 
                                                          pV30) 
                                                         (return 
                                                          (if pV62 
                                                              (LISP-SPEC::|!symbol| 
                                                               "SNARK" 
                                                               "BOOLEAN") 
                                                              (LISP-SPEC::|!symbol| 
                                                               "SNARK" 
                                                               "TRUE")))))))))))) 
                           (error 
                            "Nonexhaustive match failure in findBuiltInSort")))) 
                        (let ((builtinScheme 
                               (LIST-SPEC::|!find|-1-1 
                                #'(lambda (x) (builtinSort? (cdr x))) 
                                pV59))) 
                          (block 
                           nil 
                           (if (eq (car builtinScheme) :|Some|) 
                               (return 
                                (builtinSnarkSort (cdr (cdr builtinScheme))))) 
                           (return 
                            (block 
                             nil 
                             (if (consp pV59) 
                                 (let ((pV49 (cdr (car pV59)))) 
                                   (if (null (cdr pV59)) 
                                       (return 
                                        (block 
                                         nil 
                                         (if (eq (car pV49) :|Subsort|) 
                                             (return 
                                              (LISP-SPEC::|!symbol| "SNARK" pV65))) 
                                         (return 
                                          (SPECCALC::snarkBaseSort 
                                           pV60 
                                           pV49 
                                           pV62))))))) 
                             (return (LISP-SPEC::|!symbol| "SNARK" pV65))))))))))) 
             (return (LISP-SPEC::|!symbol| "SNARK" pV65))))))) 
   (error "Nonexhaustive match failure in findBuiltInSort")))

(defun SPECCALC::snarkBaseSort (spc s rng?) 
  (block 
   nil 
   (if (eq (car s) :|Base|) 
       (let ((pV24 (svref (cdr s) 0))) 
         (if (eq (car pV24) :|Qualified|) 
             (let ((pV27 (cdr pV24))) 
               (let ((pV29 (cdr pV27))
                     (pV28 (car pV27))) 
                 (progn (if (string=  "Nat" pV28) 
                            (if (string=  "Nat" pV29) 
                                (return (LISP-SPEC::|!symbol| "SNARK" "NATURAL"))) 
                            (if (string=  "Integer" pV28) 
                                (if (string=  "Integer" pV29) 
                                    (return 
                                     (LISP-SPEC::|!symbol| "SNARK" "INTEGER"))) 
                                (if (string=  "Boolean" pV28) 
                                    (if (string=  "Boolean" pV29) 
                                        (return 
                                         (if rng? 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "BOOLEAN") 
                                             (LISP-SPEC::|!symbol| 
                                              "SNARK" 
                                              "TRUE"))))))) 
                        (return 
                         (let ((res 
                                (SPECCALC::findBuiltInSort 
                                 spc 
                                 (cons :|Qualified| (cons pV28 pV29)) 
                                 rng?))) 
                           (progn (if SPECCALC::specwareDebug? 
                                      (STRING-SPEC::toScreen 
                                       (STRING-SPEC::^ 
                                        (STRING-SPEC::^ 
                                         "findBuiltInSort: " 
                                         (ANNSPECPRINTER::printSort s)) 
                                        " returns ")) 
                                      nil) 
                                  (progn (if SPECCALC::specwareDebug? 
                                             (LISP-SPEC::|!PPRINT| res) 
                                             (LISP-SPEC::|!list| nil)) 
                                         (progn (if SPECCALC::specwareDebug? 
                                                    (STRING-SPEC::writeLine "") 
                                                    nil) 
                                                res))))) 
                        (return 
                         (if rng? 
                             (LISP-SPEC::|!symbol| "SNARK" pV29) 
                             (LISP-SPEC::|!symbol| "SNARK" pV29)))))))) 
       (if (eq (car s) :|Product|) 
           (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
           (if (eq (car s) :|Arrow|) 
               (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
               (if (eq (car s) :|TyVar|) 
                   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")))))) 
   (return (LISP-SPEC::|!symbol| "SNARK" "TRUE"))))

(defun SPECCALC::snarkPredicateDecl (spc name dom arity) 
  (let ((pV2 (SPECENVIRONMENT::productOpt spc dom))) 
    (block 
     nil 
     (if (eq (car pV2) :|Some|) 
         (return 
          (let ((domSortList 
                 (LIST-SPEC::|!map|-1-1 
                  #'(lambda (x) (SPECCALC::snarkBaseSort spc (cdr x) nil)) 
                  (cdr pV2)))) 
            (LISP-SPEC::|!list| 
             (cons 
              SPECCALC::declare_predicate 
              (cons 
               (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) 
               (cons 
                (LISP-SPEC::|!nat| arity) 
                (cons 
                 (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                 (cons 
                  (LISP-SPEC::|!quote| 
                   (LISP-SPEC::|!cons| 
                    (LISP-SPEC::|!symbol| "SNARK" "BOOLEAN") 
                    (LISP-SPEC::|!list| domSortList))) 
                  nil))))))))) 
     (return 
      (let ((domSortList (cons (SPECCALC::snarkBaseSort spc dom nil) nil))) 
        (LISP-SPEC::|!list| 
         (cons 
          SPECCALC::declare_predicate 
          (cons 
           (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) 
           (cons 
            (LISP-SPEC::|!nat| arity) 
            (cons 
             (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
             (cons 
              (LISP-SPEC::|!quote| 
               (LISP-SPEC::|!cons| 
                (LISP-SPEC::|!symbol| "SNARK" "BOOLEAN") 
                (LISP-SPEC::|!list| domSortList))) 
              nil)))))))))))

(defun SPECCALC::snarkFunctionNoArityDecl (spc name srt) 
  (block 
   nil 
   (if (eq (car srt) :|Base|) 
       (let ((pV24 (svref (cdr srt) 0))) 
         (if (eq (car pV24) :|Qualified|) 
             (progn (if (string=  "Boolean" (cdr (cdr pV24))) 
                        (return (SPECCALC::snarkPropositionSymbolDecl name))) 
                    (return 
                     (LISP-SPEC::|!list| 
                      (cons 
                       SPECCALC::declare_constant 
                       (cons 
                        (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) 
                        (cons 
                         (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                         (cons 
                          (LISP-SPEC::|!quote| 
                           (SPECCALC::snarkBaseSort spc srt t)) 
                          nil))))))))) 
       (if (eq (car srt) :|Arrow|) 
           (let ((pV19 (cdr srt))) 
             (let ((pV22 (svref pV19 1))
                   (pV21 (svref pV19 0))) 
               (return 
                (block 
                 nil 
                 (if (eq (car pV22) :|Base|) 
                     (let ((pV12 (svref (cdr pV22) 0))) 
                       (if (eq (car pV12) :|Qualified|) 
                           (if (string=  "Boolean" (cdr (cdr pV12))) 
                               (return 
                                (SPECCALC::snarkPredicateDecl spc name pV21 1)))))) 
                 (return 
                  (let ((snarkDomSrt (SPECCALC::snarkBaseSort spc pV21 nil))) 
                    (LISP-SPEC::|!list| 
                     (cons 
                      SPECCALC::declare_function 
                      (cons 
                       (LISP-SPEC::|!quote| (LISP-SPEC::|!symbol| "SNARK" name)) 
                       (cons 
                        (LISP-SPEC::|!nat| 1) 
                        (cons 
                         (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                         (cons 
                          (LISP-SPEC::|!quote| 
                           (LISP-SPEC::|!cons| 
                            (SPECCALC::snarkBaseSort spc pV22 t) 
                            (LISP-SPEC::|!list| (cons snarkDomSrt nil)))) 
                          nil)))))))))))))) 
   (error "Nonexhaustive match failure in snarkFunctionNoArityDecl")))

(defun SPECCALC::snarkFunctionNoCurryDecl (spc name srt arity) 
  (let ((pV16 (SPECENVIRONMENT::arrowOpt spc srt))) 
    (block 
     nil 
     (if (eq (car pV16) :|Some|) 
         (let ((pV17 (cdr pV16))) 
           (let ((pV19 (cdr pV17))
                 (pV18 (car pV17))) 
             (return 
              (block 
               nil 
               (if (eq (car pV19) :|Base|) 
                   (let ((pV10 (svref (cdr pV19) 0))) 
                     (if (eq (car pV10) :|Qualified|) 
                         (if (string=  "Boolean" (cdr (cdr pV10))) 
                             (return 
                              (SPECCALC::snarkPredicateDecl spc name pV18 arity)))))) 
               (return 
                (let ((pV6 (SPECENVIRONMENT::productOpt spc pV18))) 
                  (block 
                   nil 
                   (if (eq (car pV6) :|Some|) 
                       (return 
                        (let ((domSortList 
                               (LIST-SPEC::|!map|-1-1 
                                #'(lambda (x) 
                                   (SPECCALC::snarkBaseSort spc (cdr x) nil)) 
                                (cdr pV6)))) 
                          (LISP-SPEC::|!list| 
                           (cons 
                            SPECCALC::declare_function 
                            (cons 
                             (LISP-SPEC::|!quote| 
                              (LISP-SPEC::|!symbol| "SNARK" name)) 
                             (cons 
                              (LISP-SPEC::|!nat| arity) 
                              (cons 
                               (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                               (cons 
                                (LISP-SPEC::|!quote| 
                                 (LISP-SPEC::|!cons| 
                                  (SPECCALC::snarkBaseSort spc pV19 t) 
                                  (LISP-SPEC::|!list| domSortList))) 
                                nil))))))))) 
                   (return 
                    (let ((snarkDomSrt (SPECCALC::snarkBaseSort spc pV18 nil))) 
                      (LISP-SPEC::|!list| 
                       (cons 
                        SPECCALC::declare_function 
                        (cons 
                         (LISP-SPEC::|!quote| 
                          (LISP-SPEC::|!symbol| "SNARK" name)) 
                         (cons 
                          (LISP-SPEC::|!nat| arity) 
                          (cons 
                           (LISP-SPEC::|!symbol| "KEYWORD" "SORT") 
                           (cons 
                            (LISP-SPEC::|!quote| 
                             (LISP-SPEC::|!cons| 
                              (SPECCALC::snarkBaseSort spc pV19 t) 
                              (LISP-SPEC::|!list| (cons snarkDomSrt nil)))) 
                            nil)))))))))))))))) 
     (error "Nonexhaustive match failure in snarkFunctionNoCurryDecl"))))

(defun SPECCALC::snarkFunctionDecl (spc name srt) 
  (let ((pV5 (ARITYNORMALIZE::sortArity spc srt))
        (pV4 (SPECTOLISP::curryShapeNum spc srt))) 
    (block 
     nil 
     (if ( =  1 pV4) 
         (if (eq (car pV5) :|None|) 
             (return (SPECCALC::snarkFunctionNoArityDecl spc name srt)) 
             (if (eq (car pV5) :|Some|) 
                 (return 
                  (SPECCALC::snarkFunctionNoCurryDecl 
                   spc 
                   name 
                   srt 
                   (cdr (cdr pV5))))))) 
     (if (eq (car pV5) :|None|) 
         (return (SPECCALC::snarkFunctionCurryNoArityDecl spc name srt)) 
         (if (eq (car pV5) :|Some|) (return (SPECCALC::snarkFunctionCurryDecl)))) 
     (return (SPECCALC::snarkFunctionNoArityDecl spc name srt)))))

(defun SPECCALC::snarkProperty (pV1 pV2 pV3) 
  (block 
   nil 
   (return 
    (let ((snarkFmla 
           (SPECCALC::mkSnarkFmla 
            pV1 
            pV2 
            "SNARK" 
            STRINGSET::empty 
            nil 
            (svref pV3 3)))) 
      (LISP-SPEC::|!list| 
       (cons 
        SPECCALC::snark_assert 
        (cons 
         (LISP-SPEC::|!quote| snarkFmla) 
         (cons 
          (LISP-SPEC::|!symbol| "KEYWORD" "NAME") 
          (cons (LISP-SPEC::|!symbol| "KEYWORD" (svref pV3 1)) nil))))))) 
   (error "Nonexhaustive match failure in snarkProperty")))

(defun SPECCALC::sortInfoToSnarkSubsort (spc id info) 
  (block 
   nil 
   (let ((pV20 (svref info 2))) 
     (return 
      (block 
       nil 
       (if (null pV20) 
           (return '(:|None|)) 
           (if (consp pV20) 
               (let ((pV16 (cdr (car pV20)))) 
                 (if (null (cdr pV20)) 
                     (return 
                      (block 
                       nil 
                       (if (eq (car pV16) :|Subsort|) 
                           (return 
                            (cons 
                             :|Some| 
                             (LISP-SPEC::|!list| 
                              (cons 
                               SPECCALC::declare_subsorts 
                               (cons 
                                (LISP-SPEC::|!quote| 
                                 (SPECCALC::snarkBaseSort 
                                  spc 
                                  (svref (cdr pV16) 0) 
                                  nil)) 
                                (cons 
                                 (LISP-SPEC::|!quote| 
                                  (LISP-SPEC::|!symbol| "SNARK" id)) 
                                 nil))))))) 
                       (return '(:|None|)))))))) 
       (error "Nonexhaustive match failure in sortInfoToSnarkSubsort")))) 
   (error "Nonexhaustive match failure in sortInfoToSnarkSubsort")))

(defun SPECCALC::snarkSorts-1 (spc) 
  (let ((sorts (sortsAsList-1 spc))) 
    (let ((snarkSorts 
           (LIST-SPEC::|!map|-1-1 
            #'(lambda (x) 
               (LISP-SPEC::|!list| 
                (cons 
                 SPECCALC::declare_sort 
                 (cons 
                  (LISP-SPEC::|!quote| 
                   (LISP-SPEC::|!symbol| "SNARK" (svref x 1))) 
                  nil)))) 
            sorts))) 
      (let ((snarkSubSorts 
             (LIST-SPEC::mapPartial-1-1 
              #'(lambda (x) 
                 (SPECCALC::sortInfoToSnarkSubsort spc (svref x 1) (svref x 2))) 
              sorts))) 
        (LIST-SPEC::|!++| 
         (LIST-SPEC::|!++| (SPECCALC::snarkBuiltInSorts nil) snarkSorts) 
         snarkSubSorts)))))

(defun SPECCALC::findBuiltInSort-1 (x) 
  (SPECCALC::findBuiltInSort (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::findPBuiltInSort-1 (x) 
  (SPECCALC::findPBuiltInSort (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::mkSnarkFmla-1 (x) 
  (SPECCALC::mkSnarkFmla 
   (svref x 0) 
   (svref x 1) 
   (svref x 2) 
   (svref x 3) 
   (svref x 4) 
   (svref x 5)))

(defun SPECCALC::mkSnarkTermApp-1 (x) 
  (SPECCALC::mkSnarkTermApp 
   (svref x 0) 
   (svref x 1) 
   (svref x 2) 
   (svref x 3) 
   (svref x 4) 
   (svref x 5)))

(defun SPECCALC::snarkAnswer (pV1 pV2 pV3 pV4) 
  (block 
   nil 
   (return 
    (let ((snarkFmla 
           (SPECCALC::mkSnarkFmla 
            pV1 
            pV2 
            "SNARK" 
            STRINGSET::empty 
            pV4 
            (svref pV3 3)))) 
      (let ((snarkAnsVars 
             (LIST-SPEC::|!map|-1-1 
              #'(lambda (v) (SPECCALC::snarkVar-1 v)) 
              pV4))) 
        (let ((snarkAnsTerm 
               (LISP-SPEC::|!list| 
                (LIST-SPEC::|!++| 
                 (cons (LISP-SPEC::|!symbol| "SNARK" "ANS") nil) 
                 snarkAnsVars)))) 
          (LISP-SPEC::|!list| 
           (cons 
            SPECCALC::snark_prove 
            (cons 
             (LISP-SPEC::|!quote| snarkFmla) 
             (cons 
              (LISP-SPEC::|!symbol| "KEYWORD" "ANSWER") 
              (cons 
               (LISP-SPEC::|!quote| snarkAnsTerm) 
               (cons 
                (LISP-SPEC::|!symbol| "KEYWORD" "NAME") 
                (cons (LISP-SPEC::|!symbol| "KEYWORD" (svref pV3 1)) nil))))))))))) 
   (error "Nonexhaustive match failure in snarkAnswer")))

(defun SPECCALC::snarkAnswer-1 (x) 
  (SPECCALC::snarkAnswer (svref x 0) (svref x 1) (svref x 2) (svref x 3)))

(defun SPECCALC::snarkBaseSort-1 (x) 
  (SPECCALC::snarkBaseSort (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::snarkBndVar-1 (x) 
  (SPECCALC::snarkBndVar (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::snarkBndVars-1 (x) 
  (SPECCALC::snarkBndVars (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::snarkFunctionCurryDecl-1 (ignore) 
  (declare (ignore ignore)) 
  (SPECCALC::snarkFunctionCurryDecl))

(defun SPECCALC::snarkPBaseSort-1 (x) 
  (SPECCALC::snarkPBaseSort (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::snarkPPBaseSort (sp s rng?) 
  (let ((res 
         (block 
          nil 
          (if (eq (car s) :|Base|) 
              (let ((pV16 (svref (cdr s) 0))) 
                (if (eq (car pV16) :|Qualified|) 
                    (let ((pV19 (cdr pV16))) 
                      (let ((pV21 (cdr pV19))
                            (pV20 (car pV19))) 
                        (progn (if (string=  "Nat" pV20) 
                                   (if (string=  "Nat" pV21) 
                                       (return 
                                        (LISP-SPEC::|!symbol| "SNARK" "NATURAL"))) 
                                   (if (string=  "Integer" pV20) 
                                       (if (string=  "Integer" pV21) 
                                           (return 
                                            (LISP-SPEC::|!symbol| 
                                             "SNARK" 
                                             "INTEGER"))))) 
                               (return 
                                (if rng? 
                                    (LISP-SPEC::|!symbol| "SNARK" pV21) 
                                    (LISP-SPEC::|!symbol| "SNARK" pV21)))))))) 
              (if (eq (car s) :|Product|) 
                  (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
                  (if (eq (car s) :|Arrow|) 
                      (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")) 
                      (if (eq (car s) :|TyVar|) 
                          (return (LISP-SPEC::|!symbol| "SNARK" "TRUE")))))) 
          (error "Nonexhaustive match failure in snarkPPBaseSort")))) res))

(defun SPECCALC::snarkPPBaseSort-1 (x) 
  (SPECCALC::snarkPPBaseSort (svref x 0) (svref x 1) (svref x 2)))

(defun SPECCALC::snarkPredicateDecl-1 (x) 
  (SPECCALC::snarkPredicateDecl (svref x 0) (svref x 1) (svref x 2) (svref x 3)))

(defun SPECCALC::snarkVar (x0 x1) (SPECCALC::snarkVar-1 (cons x0 x1)))

(defun SPECCALC::sortInfoToSnarkSubsort-1 (x) 
  (SPECCALC::sortInfoToSnarkSubsort (svref x 0) (svref x 1) (svref x 2)))

