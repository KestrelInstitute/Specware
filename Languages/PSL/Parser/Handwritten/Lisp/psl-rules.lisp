(defpackage "OscarAbsSyn")

(define-sw-parser-rule :SC-TERM ()
  (:anyof
   (:tuple "(" (1 :SC-TERM) ")")
   (1 :SC-PRINT)
   (1 :SC-UNIT-ID)
   (1 :SPEC-DEFINITION)
   (1 :SC-LET)
   (1 :SC-WHERE)
   (1 :SC-TRANSLATE)
   (1 :SC-QUALIFY)
   (1 :SC-DIAG)
   (1 :SC-COLIMIT)
   ;; (1 :SC-DOM)
   ;; (1 :SC-COD)
   ;; (1 :SC-LIMIT)
   ;; (1 :SC-APEX)
   ;; (1 :SC-SHAPE)
   ;; (1 :SC-DIAG-MORPH)
   (1 :SC-SUBSTITUTE)
   (1 :SC-SPEC-MORPH)
   (1 :SC-HIDE)
   (1 :SC-EXPORT)
   (1 :SC-PSL-DEFINITION)
   (1 :SC-PSL-SPECIALIZE)
   (1 :SC-PSL-INLINE)
   (1 :SC-GENERATE))
  1)

;;; ======================================================================
;;; The following are the production rules for the Procedural Specification
;;; language. The only change above this line should be to a reference
;;; to PROCSPEC-DEF in the production for SC-TERM
;;;
;;; PROCSPEC needs a better name since it implies we are defining only
;;; a procedure. We may define a collection of procedure as well as
;;; other things. The keyword "psl" is a poor choice.

(define-sw-parser-rule :SC-PSL-DEFINITION ()
  (:tuple "psl" "{" (1 (:repeat* :PROCSPEC-ELEM nil)) "}")
  (OscarAbsSyn::mkDecls-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :SC-PSL-SPECIALIZE ()
  (:tuple "specialize" (1 :TIGHT-EXPRESSION) "in" (2 :SC-TERM))
  (OscarAbsSyn::mkSpecialize-3 1 2 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :SC-PSL-INLINE ()
  (:tuple "inline" (1 :NAME) "in" (2 :SC-TERM))
  (OscarAbsSyn::mkInline-3 1 2 (make-pos ':left-lcb ':right-lcb)))


;;; The following is almost the same a SPEC-ELEM. The difference is the
;;; introduction of PROCDEF.
(define-sw-parser-rule :PROCSPEC-ELEM ()
  (:anyof
    (1 :IMPORT-DECLARATION)
    (1 :SORT-DECLARATION)
    (1 :SORT-DEFINITION)
    (1 :OP-DECLARATION)
    (1 :PSL-OP-DEFINITION)
    (1 :VARDECL)
    (1 :CLAIM-DEFINITION)
    (1 :PROCDEF))
  1)

(define-sw-parser-rule :PROCDEF ()
  (:tuple "proc"
    (1 :NAME)
    "(" (2 (:repeat* :PSL-PROC-PARAM ",")) ")"
    ":" (3 :SORT)
    (:optional (:tuple "{" (4 :PSL-COMMAND-SEQ) "}")))
  (let* ((procName 1)
         (params   2)
         (returnSort  3)
         (optCommands 4)
         (commandSeq (if (eq :unspecified optCommands)
                         (OscarAbsSyn::mkSeq-2 nil (make-pos ':left-lcb ':right-lcb))
                         optCommands))
         (procInfo (OscarAbsSyn::mkProcInfo-3 params returnSort commandSeq)))
         (OscarAbsSyn::mkProc-3 procName procInfo (make-pos ':left-lcb ':right-lcb))))

(define-sw-parser-rule :PSL-PROC-PARAM ()
  (:tuple (1 :NAME) ":" (2 :SORT))
  (cons 1 2))

(define-sw-parser-rule :PSL-COMMAND ()
  (:anyof
    (1 :PSL-IF)
    (1 :PSL-DO)
    ;; (1 :PSL-CASE)
    (1 :PSL-LET)
    (1 :PSL-RETURN)
    (1 :PSL-SKIP)
    (1 :PSL-CONTINUE)
    (1 :PSL-BREAK)
    (1 :PSL-EXEC)
    ;; (1 :PSL-ASSIGN)
    (1 :PSL-RELATION))
  1)

(define-sw-parser-rule :PSL-RELATION ()
  (:tuple "<|" (1 :EXPRESSION) "|>")
  (OscarAbsSyn::mkRelation-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :VARDECL ()
  (:tuple "var" (1 :QUALIFIABLE-OP-NAMES) ":" (2 :SORT-SCHEME))
  (OscarAbsSyn::mkVar-3 1 2 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-OP-DEFINITION ()
  (:tuple "def"
          (:optional (1 :SORT-VARIABLE-BINDER))
          (2 :QUALIFIABLE-OP-NAMES)
          (:optional (3 :FORMAL-PARAMETERS))
          (:optional (:tuple ":" (4 :SORT)))
          :EQUALS
          (5 :EXPRESSION))
  (make-psl-op-definition 1 2 3 4 5 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-IF ()
  (:tuple "if" "{" (:optional "|") (1 (:repeat+ :PSL-ALTERNATIVE "|")) "}")
  (OscarAbsSyn::mkIf-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-DO ()
  (:tuple "do" "{" (:optional "|") (1 (:repeat+ :PSL-ALTERNATIVE "|")) "}")
  (OscarAbsSyn::mkDo-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-LET ()
  (:tuple "let"
    (1 (:repeat* :PROCSPEC-ELEM nil))
    "in" "{"
    (2 :PSL-COMMAND-SEQ) "}")
  (OscarAbsSyn::mkLet-3 1 2 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-SKIP ()
  (:tuple "skip")
  (OscarAbsSyn::mkSkip (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-BREAK ()
  (:tuple "break")
  (OscarAbsSyn::mkBreak (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-CONTINUE ()
  (:tuple "continue")
  (OscarAbsSyn::mkContinue (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-RETURN ()
  (:tuple "return" (1 (:optional :EXPRESSION)))
  (let* ((opt 1)
         (optTerm (if (equal :unspecified opt) Option::None (cons :|Some| opt))))
    (OscarAbsSyn::mkReturn-2 optTerm (make-pos ':left-lcb ':right-lcb))))

;; (define-sw-parser-rule :PSL-ASSIGN ()
;;   (:tuple (1 :EXPRESSION) ":=" (2 :EXPRESSION))
;;   (OscarAbsSyn::mkAssign-3 1 2 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-EXEC ()
  (:tuple (1 :EXPRESSION))
  (OscarAbsSyn::mkExec-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-COMMAND-SEQ ()
  (1 (:repeat+ :PSL-COMMAND ";"))
  (OscarAbsSyn::mkSeq-2 1 (make-pos ':left-lcb ':right-lcb)))

(define-sw-parser-rule :PSL-ALTERNATIVE ()
  (:tuple (1 :EXPRESSION) "->" (2 :PSL-COMMAND-SEQ))
  (OscarAbsSyn::mkAlternative-3 1 2 (make-pos ':left-lcb ':right-lcb)))

;; (define-sw-parser-rule :PSL-CASE ()
;;   (:tuple "case" (1 :EXPRESSION) "{" (2 (:repeat+ :PSL-CASE-BRANCH "|")) "}")
;;   (make-psl-case 1 2 ':left-lcb ':right-lcb))
;; 
;; (define-sw-parser-rule :PSL-CASE-BRANCH ()
;;   (:tuple (1 :PATTERN) "->" (2 :PSL-COMMAND-SEQ))
;;   (make-psl-case-branch 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CLAIM-KIND ()
  (:anyof ((:tuple "axiom")       :|Axiom|)
          ((:tuple "theorem")     :|Theorem|)
          ((:tuple "invariant")   :|Invariant|)
          ((:tuple "conjecture")  :|Conjecture|)))
