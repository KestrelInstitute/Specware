(define-sw-parser-rule :SC-TERM ()
  (:anyof
   (:tuple "(" (1 :SC-TERM) ")")
   (1 :SC-PRINT)
   (1 :SC-URI)
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
  (:tuple "psl" "{" (1 (:optional :PROCSPEC-ELEMS)) "}")
  (make-procspec 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PROCSPEC-ELEMS ()
  (1 (:repeat :PROCSPEC-ELEM nil))
  (list . 1))

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
    "(" (:optional (2 :PSL-PROC-PARAMS)) ")"
    ":" (3 :SORT)
    (:optional (:tuple "{" (4 :PSL-COMMAND-SEQ) "}")))
  (make-psl-proc-def 1 2 3 4 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-PROC-PARAMS ()
  (1 (:repeat :PSL-PROC-PARAM ","))
  (list . 1))

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
    ;;; (1 :PSL-CALL)
    ;;; (1 :PSL-ASSIGN-CALL)
    (1 :PSL-ASSIGN)
    (1 :PSL-RELATION))
  1)

(define-sw-parser-rule :PSL-RELATION ()
  (:tuple "<|" (1 :EXPRESSION) "|>")
  (make-psl-relation 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :VARDECL ()
  (:tuple "var" (1 :QUALIFIABLE-OP-NAMES) ":" (2 :SORT-SCHEME))
  (make-psl-var-decl 1 2 ':left-lcb ':right-lcb))

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
  (:tuple "if" "{" (1 (:repeat :PSL-ALTERNATIVE "|")) "}")
  (make-psl-if (list . 1) ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-DO ()
  (:tuple "do" "{" (1 (:repeat :PSL-ALTERNATIVE "|")) "}")
  (make-psl-do (list . 1) ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-CASE ()
  (:tuple "case" (1 :EXPRESSION) "{" (2 (:repeat :PSL-CASE-BRANCH "|")) "}")
  (make-psl-case 1 (list . 2) ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-LET ()
  (:tuple "let"
    (1 :PROCSPEC-ELEMS)
    "in" "{"
    (2 :PSL-COMMAND-SEQ) "}")
  (make-psl-let 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-SKIP ()
  (:tuple "skip")
  (make-psl-skip ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-BREAK ()
  (:tuple "break")
  (make-psl-break ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-CONTINUE ()
  (:tuple "continue")
  (make-psl-continue ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-RETURN ()
  (:tuple "return" (1 (:optional :EXPRESSION)))
  (make-psl-return 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-ASSIGN ()
  (:tuple (1 :EXPRESSION) ":=" (2 :EXPRESSION))
  (make-psl-assign 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-EXEC ()
  (:tuple (1 :EXPRESSION))
  (make-psl-exec 1 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-COMMAND-SEQ ()
  (1 (:repeat :PSL-COMMAND ";"))
  (list . 1))

(define-sw-parser-rule :PSL-ALTERNATIVE ()
  (:tuple (1 :EXPRESSION) "->" (2 :PSL-COMMAND-SEQ))
  (make-psl-alternative 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :PSL-CASE-BRANCH ()
  (:tuple (1 :PATTERN) "->" (2 :PSL-COMMAND-SEQ))
  (make-psl-case-branch 1 2 ':left-lcb ':right-lcb))

(define-sw-parser-rule :CLAIM-KIND ()
  (:anyof ((:tuple "axiom")       :|Axiom|)
          ((:tuple "theorem")     :|Theorem|)
          ((:tuple "invariant")   :|Invariant|)
          ((:tuple "conjecture")  :|Conjecture|)))
