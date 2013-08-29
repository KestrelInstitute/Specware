;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :LM       (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; ========================================================================
;;; MetaSlang names are qualified ids.  Ids are simple strings.
;;; ========================================================================

(define-lm-parser-rule :MS_Id ;; same as :NAME in specware parser
    (:anyof
     ((:tuple "answerVar")    "answerVar")
     ((:tuple "colimit")      "colimit")
     ((:tuple "diagram")      "diagram")
     ((:tuple "expand")       "expand")
     ((:tuple "export")       "export")
     ((:tuple "extendMorph")  "extendMorph")
     ((:tuple "hide")         "hide")
     ((:tuple "is")           "is")
     ((:tuple "options")      "options")
     ((:tuple "print")        "print")
     ((:tuple "reduce")       "reduce")
     ((:tuple "translate")    "translate")
     ((:tuple "using")        "using")
     ((:tuple "with")         "with")
     ((:tuple "/")            "/")
     ((:tuple "*")            "*")
     ((:tuple "\\_times")     "\\_times")
     ((:tuple "UID")          "UID")
     ((:tuple "at")           "at")
     ((:tuple "repeat")       "repeat")
     ((:tuple "slice")        "slice")
     ((:tuple (1 :Symbol))    (common-lisp::symbol-name (quote 1)))
     ))

(define-lm-parser-rule :MS_Name 
    (:anyof :UnqualifiedName :QualifiedName))

(define-lm-parser-rule :UnqualifiedName
    (:tuple (1 :MS_Id))
  (MetaSlang::mkUnQualifiedId 1))

(define-lm-parser-rule :QualifiedName 
    (:tuple (1 :MS_Qualifier) "." (2 :MS_Id))
  (MetaSlang::mkQualifiedId-2 1 2))

(define-lm-parser-rule :MS_Qualifier 
    :MS_Id)


