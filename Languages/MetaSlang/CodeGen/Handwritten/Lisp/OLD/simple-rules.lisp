;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :LM       (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;; ========================================================================
;;; Simple names are just unstructured strings -- no packages, qualifiers, 
;;; etc.
;;;
;;; They could appear in pretty much any language.
;;; ========================================================================

(define-lm-parser-rule :Simple_Id  
    (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))

(define-lm-parser-rule :SImple_Name
    (:tuple (1 :Symbol))
  (common-lisp::symbol-name (quote 1)))

