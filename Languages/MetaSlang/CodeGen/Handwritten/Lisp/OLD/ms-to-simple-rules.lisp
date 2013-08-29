;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :LM       (:use :COMMON-LISP-USER))
(in-package :Parser4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Source is MetaSlang
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-lm-parser-rule :Source_Id    :MS_Id)
(define-lm-parser-rule :Source_Name  :MS_Name)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Target is Simple.
;;; I.e., names are just simple strings (no packages, qualifiers, etc.).
;;; This could thus be a subset of Lisp, Java, C, Haskell, Isabelle, etc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-lm-parser-rule :Target_Id    :Simple_Id)
(define-lm-parser-rule :Target_Name  :Simple_Name)
