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
;;; Target is Lisp, Java, C, Haskell, Isabelle,etc., but referenced names are 
;;; just simple strings (no packages, qualifiers, etc.).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-lm-parser-rule :Target_Id    :Simple_Id)
(define-lm-parser-rule :Target_Name  :Simple_Name)
