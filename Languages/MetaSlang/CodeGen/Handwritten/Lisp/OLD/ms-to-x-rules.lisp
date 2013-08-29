;;; -*- Mode: LISP; Package: Specware; Base: 10; Syntax: Common-Lisp -*-

(defpackage :SpecCalc (:use :COMMON-LISP-USER))
(defpackage :LM       (:use :COMMON-LISP-USER))
(in-package :Parser4)


;;; Source is MetaSlang

(define-lm-parser-rule :Source_Id    :MS_Id)
(define-lm-parser-rule :Source_Name  :MS_Name)

(define-lm-parser-rule :Target_Id    :Simple_Id)
(define-lm-parser-rule :Target_Name  :Simple_Name)
