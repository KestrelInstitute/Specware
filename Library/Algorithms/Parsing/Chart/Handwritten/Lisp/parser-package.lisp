;;; -*- Mode: LISP; Package: User; Base: 10; Syntax: Common-Lisp -*-

(in-package :cl-user)

(defpackage :Parser4 
  (:use :common-lisp)
  (:export :*VERBOSE?*
	   :WHEN-DEBUGGING
	   :DEFINE-SW-PARSER-RULE	
	   :PARSE-SESSION-GAPS
	   :PARSE-SESSION-ERROR-REPORTED?
	   :PARSE-SESSION-RESULTS 
	   :PARSE-FILE))

(in-package :Parser4) 

