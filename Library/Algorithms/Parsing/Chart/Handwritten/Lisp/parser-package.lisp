;;; -*- Mode: LISP; Package: User; Base: 10; Syntax: Common-Lisp -*-

(in-package "CL-USER")

(defpackage "PARSER4")

(in-package "PARSER4")

(export '(*VERBOSE?*
	  WHEN-DEBUGGING
	  DEFINE-SW-PARSER-RULE	
	  PARSE-SESSION-GAPS
	  PARSE-SESSION-ERROR-REPORTED?
	  PARSE-SESSION-RESULTS 
	  PARSE-FILE))
