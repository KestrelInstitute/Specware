;;; Parser for Specware to C Translation Pragmas

(in-package :Parser4)

;; This is a common load file for all the build files in this direcrtory. 
;; This loads and compiles all the files pertaining to the specializer.

(cl-user::compile-and-load-local-file "sw-to-c-tokenizer")

(defparameter *sw-to-c-tokenizer*
  #'extract-sw-to-c-tokens-from-file)

;; *sw-to-c-parser* is referenced in parser-interface.lisp, so declare it first...
(defparameter *sw-to-c-parser* nil)

(cl-user::compile-and-load-local-file "sw-to-c-parser-interface")

(setq *sw-to-c-parser* 
      (load-parser (cl-user::local-file "sw-to-c-rules") 
                   :name 'SW-TO-C-PARSER
                   :case-sensitive? t))
  
