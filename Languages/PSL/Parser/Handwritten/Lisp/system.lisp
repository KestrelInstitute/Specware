
;;; Parser

(in-package "PARSER4")

(cl-user::compile-and-load-local-file "tokenizer")

(defparameter *specware4-tokenizer*
  #'extract-specware4-tokens-from-file)

;; *specware4-parser* is referenced in semantics.lisp, so declare it first...
(defparameter *specware4-parser* nil)

(cl-user::compile-and-load-local-file "semantics")
(cl-user::compile-and-load-local-file "parser-interface")

(setq *specware4-parser* (load-parser (cl-user::local-file "rules") :name 'SPECWARE4-PARSER :case-sensitive? t))
