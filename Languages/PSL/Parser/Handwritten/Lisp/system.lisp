
;;; Parser

(in-package "PARSER4")

(user::compile-and-load-local-file "tokenizer")

(defparameter *specware4-tokenizer*
  #'extract-specware4-tokens-from-file)

;; *specware4-parser* is referenced in semantics.lisp, so declare it first...
(defparameter *specware4-parser* nil)

(user::compile-and-load-local-file "semantics")
(user::compile-and-load-local-file "parser-interface")

(setq *specware4-parser* (load-parser (user::local-file "rules") :name 'SPECWARE4-PARSER :case-sensitive? t))
