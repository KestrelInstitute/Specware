;;; Parser for Specware to C Translation Pragmas

(in-package :Parser4)

;; This is a common load file for all the build files in this direcrtory. 
;; This loads and compiles all the files pertaining to the specializer.

(defparameter *lm-parser* nil)

(defmacro define-lm-parser-rule (name &optional pattern semantics
                                 &key documentation)
  `(add-parser-main-rule *current-parser*     ; load-parser binds *current-parser*
                         ',name 
                         ()                   ; no parents
                         ',pattern 
                         ',semantics
                         +default-precedence+
                         ',documentation))

(cl-user::compile-and-load-local-file "lm-tokenizer")

(defparameter *lm-tokenizer*  #'extract-lm-tokens-from-file)

(cl-user::compile-and-load-local-file "lm-parser-interface")

(setq *lm-parser* 
      (load-parser (cl-user::local-file "lm-rules") 
                   :name 'LM-PARSER
                   :case-sensitive? t))
  
