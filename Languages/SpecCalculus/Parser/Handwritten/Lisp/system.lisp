
;;; Parser

(in-package "PARSER4")

;; This is a common load file for all the build files in this direcrtory. 
;; This loads and compiles all the files pertaining to the specializer.

(cl-user::compile-and-load-local-file "tokenizer")

(defparameter *specware4-tokenizer*
  #'extract-specware4-tokens-from-file)

;; *specware4-parser* is referenced in parser-interface.lisp, so declare it first...
(defparameter *specware4-parser* nil)

(cl-user::compile-and-load-local-file "semantics")
(cl-user::compile-and-load-local-file "parser-interface")

(setq *specware4-parser* (load-parser (cl-user::local-file "rules") :name 'SPECWARE4-PARSER :case-sensitive? t))
  
(progn
  ;;(comment "===================================================================================")
  ;; (comment " ")
  ;; (comment "Printing grammar as .ps file")
  ;; sjw: This dies on windows build, and why is this done at build time
  ;;  (print-grammar-ps-file)
  ;;(comment " ")
  ;;(comment "===================================================================================")
  )

(defun cl-user::test-specware4-parser (&optional (file "Languages/SpecCalculus/Parser/test.spec"))
  ;; (parse-file file *meta-slang-parser* *meta-slang-tokenizer*)
  (format t "~&~%;;; SPECWARE4 Parsing ~A~%" file)
  (let* ((*parser-source* (list :file file))
	 (res1
	  (car 
	   (parse-session-results 
	    (parse-file file
			*specware4-parser*
			*specware4-tokenizer*)))))
    (print (mapcar #'eval (third res1)))))

(progn
  (format t "~&;     To print specware4 grammar as pdf file: (parser4::print-grammar-ps-file)~&")
  (format t "~&;     To test specware4 parser: (cl-user::test-specware4-parser <file defaulting to test.spec>)~%")
  )
