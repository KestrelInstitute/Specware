
;;; Parser

(in-package "PARSER4")

;;;; #||
;;;; (defun current-directory2 ()
;;;;   (excl::current-directory))
;;;; 
;;;; (defun change-directory2 (directory)
;;;;   ;; (lisp::format t "Changing to: ~A~%" directory)
;;;;   (excl::chdir directory)
;;;;   (setq lisp::*default-pathname-defaults* (excl::current-directory)))
;;;; 
;;;; (defun make-system2 (new-directory)
;;;;   (let ((old-directory (current-directory2)))
;;;;     (change-directory2 new-directory)
;;;;     (unwind-protect (load "system.lisp")
;;;;       (change-directory2 old-directory))))
;;;; 
;;;; (format t "~&;;; Loading /specware/parser ~%")
;;;; (make-system2 "/specware/parser/")
;;;; (format t "~&;;; Loaded ~%")
;;;; #||

;; === temporary
;; This is a common load file for all the build files in this direcrtor. 
;; This loads and compiles all he files pertaing to the specializer.


;; All library paths are relative to the Specware4 root directory.
(setq baseDir (specware::getenv "SPECWARE4"))

;; ========

(cl-user::compile-and-load-local-file "tokenizer")

(defparameter *specware4-tokenizer*
  #'extract-specware4-tokens-from-file)

;; *specware4-parser* is referenced in semantics.lisp, so declare it first...
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
  ;; (comment " ")
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
  (format t "~&;     To test specware4 parser: (cl-user::test-specware4-parser <file defaulting to test.spec>)~%")
  )
