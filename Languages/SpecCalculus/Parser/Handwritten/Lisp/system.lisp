
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

(defun cur-directory ()
  (excl::current-directory))

(defun change-directory (directory)
  ;; (lisp::format t "Changing to: ~A~%" directory)
  (excl::chdir directory)
  (setq lisp::*default-pathname-defaults* (excl::current-directory)))

(defun make-system (new-directory)
  (let ((old-directory (cur-directory)))
    (change-directory new-directory)
    (unwind-protect (load "system.lisp")
      (change-directory old-directory))))

;; All library paths are relative to the Specware4 root directory.
(setq baseDir (sys:getenv "SPECWARE4"))

(defun compile-and-load-lisp-file (file)
   (excl::compile-file-if-needed (make-pathname :defaults file :type "lisp"))
   (load (make-pathname :defaults file :type nil)))
;; ========

(compile-and-load-lisp-file "tokenizer")

(defparameter *specware4-tokenizer*
  #'extract-specware4-tokens-from-file)

;; *specware4-parser* is referenced in semantics.lisp, so declare it first...
(defparameter *specware4-parser* nil)

(compile-and-load-lisp-file "semantics")
(compile-and-load-lisp-file "parser-interface")

(progn
  (comment-blank-lines 1)
  (comment "========================================================================")
  (comment "Load parser for specware 4")
  (comment " ")
  (comment "Before loading specware4 parser")
  (comment "PARSER::*CURRENT-PARSER*    = ~S" PARSER::*CURRENT-PARSER*)
  (comment "PARSER4::*CURRENT-PARSER*   = ~S" PARSER4::*CURRENT-PARSER*)
  (comment "PARSER4::*SPECWARE4-PARSER* = ~S" PARSER4::*SPECWARE4-PARSER*)

  (setq *specware4-parser*
    (load-parser
     "rules" 
     :name 'SPECWARE4-PARSER 
     :case-sensitive? t))

  (comment-blank-lines 1)
  (comment "After loading specware4 parser")
  (comment "PARSER::*CURRENT-PARSER*    = ~S" PARSER::*CURRENT-PARSER*)
  (comment "PARSER4::*CURRENT-PARSER*   = ~S" PARSER4::*CURRENT-PARSER*)
  (comment "PARSER4::*SPECWARE4-PARSER* = ~S" PARSER4::*SPECWARE4-PARSER*)
  (comment "========================================================================")
  (comment-blank-lines 1))

(defun user::test-specware4-parser (&optional (file "Languages/SpecCalculus/Parser/test.spec"))
  ;; (parse-file file *meta-slang-parser* *meta-slang-tokenizer*)
  (format t "~&~%;;; SPECWARE4 Parsing ~A~%" file)
  (let* ((res1
	  (car 
	   (parse-session-results 
	    (parse-file file
			*specware4-parser*
			*specware4-tokenizer*)))))
    (print (mapcar #'eval (third res1)))))

(progn
  (comment "To test specware4 parser: (user::test-specware4-parser <file defaulting to test.spec>)")
  )