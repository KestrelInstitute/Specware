;;; -*- Mode: LISP; Package: User; Base: 10; Syntax: Common-Lisp -*-

(in-package "CL-USER")

(defun local-file (filename) 
  (make-pathname :name filename :defaults *LOAD-PATHNAME*))

(defun load-local-file (filename) 
  (specware::load-lisp-file (local-file filename) :compiled? nil))

(defun compile-and-load-local-file (filename) 
  (specware::compile-and-load-lisp-file (local-file filename)))

(load-local-file "parser-package") 

;; Setting the count to 1 means you can push :DEBUG-PARSER twice onto
;;  *features* prior to loading this file and one occurrence will survive.
(setq *features* (remove :DEBUG-PARSER    *features* :count 1))
(setq *features* (remove :OPTIMIZE-PARSER *features* :count 1))

;; Or you can just edit the following to choose either or neither (both is ok, but would be peculiar)
;(pushnew :DEBUG-PARSER *features*)
;(pushnew :OPTIMIZE-PARSER *features*)

#+DEBUG-PARSER    (format t "~&;;; DEBUG-PARSER    feature is on.~%")
#-DEBUG-PARSER    (format t "~&;;; DEBUG-PARSER    feature is off.~%")
#+OPTIMIZE-PARSER (format t "~&;;; OPTIMIZE-PARSER feature is on.~%")
#-OPTIMIZE-PARSER (format t "~&;;; OPTIMIZE-PARSER feature is off.~%")

#+COMPILER ; don't delete fasl files if there is no compiler to recreate them
(dolist (f (directory (format nil "~A/Library/Algorithms/Parsing/Chart/Handwritten/Lisp/*.~A" 
			      specware::specware4
			      specware::*fasl-type*)))
  (delete-file f))
    
#+DEBUG-PARSER 
(proclaim '(optimize (speed 0) (safety 3) (compilation-speed 0) (space 0) (debug 3)))

#-DEBUG-PARSER 
(progn
  #+OPTIMIZE-PARSER
  (proclaim '(optimize (speed 3) (safety 0) (compilation-speed 0) (space 0) (debug 0)))
  #-OPTIMIZE-PARSER
  (proclaim '(optimize (speed 3) (safety 1) (compilation-speed 0) (space 0) (debug 2)))
  )

(defmacro parser4::when-debugging (&body body)  
  #-DEBUG-PARSER ()
  #+DEBUG-PARSER `(progn ,@body)
  )

(defmacro parser4::debugging-comment (&body body) 
  `(parser4::when-debugging 
    (when parser4::*verbose?*
      (parser4::comment ,@body))))

(compile-and-load-local-file "comment-hack")
(compile-and-load-local-file "parse-decls")

#+DEBUG-PARSER (compile-and-load-local-file "parse-debug-1")
#-DEBUG-PARSER (defun parser4::verify-all-parser-rule-references (parser) (declare (ignore parser)) nil)

(compile-and-load-local-file "parse-add-rules")
(compile-and-load-local-file "seal-parser")

(compile-and-load-local-file "parse-node-utilities")

(compile-and-load-local-file "tokenizer-decls")
(compile-and-load-local-file "tokenizer")

(compile-and-load-local-file "parse-semantics")
;;   (compile-and-load-local-file  "pprint") ; will be here soon 

(compile-and-load-local-file "parse-top")

#+DEBUG-PARSER (compile-and-load-local-file "parse-debug-2")

(compile-and-load-local-file "describe-grammar")

(with-open-file (s (format nil "~A/Library/Algorithms/Parsing/Chart/Handwritten/Lisp/log.~A.status"
			   specware::specware4
			   specware::*fasl-type*)
		   :direction :output :if-exists :supersede)
  (format s "~%;;; When lisp files were last compiled to ~A files ~A,~%"
	  specware::*fasl-type*
	  (multiple-value-bind (sec min hour day month year)
	      (decode-universal-time (get-universal-time))
	    (format nil "at ~2,'0D:~2,'0D:~2,'0D on ~4,'0D-~2,'0D-~2,'0D" 
		    hour min sec year month day)))
  (format s "~&;;;~%")
  (format s "~&;;;  DEBUG-PARSER    was ~A,~%"
	  #+DEBUG-PARSER "on"
	  #-DEBUG-PARSER "off")
  (format s "~&;;;  OPTIMIZE-PARSER was ~A.~%"
	  #+OPTIMIZE-PARSER "on"
	  #-OPTIMIZE-PARSER "off"))
