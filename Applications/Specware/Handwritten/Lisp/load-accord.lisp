(defpackage "SPECWARE")
(in-package "USER")

;;; ============================================================================
;;;                       MAIN BUILD SCRIPT
;;;
;;;      This file is loaded by Accord/Scripts/unix/build-accord
;;;                      and by Accord/Scripts/emacs/accord.el
;;; ============================================================================

(proclaim '(optimize (speed 3) (safety 1) (space 0) (debug 0) (compilation-speed 0)))

#+ALLEGRO
(setq comp:*cltl1-compile-file-toplevel-compatibility-p* t) ; default is WARN, which would be very noisy

(defun specware::getenv (varname) ; duplicate of definition in load-utilities.lisp
  #+allegro   (system::getenv varname)
  #+mcl       (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
		  (ccl::getenv varname))
  #+lispworks (hcl::getenv varname) 	;?
  #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
  )

(defvar *SPECWARE4* (specware::getenv "SPECWARE4"))
(defvar SPECWARE::SPECWARE4 *SPECWARE4*)
(defvar *ACCORD*    (specware::getenv "ACCORD"))
  
(if (null *SPECWARE4*)
    (warn "SPECWARE4 environment var not set")
  (format t "~%SPECWARE4 = ~S~%" *SPECWARE4*))

(if (null *ACCORD*)
    (warn "ACCORD environment var not set")
  (format t "~&ACCORD    = ~S~%~%" *ACCORD*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; functions used locally here 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun specware-file (x) (concatenate 'string *SPECWARE4* "/" x))
(defun accord-file   (x) (concatenate 'string *ACCORD*    "/" x))

(defun load-specware-file (x)
  ;; specware::load-fasl-file 
  (specware::compile-and-load-lisp-file (specware-file x)))

(defun load-accord-file (x)
  ;; specware::load-fasl-file 
  (specware::compile-and-load-lisp-file (accord-file x)))

(defun process-specware-file (x)
  (load-specware-file x))

(defun process-accord-file (x)
  (load-accord-file x))

(load (accord-file "Scripts/Lisp/process-files.lisp"))
