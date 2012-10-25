;; for simplicity, use the same package that GatherComponents.lisp uses
(defpackage :Distribution)
(in-package :Distribution")

(eval-when (compile eval load)
  #+Allegro (require "dist-utils")
  ; #-Allegro (load    "dist-utils")
  )


;;; Utilities for environment vars

(defun generic-getenv (varname)
  #+allegro   (si::getenv varname)
  #+mcl       (or (cdr (assoc (intern varname "KEYWORD") *environment-shadow*))
		  (ccl::getenv varname))
  #+lispworks (hcl::getenv varname) 	;?
  #+cmu       (cdr (assoc (intern varname "KEYWORD") ext:*environment-list*))
  #+sbcl      (sb-ext:posix-getenv  varname)
  #+gcl       (si:getenv varname)
  #+clisp     (ext:getenv varname)
  #-(or allegro mcl lispworks cmu sbcl gcl clisp)
              (error "Distribution::generic-getenv undefined for ~A, which is not Allegro, MCL, LISPWORKS, CMU, SBCL, or GCL"
		     (lisp-implementation-type))
  )

(defun generic-setenv (varname newvalue)
  #+allegro   (setf (si::getenv varname) newvalue)
  #+mcl       (let ((pr (assoc (intern varname "KEYWORD") *environment-shadow*)))
		(if pr (setf (cdr pr) newvalue)
		  (push (cons (intern varname "KEYWORD") newvalue)
			*environment-shadow*)))
  #+lispworks (setf (hcl::getenv varname) newvalue) 
  #+cmu       (let ((pr (assoc (intern varname "KEYWORD") ext:*environment-list*)))
		(if pr (setf (cdr pr) newvalue)
		  (push (cons (intern varname "KEYWORD") newvalue)
			ext:*environment-list*)))
  #+sbcl      (progn (sb-unix::int-syscall ("setenv" sb-alien:c-string sb-alien:c-string sb-alien:int)
					   varname newvalue 1)
		     (getenv varname))
  #+gcl       (si:setenv varname newvalue)
  #+clisp     (setf (ext:getenv varname) newvalue)
  #-(or allegro mcl lispworks cmu sbcl gcl clisp)
              (error "Distribution::generic-setenv undefined for ~A, which is not Allegro, MCL, LISPWORKS, CMU, SBCL, or GCL"
		     (lisp-implementation-type))
  )

#+Allegro (provide "env-utils")
