(defpackage "SPECWARE" (:use "CL"))
(in-package "SPECWARE")

;;; This file is loaded before Specware4.lisp when generating
;;; a Specware distribution

;;; Get version information from canonical source...
(let ((specware4 (specware::getenv "SPECWARE4")))
  (if (equal specware4 nil)
      (error "in BuildSpecwarePreamble.lisp:  SPECWARE4 environment variable not set")
    (let ((specware-dir
	   (let ((dir (substitute #\/ #\\ specware4)))
	     (if (eq (schar dir (1- (length dir))) #\/)
		 dir
	       (concatenate 'string dir "/")))))
      (let ((version-file (format nil "~AApplications/Specware/Handwritten/Lisp/SpecwareVersion.lisp"
				  specware-dir)))
	(if (probe-file version-file)
	    (load version-file)
	  (error "in BuildSpecwarePreamble.lisp:  Cannot find ~A" version-file))))))

(push ':SPECWARE-DISTRIBUTION *features*) ; used by parser

;;; Normally autoloaded, but we want to preload them for a stand-alone world
#+(and allegro mswindows)
(require "eli")
#+allegro
(require "sock")
#+allegro
(require "trace")
#+allegro
(require "fileutil")

;;; If there is a compiler, then fasl files will have been deleted
;;; to avoid version incompatibilities, in which case we need the
;;; normal definition of compile-file-if-needed
;;; But if there is no compiler, then we should avoid attempting
;;; to call it.
#-(or COMPILER NEW-COMPILER)
(defun compile-file-if-needed (file) file)

;;; Override normal definition because of an apparent Allegro bug in
;;; generate-application where excl::compile-file-if-needed compiles
;;; even if not needed
;;; Comment out for now to see if problem has gone away...
;;; #+ALLEGRO 
;;; (defun compile-file-if-needed (file) file)

;;;Patch .fasl files will be named in the form "patch-4-2.fasl" and
;;;will probably be copied into a Patches folder in the installation
;;;directory.  Old patch files will not be removed or overwritten.

(defparameter *Specware-dir*  (format nil "~A/" (specware::getenv "SPECWARE4")))

(defun in-specware-dir (file) 
  (concatenate 'string *Specware-dir* file))

(defun patch-directory ()
  (declare (special *specware-dir*))
  (if (equal *specware-dir* nil)
      (warn "patch-directory: SPECWARE4 environment variable not set")
    (in-specware-dir "Patches/")))

#+SBCL (setq sb-fasl:*fasl-file-type* "sfsl") ; default is "fasl", which conflicts with Allegro

(defvar *fasl-type*
  #+CMU     "x86f"
  #+SBCL    sb-fasl:*fasl-file-type*
  #+Allegro "fasl" 
  #+OpenMCL "???"
  #-(or CMU SBCL Allegro OpenMCL) "unknown-fasl")

(defun patch-number (path)
  (declare (special cl-user::*Specware-Major-Version-String*))
  (or (ignore-errors
       (let* ((file-name (pathname-name path))
	      (major-version-len (length cl-user::*Specware-Major-Version-String*)))
	 (if (and (string-equal (pathname-type path) specware::*fasl-type*)
		  (string-equal file-name "patch-" :end1 6)
		  (string-equal file-name cl-user::*Specware-Major-Version-String*
				:start1 6 :end1 (+ major-version-len 6))
		  (eq (elt file-name (+ major-version-len 6)) #\-))
	     (let ((num? (read-from-string (subseq file-name (+ major-version-len 7)))))
	       (if (integerp num?) num? 0))
	   0)))
      0))

(defun load-specware-patch-if-present ()
  (declare (special cl-user::*Specware-Patch-Level*))
  (let* ((patch-dir (patch-directory))
	 (files (cl:directory patch-dir))
	 (highest-patch-number 0)
	 (highest-patch-file nil)
	 #+allegro *redefinition-warnings*)
    (loop for file in files
       do (let ((patch-num (patch-number file)))
	    (when (> patch-num highest-patch-number)
	      (setq highest-patch-number patch-num)
	      (setq highest-patch-file file))))
    (when (> highest-patch-number 0)
      (setq cl-user::*Specware-Patch-Level* highest-patch-number)
      (ignore-errors (load highest-patch-file)))))

(push 'load-specware-patch-if-present
       #+allegro common-lisp-user::*restart-actions*
       #+cmu     ext:*after-save-initializations*
       #+mcl     ccl:*lisp-startup-functions*
       #+sbcl    sb-ext:*init-hooks*)
