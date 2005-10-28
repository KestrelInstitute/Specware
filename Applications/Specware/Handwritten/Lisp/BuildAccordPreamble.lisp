(defpackage "SPECWARE")
(in-package "SPECWARE")

;;; This file is loaded before Specware4.lisp when generating
;;; a Specware distribution

;;;The next three variable initializations need to be changed when going to a new minor version

;; Used in printing out the license and about-specware command
(defvar cl-user::Accord-version "4.1")
(defvar cl-user::Accord-version-name "Accord-4-1")
(defvar cl-user::Accord-patch-level "4")
(defvar cl-user::Accord-name "Accord")	; Name of directory and startup files

(defvar cl-user::Specware-version "4.1")
(defvar cl-user::Specware-version-name "Specware-4-1")
(defvar cl-user::Specware-patch-level "4")

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-1")

;;; Normally autoloaded, but we want to preload them for a stand-alone world
#+(and allegro mswindows)
(require "eli")
#+(and allegro mswindows)
(require "sock")
#+(and allegro mswindows)
(require "trace")


;; Override normal definition because of an apparent Allegro bug in
;; generate-application where excl::compile-file-if-needed compiles
;; even if not needed
#+allegro
(defun compile-file-if-needed (file) file)

;;;Patch .fasl files will be named in the form "patch-4-0-x.fasl" and
;;;will probably be copied into a Patches folder in the installation
;;;directory.  Old patch files will not be removed or overwritten.

(defun patch-directory ()
  (let ((specware-dir (specware::getEnv "SPECWARE4")))
    ;; system-spec::getEnv returns  (:|Some| . <string>)  or  (:|None|)
    ;;    specware::getEnv returns  <string>              or  NIL.
    ;; system-spec package is missing in cmulisp release, for some reason
    (if (equal specware-dir nil)
	(warn "patch-directory: SPECWARE4 environment variable not set")
      (concatenate 'string specware-dir "/Patches/"))))

(defun patch-number (path)
  (or (ignore-errors
       (let* ((file-name (pathname-name path))
	      (major-version-len (length Major-Version-String)))
	 (if (and (string-equal (pathname-type path) specware::*fasl-type*)
		  (string-equal file-name "patch-" :end1 6)
		  (string-equal file-name Major-Version-String
				:start1 6 :end1 (+ major-version-len 6))
		  (eq (elt file-name (+ major-version-len 6)) #\-))
	     (let ((num? (read-from-string (subseq file-name (+ major-version-len 7)))))
	       (if (integerp num?) num? 0))
	   0)))
      0))

(defun load-specware-patch-if-present ()
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
      (setq cl-user::Specware-patch-level highest-patch-number)
      (ignore-errors (load highest-patch-file)))))

#+allegro
(push 'load-specware-patch-if-present cl-user::*restart-actions*)

#+cmu
(push 'load-specware-patch-if-present ext:*after-save-initializations*)
