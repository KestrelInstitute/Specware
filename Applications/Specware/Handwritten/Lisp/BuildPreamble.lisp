(defpackage "SYSTEM-SPEC")
(defpackage "SPECWARE")
(in-package "SPECWARE")

;;; This file is loaded before Specware4.lisp when generating
;;; a Specware distribution

;;;The next three variable initializations need to be changed when going to a new minor version

;; Used in printing out the license and about-specware command
(defvar user::Specware-version "4.0")
(defvar user::Specware-version-name "Specware-4-0")
(defvar user::Specware-patch-level "1")

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-0")

;;; Normally autoloaded, but we want to preload them for a stand-alone world
(require "eli")
(require "sock")
(require "trace")

;; Override normal definition because of an apparent Allegro bug in
;; generate-application where excl::compile-file-if-needed compiles
;; even if not needed
(defun compile-file-if-needed (file) file)

;;;Patch .fasl files will be named in the form "patch-4-0-x.fasl" and
;;;will probably be copied into a Patches folder in the installation
;;;directory.  Old patch files will not be removed or overwritten.

(defun patch-directory ()
  (let ((specware-dir (system-spec::getEnv "SPECWARE4")))
    (if (equal specware-dir '(:|None|))
	(warn "patch-directory: SPECWARE4 environment variable not set")
      (concatenate 'string (cdr specware-dir) "/Patches/"))))

(defun patch-number (path)
  (or (ignore-errors
       (let* ((file-name (pathname-name path))
	      (major-version-len (length Major-Version-String)))
	 (if (and (string-equal (pathname-type path) excl:*fasl-default-type*)
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
	 (highest-patch-file nil))
    (loop for file in files
       do (let ((patch-num (patch-number file)))
	    (when (> patch-num highest-patch-number)
	      (setq highest-patch-number patch-num)
	      (setq highest-patch-file file))))
    (when (> highest-patch-number 0)
      (setq user::Specware-patch-level highest-patch-number)
      (ignore-errors (load highest-patch-file)))))

#+allegro
(setq cl-user::*restart-init-function* 'load-specware-patch-if-present)