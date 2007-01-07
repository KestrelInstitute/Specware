(defpackage "SPECWARE")
(in-package "SPECWARE")

;;; This file is loaded before Specware4.lisp when generating
;;; a Specware distribution

;;;The next three variable initializations need to be changed when going to a new minor version

;; Used in printing out the license and about-specware command
(defparameter cl-user::Specware-version      "4.2")
(defparameter cl-user::Specware-version-name "Specware-4-2")
(defparameter cl-user::Specware-patch-level  "0")
(defparameter Major-Version-String           "4-2") ; Used in patch detection and about-specware command

(push ':SPECWARE-DISTRIBUTION *features*)

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
#-(or COMPILER NEW-COMPILER) ; cmucl has NEW-COMPILER (sigh)
(defun compile-file-if-needed (file) file)

;;;Patch .fasl files will be named in the form "patch-4-2-x.fasl" and
;;;will probably be copied into a Patches folder in the installation
;;;directory.  Old patch files will not be removed or overwritten.

(defun patch-directory ()
  (if (equal specware-dir nil)
      (warn "patch-directory: SPECWARE4 environment variable not set")
    (in-specware-dir "Patches/")))

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

(push 'load-specware-patch-if-present 
       #+allegro cl-user::*restart-actions*
       #+cmu     ext:*after-save-initializations*
       #+mcl     ccl:*lisp-startup-functions*
       #+sbcl    sb-ext:*init-hooks*)
