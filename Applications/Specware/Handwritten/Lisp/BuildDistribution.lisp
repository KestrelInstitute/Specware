;; This file builds a distribution directory for Window/Allegro Runtime Specware.

(defpackage :Specware)

(defvar Specware-name "Specware4")	; Name of directory and startup files
(defvar Specware4-dir (specware::getenv "SPECWARE4"))
;;(defvar Specware4-dir "C:/Progra~1/Specware4-0-7/Specware4")
(defun in-specware-dir (file) (concatenate 'string Specware4-dir "/" file))

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-1")

;; dist-dir-name is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defvar dist-dir-name "distribution/")

(defparameter distribution-directory 
  (in-specware-dir  (concatenate 'string dist-dir-name Specware-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; in-lisp-dir is used to get some emacs files used by allegro runtime
(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;;; For Windows, we use the Allegro Enterprise gen-app facility

  ;; If the application directory already exists, then we delete it.
  ;; generate-application complains and dies if the directory exists.
;;  (when (probe-file (make-pathname :directory distribution-directory))
;;    (excl::delete-directory-and-files
;;      (make-pathname :directory distribution-directory)))

  (excl:generate-application
    ;; this is the name of the application
    Specware-name

    ;; this is the directory where the application is to go
    ;; (plus accompanying files) 
    distribution-directory

    ;; a list of files to load
    '("BuildPreamble.lisp" "Specware4.lisp" "license.lisp")

    ;; a list of files to copy to the distribution directory
    :application-files
    (list (in-specware-dir "Release/Windows/Specware4.cmd")
	  (in-specware-dir "Release/Windows/Specware4 Shell.cmd")
	  (in-specware-dir "Applications/Specware/Handwritten/Lisp/StartShell.lisp"))

    ;; Possible option instead of excl::delete-directory-and-files call
    :allow-existing-directory t

    ;; the image does not have a compiler neither during the build nor after.
    ;; The application has the interpreter only.
    :include-compiler nil

    ;; which runtime? the other option is :dynamic which includes the compiler
    :runtime :standard
  )

(load (in-specware-dir "Applications/Specware/Handwritten/Lisp/copy-files-for-distribution.lisp"))

(specware::copy-directory (in-lisp-dir "xeli/") (in-distribution-dir "Library/IO/Emacs/xeli/"))
