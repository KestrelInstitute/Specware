;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defvar Accord-version "1.0")
(defvar Accord-version-name "Accord-1-0")
(defvar Accord-name "Accord")	; Name of directory and startup files
(defvar Accord-dir (sys:getenv "ACCORD"))
(defvar Specware-dir (sys:getenv "SPECWARE4"))
(defun in-accord-dir (file) (concatenate 'string Accord-dir "/" file))
(defun in-specware-dir (file) (concatenate 'string Specware-dir "/" file))
(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defparameter distribution-directory 
  (in-accord-dir  (concatenate 'string "distribution/" Accord-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
(when (probe-file distribution-directory)
  (excl::delete-directory-and-files distribution-directory))

(generate-application
  ;; this is the name of the application
  Accord-name

  ;; this is the directory where the application is to go
  ;; (plus accompanying files) 
  distribution-directory

  ;; a list of files to load
  (mapcar #'(lambda (file) (format nil "~A/Applications/Specware/Handwritten/Lisp/~A.lisp" 
				   Specware-dir
				   file))
	  '("BuildPreamble" "Specware4" "load-accord" "accord-license"))

  ;; a list of files to copy to the distribution directory
  :application-files
  (list ;;; (in-accord-dir "/Library/")
	;;; (in-accord-dir "/Applications/Accord/Courses/")
   (in-accord-dir "Scripts/windows/Accord.cmd"))

  ;; Possible option instead of excl::delete-directory-and-files call
  ;;  :allow-existing-directory t

  ;; the image does not have a compiler neither during the build nor after.
  ;; The application has the interpreter only.
  :include-compiler nil

  ;; which runtime? the other option is :dynamic which includes the compiler
  :runtime :standard
  )

;;; Copy needed directories to distribution
(copy-directory (in-specware-dir "Library/Base/")
		(in-distribution-dir "Library/Base/"))
;(copy-file (in-specware-dir "Library/Base.sw")
;	   (in-distribution-dir "Library/Base.sw"))
(copy-directory (in-specware-dir "Library/IO/Emacs/")
		(in-distribution-dir "Library/IO/Emacs/"))
(copy-directory (in-specware-dir "UserDoc/tutorial/example/")
		(in-distribution-dir "Examples/Matching/"))
(copy-directory (in-specware-dir "UserDoc/examples/")
		(in-distribution-dir "Examples/"))

(copy-directory (in-accord-dir "Sources/Handwritten/")
		(in-distribution-dir "Sources/Handwritten/"))

(copy-directory (in-lisp-dir "xeli/")
		(in-distribution-dir "Sources/Handwritten/IO/Emacs/xeli/"))
