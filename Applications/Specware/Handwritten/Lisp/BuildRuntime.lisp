;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defvar Specware-version "4.0")
(defvar Specware-version-name "Specware-4-0")
(defvar Specware-name "Specware4")	; Name of directory and startup files
(defvar Specware4-dir (sys:getenv "SPECWARE4"))
(defun in-specware-dir (file) (concatenate 'string Specware4-dir "/" file))

(defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defparameter distribution-directory 
  (in-specware-dir  (concatenate 'string "distribution/" Specware-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; If the application directory already exists, then we delete it.
;; generate-application complains and dies if the directory exists.
(when (probe-file (make-pathname :directory distribution-directory))
  (excl::delete-directory-and-files
    (make-pathname :directory distribution-directory)))

(generate-application
  ;; this is the name of the application
  Specware-name

  ;; this is the directory where the application is to go
  ;; (plus accompanying files) 
  distribution-directory

  ;; a list of files to load
  '("BuildPreamble.lisp" "Specware4.lisp" "license.lisp")

  ;; a list of files to copy to the distribution directory
  :application-files
  (list (in-specware-dir "Release/Specware4.cmd"))

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
(sys:copy-file (in-specware-dir "Library/Base.sw")
	   (in-distribution-dir "Library/Base.sw"))
(delete-directory-and-files (in-distribution-dir "Library/Base/CVS/"))
(delete-file (in-distribution-dir "Library/Base/System.sw"))

(copy-directory (in-specware-dir "Applications/Specware/Courses/NSA_Sept_2002/")
		(in-distribution-dir "Examples/"))
(delete-directory-and-files (in-distribution-dir "Examples/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/Matching/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple1/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple2/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple3/CVS/"))

(copy-directory (in-lisp-dir "xeli/")
		(in-distribution-dir "Library/IO/Emacs/xeli/"))

(make-directory (in-distribution-dir "Documentation/"))
(sys:copy-file (in-specware-dir "UserDoc/language-manual/SpecwareLanguageManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(sys:copy-file (in-specware-dir "UserDoc/tutorial/SpecwareTutorial.pdf")
	   (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(sys:copy-file (in-specware-dir "UserDoc/user-manual/SpecwareUserManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
