;; This builds the Specware4 distribution for users who already have an Allegro license.
;; Namely, a directory containing the Specware4 image, start up script, documentation,
;; libraries, and patch file(s) is built by loading this build file.

;; These two definitions might not be needed here
;; They are in BuildPreamble.lisp where they are needed
(defvar Specware-version "4.0")
(defvar Specware-version-name "Specware-4-0")
(defvar Specware-name "Specware4")	; Name of directory and startup files
(defvar Specware4-dir (sys:getenv "SPECWARE4"))
(defun in-specware-dir (file) (concatenate 'string Specware4-dir "/" file))

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-0")

;; This is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
(defparameter distribution-directory 
  (in-specware-dir  (concatenate 'string "distribution/" Specware-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;;; Copy needed directories to distribution, deleting CVS/ directories and other
;;; stuff that users shouldn't see

;;; Base specs and handwritten lisp from Specware4/Library/

(copy-directory (in-specware-dir "Library/Base/")
		(in-distribution-dir "Library/Base/"))
(sys:copy-file (in-specware-dir "Library/Base.sw")
	   (in-distribution-dir "Library/Base.sw"))
(delete-directory-and-files (in-distribution-dir "Library/Base/CVS/"))
(delete-directory-and-files (in-distribution-dir "Library/Base/Handwritten/CVS/"))
(delete-directory-and-files (in-distribution-dir "Library/Base/Handwritten/Lisp/CVS/"))
(delete-file (in-distribution-dir "Library/Base/Handwritten/Lisp/.cvsignore"))

;;; Emacs stuff from Library/IO & acl directory

(copy-directory (in-specware-dir "Library/IO/Emacs/")
		(in-distribution-dir "Library/IO/Emacs/"))
(delete-directory-and-files (in-distribution-dir "Library/IO/Emacs/ilisp-20020831/"))
(delete-directory-and-files (in-distribution-dir "Library/IO/Emacs/CVS/"))
(delete-file (in-distribution-dir "Library/IO/Emacs/.cvsignore"))

(copy-directory "/usr/local/acl/acl62/xeli/"
		(in-distribution-dir "Library/IO/Emacs/xeli/"))

;;; Matching Example specs from Specware4/UserDoc/tutorial/example

(copy-directory (in-specware-dir "UserDoc/tutorial/example/")
		(in-distribution-dir "Examples/Matching/"))
(copy-directory (in-specware-dir "UserDoc/examples/")
		(in-distribution-dir "Examples/"))
(delete-directory-and-files (in-distribution-dir "Examples/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/Matching/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple1/CVS/"))
(delete-file (in-distribution-dir "Examples/simple1/test.lisp"))
(delete-directory-and-files (in-distribution-dir "Examples/simple2/CVS/"))
(delete-file (in-distribution-dir "Examples/simple2/test.lisp"))
(delete-directory-and-files (in-distribution-dir "Examples/simple2/Refs/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple2/Specs/CVS/"))
(delete-directory-and-files (in-distribution-dir "Examples/simple3/CVS/"))
(delete-file (in-distribution-dir "Examples/simple3/test.lisp"))

;;; Documentation pdf's from Specware4/UserDoc/

(make-directory (in-distribution-dir "Documentation/"))
(sys:copy-file (in-specware-dir "UserDoc/language-manual/SpecwareLanguageManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(sys:copy-file (in-specware-dir "UserDoc/tutorial/SpecwareTutorial.pdf")
	   (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(sys:copy-file (in-specware-dir "UserDoc/user-manual/SpecwareUserManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))

;;; Current (highest-numbered) patch from Specware4/Release/Patches/

(make-directory (in-distribution-dir "Patches/"))
(sys:copy-file (in-specware-dir "Release/Patches/ansi-loop.fasl")
	       (in-distribution-dir "Patches/ansi-loop.fasl"))

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

(defun copy-specware-patch-if-present ()
  (let* ((patch-dir (in-specware-dir "Release/Patches/"))
	 (files (cl:directory patch-dir))
	 (highest-patch-number 0)
	 (highest-patch-file nil))
    (loop for file in files
       do (let ((patch-num (patch-number file)))
	    (when (> patch-num highest-patch-number)
	      (setq highest-patch-number patch-num)
	      (setq highest-patch-file file))))
    (when (> highest-patch-number 0)
      (setq cl-user::Specware-patch-level highest-patch-number)
      (ignore-errors (sys:copy-file highest-patch-file (in-distribution-dir 
							(concatenate 'list "Patches/" (pathname-name highest-patch-file) 
								     "." (pathname-type highest-patch-file))))))))


(copy-specware-patch-if-present)

;;; Specware4.dxl & Specware4 startup script
(sys:copy-file (in-specware-dir "Applications/Specware/bin/linux/Specware4.dxl")
	       (in-distribution-dir "Specware4.dxl"))
(sys:copy-file (in-specware-dir "Release/Linux/Specware4")
	       (in-distribution-dir "Specware4"))

