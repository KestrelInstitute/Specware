;; This file builds a distribution directory for Specware.


(defvar Specware-name "Specware4")	; Name of directory and startup files
(defvar Specware4-dir (specware::getenv "SPECWARE4"))
(defun in-specware-dir (file) (concatenate 'string Specware4-dir "/" file))

;; dist-dir-name is the sub-directory to receive this particular distribution.
;; In particular, this is where generate-application puts all its stuff.
#+cmu
(defvar dist-dir-name "distribution-cmulisp/")
#+allegro
(defvar dist-dir-name "distribution-allegro/")

(defparameter distribution-directory 
  (in-specware-dir  (concatenate 'string dist-dir-name Specware-name "/")))
(defun in-distribution-dir (file) (concatenate 'string distribution-directory file))

;; in-lisp-dir is used to get some emacs files used by allegro runtime
#+allegro
(progn
  #+mswindows
  (defun in-lisp-dir (file) (concatenate 'string (sys:getenv "ALLEGRO") "/" file))
  #+linux
  (defun in-lisp-dir (file) (concatenate 'string "/usr/local/acl/acl62/" file))
)


;;; Load these for Linux builds
#+linux
(progn
  (load "BuildPreamble.lisp")
  (load "Specware4.lisp")
  (load "license.lisp")
)

;;; For Windows, we use the Allegro Enterprise gen-app facility
#+mswindows
(progn

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
    (list (in-specware-dir "Release/Windows/Specware4.cmd"))

    ;; Possible option instead of excl::delete-directory-and-files call
    ;;  :allow-existing-directory t

    ;; the image does not have a compiler neither during the build nor after.
    ;; The application has the interpreter only.
    :include-compiler nil

    ;; which runtime? the other option is :dynamic which includes the compiler
    :runtime :standard
  )
)

;;; Copy needed directories to distribution, deleting CVS/ directories and other
;;; stuff that users shouldn't see

;;; Base specs and handwritten lisp from Specware4/Library/

(specware::copy-directory (in-specware-dir "Library/Base/")
		(in-distribution-dir "Library/Base/"))
(specware::copy-file (in-specware-dir "Library/Base.sw")
	   (in-distribution-dir "Library/Base.sw"))
(specware::delete-directory-and-files (in-distribution-dir "Library/Base/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Library/Base/Handwritten/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Library/Base/Handwritten/Lisp/CVS/"))

;;(delete-file (in-distribution-dir "Library/Base/Handwritten/Lisp/.cvsignore"))

;;; Emacs stuff from Library/IO (& acl directory, if using acl)

(specware::copy-directory (in-specware-dir "Library/IO/Emacs/")
		(in-distribution-dir "Library/IO/Emacs/"))
(specware::delete-directory-and-files (in-distribution-dir "Library/IO/Emacs/CVS/"))
(delete-file (in-distribution-dir "Library/IO/Emacs/.cvsignore"))
(specware::delete-directory-and-files (in-distribution-dir "Library/IO/Emacs/ilisp/CVS/"))

#+allegro
(specware::copy-directory (in-lisp-dir "xeli/")
		(in-distribution-dir "Library/IO/Emacs/xeli/"))

;;; Matching Example specs from Specware4/UserDoc/tutorial/example & Simple example specs

(specware::copy-directory (in-specware-dir "UserDoc/tutorial/example/")
		(in-distribution-dir "Examples/Matching/"))
(specware::copy-directory (in-specware-dir "UserDoc/examples/")
		(in-distribution-dir "Examples/"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/Matching/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/simple1/CVS/"))
(delete-file (in-distribution-dir "Examples/simple1/test.lisp"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/simple2/CVS/"))
(delete-file (in-distribution-dir "Examples/simple2/test.lisp"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/simple2/Refs/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/simple2/Specs/CVS/"))
(specware::delete-directory-and-files (in-distribution-dir "Examples/simple3/CVS/"))
(delete-file (in-distribution-dir "Examples/simple3/test.lisp"))

;;; Documentation pdf's from Specware4/UserDoc/

(specware::make-directory (in-distribution-dir "Documentation/"))
(specware::copy-file (in-specware-dir "UserDoc/language-manual/SpecwareLanguageManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/tutorial/SpecwareTutorial.pdf")
	   (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/user-manual/SpecwareUserManual.pdf")
	   (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
(specware::copy-file (in-specware-dir "UserDoc/cheat-sheet/Specware-405-QuickReference.pdf")
	   (in-distribution-dir "Documentation/Specware-QuickReference.pdf"))

;;; Current (highest-numbered) patch from Specware4/Release/Patches/

(specware::make-directory (in-distribution-dir "Patches/"))
#+mswindows
(specware::copy-file (in-specware-dir "Release/Patches/ansi-loop.fasl")
	       (in-distribution-dir "Patches/ansi-loop.fasl"))

(defun patch-number (path)
  (or (ignore-errors
       (let* ((file-name (pathname-name path))
	      (major-version-len (length Major-Version-String)))
	 (if (and (string-equal (pathname-type path) specware::*fasl-default-type*)
		  (string-equal file-name "patch-" :end1 6)
		  (string-equal file-name Major-Version-String
				:start1 6 :end1 (+ major-version-len 6))
		  (eq (elt file-name (+ major-version-len 6)) #\-))
	     (let ((num? (read-from-string (subseq file-name (+ major-version-len 7)))))
	       (if (integerp num?) num? 0))
	   0)))
      0))

(defvar *patch-dir-name*
  #+mswindows
  "Release/Windows/Patches/"
  #+(and linux cmu)
  "Release/Linux/CMU/Patches/"
  #+(and linux allegro)
  "Release/Linux/Allegro/Patches/"
)

(defun copy-specware-patch-if-present ()
  (let* ((patch-dir (in-specware-dir *patch-dir-name*))
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
      (ignore-errors (specware::copy-file highest-patch-file (in-distribution-dir 
							(concatenate 'list "Patches/" (pathname-name highest-patch-file) 
								     "." (pathname-type highest-patch-file))))))))


(copy-specware-patch-if-present)


;;; Copy appropriate Specware image & startup script
#+cmu
(specware::copy-file (in-specware-dir "Applications/Specware/bin/linux/Specware4.cmuimage")
	       (in-distribution-dir "Specware4.cmuimage"))
#+cmu
(specware::copy-file (in-specware-dir "Release/Linux/CMU/Specware-cmulisp")
	       (in-distribution-dir "Specware-cmulisp"))

#+(and allegro linux)
  (specware::copy-file(in-specware-dir "Applications/Specware/bin/linux/Specware4.dxl")
	        (in-distribution-dir "Specware4.dxl"))
#+(and allegro linux)
  (specware::copy-file (in-specware-dir "Release/Linux/Allegro/Specware4")
	        (in-distribution-dir "Specware4"))