;;; Loaded from BuildDistribution_ACL.lisp
;;; Moves a variety of files to the distribution directory.

;;; Assumes distribution dir is something like:
;;;   C:/SpecwareReleases/Specware-4-1-4/Windows/Specware4
;;;   Also assumes the directory contains only stuff that
;;    generate-application has just placed in it.

(in-package :cl-user)

;;; ============ SPECWARE LIBRARY  ============

(format t "~&~%")
(format t "~&;;; Getting Specware library ...~%")

;;; Copy needed directories to distribution
;;; Flushes CVS sub-directories and .cvsignore files

(specware::make-directory (in-distribution-dir "Library/"))
(specware::copy-directory (in-specware-dir     "Library/Base/")
			  (in-distribution-dir "Library/Base/"))
(delete-dir-if-present    (in-distribution-dir "Library/Base/CVS/"))
(delete-dir-if-present    (in-distribution-dir "Library/Base/Handwritten/CVS/"))
(delete-dir-if-present    (in-distribution-dir "Library/Base/Handwritten/Lisp/CVS/"))
(delete-file-if-present   (in-distribution-dir "Library/Base/Handwritten/Lisp/.cvsignore"))

(specware::copy-directory (in-specware-dir     "Library/ProverBase/")
			  (in-distribution-dir "Library/ProverBase/"))
(delete-dir-if-present    (in-distribution-dir "Library/ProverBase/CVS/"))

(specware::copy-file      (in-specware-dir     "Library/Base.sw")
                          (in-distribution-dir "Library/Base.sw"))
(specware::copy-file      (in-specware-dir     "Library/InterpreterBase.sw")
                          (in-distribution-dir "Library/InterpreterBase.sw"))

(specware::make-directory (in-distribution-dir "Library/IO/"))
(specware::copy-directory (in-specware-dir     "Library/IO/Emacs/")
			  (in-distribution-dir "Library/IO/Emacs/"))
(delete-dir-if-present    (in-distribution-dir "Library/IO/Emacs/CVS/"))
(delete-dir-if-present    (in-distribution-dir "Library/IO/Emacs/ilisp/CVS/"))

(specware::concatenate-files
   (loop for fil in '("Base/Handwritten/Lisp/Integer"
		      "Base/Handwritten/Lisp/Nat"
		      "Base/Handwritten/Lisp/Char"
		      "Base/Handwritten/Lisp/String"
		      "Base/Handwritten/Lisp/System"
		      "IO/Primitive/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/State"
		      "Legacy/Utilities/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/Lisp"
		      "Structures/Data/Monad/Handwritten/Lisp/State"
		      "../Applications/Handwritten/Lisp/meta-slang-runtime"
		      "../Applications/Specware/Handwritten/Lisp/ProvideSpecwareRuntime")
      collect (in-specware-dir (format nil "Library/~a.lisp" fil)))
   (in-distribution-dir "Library/SpecwareRuntime.lisp"))

;;; ============ EMACS SUPPORT ============


(format t "~&;;;~%")
(if (probe-file (in-distribution-dir "Library/IO/Emacs/xeli/"))
    (format t "~&;;; Getting Allegro/emacs interface already in specware libarary. ...~%")
  (progn
    (format t "~&;;; Getting Allegro/emacs interface from ~A ...~%" (in-lisp-dir "xeli/"))
    (specware::copy-directory (in-lisp-dir "xeli/") 
			      (in-distribution-dir "Library/IO/Emacs/xeli/"))))

;;; ============ EXAMPLES ============

(format t "~&;;;~%")
(format t "~&;;; Getting Examples ...~%")

(specware::make-directory (in-distribution-dir "Examples/"))
(specware::copy-directory (in-specware-dir     "UserDoc/tutorial/example/")
			  (in-distribution-dir "Examples/Matching/"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/CVS"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/Snark"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/lisp"))
(delete-file-if-present   (in-distribution-dir "Examples/Matching/.cvsignore"))

(specware::copy-directory (in-specware-dir     "UserDoc/examples/")
			  (in-distribution-dir "Examples/"))
(delete-dir-if-present    (in-distribution-dir "Examples/CVS"))
(delete-dir-if-present    (in-distribution-dir "Examples/simple1/CVS"))
(delete-file-if-present   (in-distribution-dir "Examples/simple1/test.lisp"))
(delete-dir-if-present    (in-distribution-dir "Examples/simple2/CVS"))
(delete-file-if-present   (in-distribution-dir "Examples/simple2/test.lisp"))
(delete-dir-if-present    (in-distribution-dir "Examples/simple2/Refs/CVS"))
(delete-dir-if-present    (in-distribution-dir "Examples/simple2/Specs/CVS"))
(delete-dir-if-present    (in-distribution-dir "Examples/simple3/CVS"))
(delete-file-if-present   (in-distribution-dir "Examples/simple3/test.lisp"))

;;; ============ DOCUMENTATION ============

(format t "~&;;;~%")
(format t "~&;;; Getting Documentation ...~%")

(specware::make-directory (in-distribution-dir "Documentation/"))

(specware::copy-file      (in-specware-dir     "UserDoc/language-manual/SpecwareLanguageManual.pdf")
		          (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(specware::copy-file      (in-specware-dir     "UserDoc/tutorial/SpecwareTutorial.pdf")
		          (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(specware::copy-file      (in-specware-dir     "UserDoc/user-manual/SpecwareUserManual.pdf")
		          (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
(specware::copy-file      (in-specware-dir     "UserDoc/cheat-sheet/QuickReference.pdf")
		          (in-distribution-dir "Documentation/Specware-QuickReference.pdf"))

;(specware::copy-file (in-specware-dir     "UserDoc/ReleaseNotes.txt")
;		      (in-distribution-dir "Documentation/ReleaseNotes.txt"))

;;; ============ RUNTIME C LIBRARY ============

(format t "~&;;;~%")
(format t "~&;;; Getting C library ...~%")
(specware::make-directory (in-distribution-dir "Languages/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/include/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/include/private/"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/cord"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/doc"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/Mac_files"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/tests"))
(specware::make-directory (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Examples"))

(with-open-file (s (in-specware-dir "Languages/MetaSlang/CodeGen/C/cgen-distribution-files"))
  (let ((eof (cons nil nil)))
    (do ((filename (read-line s nil eof) (read-line s nil eof)))
	((eq filename eof))
      (let ((filename (string-trim '(#\Space #\Tab) filename)))
	(unless (equalp filename "")
	  (specware::copy-file (in-specware-dir     filename) 
			       (in-distribution-dir filename)))))))

(let ((saw? nil)
      (in-file (in-distribution-dir "Languages/MetaSlang/CodeGen/C/Clib/gc6.2/Makefile"))
      (out-file (in-distribution-dir "temp")))
  (with-open-file (in in-file)
    (with-open-file (out out-file :direction :output)
      (let ((eof (cons nil nil)))
	(do ((line (read-line in nil eof) (read-line in nil eof)))
	    ((eq line eof))
	  (write-line (format nil "~A"
				  (cond ((equalp line "CC=cc $(ABI_FLAG)")
					 (setq saw? t)
					 "CC=gcc -w $(ABI_FLAG)")
					(t
					 line)))
		      out)))))
  (unless saw?
    (warn "Did not see \"CC=cc $(ABI_FLAG)\""))
  (delete-file in-file)
  (rename-file out-file in-file))

;;; ============ PATCHES ============

(format t "~&;;;~%")
(let ((patch-dir (in-distribution-dir "Patches/")))
  (format t "~&;;; Creating new patch directory : ~A~%" patch-dir)
  (specware::make-directory patch-dir))

(format t "~&;;;~%")

;;; ============ AUTORUN FILES FOR CD ============

(format t "~&;;;~%")
(format t "~&;;;     ===~%")
(format t "~&;;;~%")

;; Set up the directory that will hold the CD contents:
;;   C:/SpecwareReleases/Specware-4-1-4/CD/
;;
;; Put in the Autorun.inf file that will automatically invoke
;; Windows\setupwin32.exe for the user when the CD is inserted.
;;
;; Later the results from InstallShield will be put under
;;   C:/SpecwareReleases/Specware-4-1-4/CD/Windows/
;;   C:/SpecwareReleases/Specware-4-1-4/CD/Linux/
;;   C:/SpecwareReleases/Specware-4-1-4/CD/Mac/
;;   ...


(delete-dir-if-present *cd-dir*)
(sleep 1) ; avoid stupid race condition in Windows

(make-dir-if-missing *cd-dir*)

(format t "~&;;; Adding Autorun for Windows: ~A~%" (in-cd-dir "Autorun.inf"))
(specware::copy-file (in-specware-dir "Release/Autorun.inf")
		     (in-cd-dir "Autorun.inf"))

(format t "~&;;; Adding install script for Windows: ~A~%" (in-cd-dir "InstallOnWindows.cmd"))
(specware::copy-file (in-specware-dir "Release/InstallOnWindows.cmd")
		     (in-cd-dir "InstallOnWindows.cmd"))

(format t "~&;;; Adding install script for Linux: ~A~%" (in-cd-dir "InstallOnLinux"))
(specware::copy-file (in-specware-dir "Release/InstallOnLinux")
		     (in-cd-dir "InstallOnLinux"))

(format t "~&;;; Adding install script for Mac: ~A~%" (in-cd-dir "InstallOnMac"))
(specware::copy-file (in-specware-dir "Release/InstallOnMac")
		     (in-cd-dir "InstallOnMac"))

;;; ============ EMPTY DIRS TO RECEIVE INSTALLSHIELD RESULTS ============

(make-dir-if-missing (concatenate 'string *CD-dir* "Windows"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Linux"))
(make-dir-if-missing (concatenate 'string *CD-dir* "Mac"))

(format t "~&;;;~%")
(format t "~&;;;     ===~%")
(format t "~&;;;~%")
