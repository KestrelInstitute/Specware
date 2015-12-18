;;; Loaded from BuildDistribution_{$LISP}.lisp 
;;; Moves a variety of files to the distribution directory.

;;; Assumes distribution dir is something like:
;;;   C:/SpecwareReleases/Specware-4-2-2/Windows/Specware4
;;;   Also assumes the directory contains only stuff that
;;    generate-application has just placed in it.

(defpackage :Distribution (:use :common-lisp))
(in-package :Distribution)

;;; ============ SPECWARE LIBRARY  ============

(format t "~&~%")
(format t "~&;;; Getting Specware library ...~%")

;;; Copy needed directories to distribution
;;; Flushes CVS sub-directories and .cvsignore files

(Specware::make-directory (in-distribution-dir "Library/"))
(copy-dist-directory (in-specware-dir     "Library/Base/")
                     (in-distribution-dir "Library/Base/"))
(delete-file-if-present   (in-distribution-dir "Library/Base/Handwritten/Lisp/.cvsignore"))

(copy-dist-directory (in-specware-dir     "Library/ProverBase/")
                     (in-distribution-dir "Library/ProverBase/"))

(copy-dist-file      (in-specware-dir     "Library/Base.sw")
                     (in-distribution-dir "Library/Base.sw"))
(copy-dist-file      (in-specware-dir     "Library/InterpreterBase.sw")
                     (in-distribution-dir "Library/InterpreterBase.sw"))
(copy-dist-file      (in-specware-dir     "Library/General.sw")
                     (in-distribution-dir "Library/General.sw"))

(Specware::make-directory (in-distribution-dir "Library/IO/"))
(copy-dist-directory (in-specware-dir     "Library/IO/Emacs/")
                     (in-distribution-dir "Library/IO/Emacs/"))
(delete-dir-if-present (in-distribution-dir "Library/IO/Emacs/ilisp/"))

(copy-dist-directory (in-specware-dir     "Library/General/")
                     (in-distribution-dir "Library/General/"))
(delete-dir-if-present (in-distribution-dir "Library/General/Isa/"))
(copy-dist-file (in-specware-dir     "Library/Structures/Data/Monad.sw")
                (in-distribution-dir "Library/General/Monad.sw"))

(Specware::concatenate-files
   (loop for fil in '("Base/Handwritten/Lisp/Integer"
; 		      "Base/Handwritten/Lisp/Nat"
		      "Base/Handwritten/Lisp/Character"
		      "Base/Handwritten/Lisp/String"
		      "Legacy/Utilities/Handwritten/Lisp/System"
		      "IO/Primitive/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/State"
		      "Legacy/Utilities/Handwritten/Lisp/IO"
		      "Legacy/Utilities/Handwritten/Lisp/Lisp"
		      "Structures/Data/Monad/Handwritten/Lisp/State"
		      "../Applications/Handwritten/Lisp/meta-slang-runtime"
		      "../Applications/Specware/Handwritten/Lisp/ProvideSpecwareRuntime")
      collect (in-specware-dir (format nil "Library/~a.lisp" fil)))
   (in-distribution-dir "Library/SpecwareRuntime.lisp"))

;;; ============ EXAMPLES ============

(format t "~&;;;~%")
(format t "~&;;; Getting Examples ...~%")

(Specware::make-directory (in-distribution-dir "Examples/"))
(copy-dist-directory (in-specware-dir     "UserDoc/tutorial/example/")
                     (in-distribution-dir "Examples/Matching/"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/Snark"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/Isa"))
(delete-dir-if-present    (in-distribution-dir "Examples/Matching/asw"))
(delete-file-if-present   (in-distribution-dir "Examples/Matching/.cvsignore"))
(delete-file-if-present   (in-distribution-dir "Examples/Matching/MatchingRichard.sw"))
(delete-file-if-present   (in-distribution-dir "Examples/Matching/MatchingRichardTheorems.sw"))

(copy-dist-directory (in-specware-dir     "UserDoc/examples/")
                     (in-distribution-dir "Examples/"))
(delete-file-if-present   (in-distribution-dir "Examples/simple1/test.lisp"))
(delete-file-if-present   (in-distribution-dir "Examples/simple2/test.lisp"))
(delete-file-if-present   (in-distribution-dir "Examples/simple3/test.lisp"))

;;; ============ DOCUMENTATION ============

(format t "~&;;;~%")
(format t "~&;;; Getting Documentation ...~%")

(Specware::make-directory (in-distribution-dir "Documentation/"))

(copy-dist-file      (in-specware-dir     "UserDoc/language-manual/SpecwareLanguageManual.pdf")
                     (in-distribution-dir "Documentation/SpecwareLanguageManual.pdf"))
(copy-dist-file      (in-specware-dir     "UserDoc/tutorial/SpecwareTutorial.pdf")
                     (in-distribution-dir "Documentation/SpecwareTutorial.pdf"))
(copy-dist-file      (in-specware-dir     "UserDoc/user-manual/SpecwareUserManual.pdf")
                     (in-distribution-dir "Documentation/SpecwareUserManual.pdf"))
(copy-dist-file      (in-specware-dir     "UserDoc/cheat-sheet/QuickReference.pdf")
                     (in-distribution-dir "Documentation/Specware-QuickReference.pdf"))

;(copy-dist-file (in-specware-dir     "UserDoc/ReleaseNotes.txt")
;		      (in-distribution-dir "Documentation/ReleaseNotes.txt"))


;;; ============ Start-up Scripts & Binary ============

#+(and sbcl darwin)
(progn
  (format t "~&;;;~%")
  (format t "~&;;; Getting Specware Start-up Scripts % Binary ...~%")

  (copy-dist-file (in-specware-dir "Release/Mac/sbcl/Specware")
                  (in-distribution-dir "Specware.terminal"))
  (copy-dist-directory (in-specware-dir "Release/Mac/sbcl/Specware.app/")
                       (in-distribution-dir "Specware.app/"))
  (copy-dist-file (in-specware-dir "Release/Mac/sbcl/SpecwareShell.sh")
                  (in-distribution-dir "SpecwareShell.sh"))
  (copy-dist-file (in-specware-dir "Applications/Specware/bin/unix/Specware4.sbclexe")
                  (in-distribution-dir "Specware4.sbclexe"))
  )
#+(and sbcl linux)
(progn
  (format t "~&;;;~%")
  (format t "~&;;; Getting Specware Start-up Scripts % Binary ...~%")

  (copy-dist-file (in-specware-dir "Release/Linux/SBCL/Specware")
                  (in-distribution-dir "Specware"))
  (copy-dist-file (in-specware-dir "Release/Linux/SBCL/SpecwareShell")
                  (in-distribution-dir "SpecwareShell"))
  (copy-dist-file (in-specware-dir "Release/Linux/SBCL/Find_Specware_App_SBCL")
                  (in-distribution-dir "Find_Specware_App_SBCL"))
  (copy-dist-file (in-specware-dir "Applications/Specware/bin/unix/Specware4.sbclexe")
                  (in-distribution-dir "Specware4.sbclexe"))
;  (copy-dist-file (in-specware-dir "Release/Linux/install_gnome_desktop_icons_specware")
;                  (in-distribution-dir "install_gnome_desktop_icons_specware"))
  (copy-dist-file (in-specware-dir "Release/Linux/Find_SPECWARE4")
                  (in-distribution-dir "Find_SPECWARE4"))
  (copy-dist-file (in-specware-dir "Release/Linux/Find_XEMACS")
                  (in-distribution-dir "Find_XEMACS"))
  (copy-dist-file (in-specware-dir "Release/Linux/Update_Path")
                  (in-distribution-dir "Update_Path"))
  (copy-dist-file (in-specware-dir "Release/Linux/Update_SWPATH")
                  (in-distribution-dir "Update_SWPATH")))

;; ;;; ============ RUNTIME C LIBRARY ============

;; (format t "~&;;;~%")
;; (format t "~&;;; Getting C library ...~%")
;; (Specware::make-directory (in-distribution-dir "Library/Clib/"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/include/"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/include/private/"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/cord"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/doc"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/Mac_files"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/gc6.6/tests"))
;; (Specware::make-directory (in-distribution-dir "Library/Clib/Examples"))

;; (with-open-file (s (in-specware-dir "Library/Clib/cgen-distribution-files"))
;;   (let ((eof (cons nil nil)))
;;     (do ((filename (read-line s nil eof) (read-line s nil eof)))
;; 	((eq filename eof))
;;       (let ((filename (string-trim '(#\Space #\Tab) filename)))
;; 	(unless (equalp filename "")
;; 	  (let ((filename (format nil "Library/Clib/~a" filename)))
;; 	    (copy-dist-file (in-specware-dir     filename) 
;;                             (in-distribution-dir filename))))))))

;; (let ((saw? nil)
;;       (in-file  (in-distribution-dir "Library/Clib/gc6.6/Makefile"))
;;       (out-file (in-distribution-dir "temp")))
;;   (with-open-file (in in-file)
;;     (with-open-file (out out-file :direction :output)
;;       (let ((eof (cons nil nil)))
;; 	(do ((line (read-line in nil eof) (read-line in nil eof)))
;; 	    ((eq line eof))
;; 	  (write-line (format nil "~A"
;; 				  (cond ((equalp line "CC=cc $(ABI_FLAG)")
;; 					 (setq saw? t)
;; 					 "CC=gcc -w $(ABI_FLAG)")
;; 					(t
;; 					 line)))
;; 		      out)))))
;;   (unless saw?
;;     (warn "Did not see \"CC=cc $(ABI_FLAG)\""))
;;   (delete-file in-file)
;;   (rename-file out-file in-file))

;;; ============ PATCHES ============

(format t "~&;;;~%")
(let ((patch-dir (in-distribution-dir "Patches/")))
  (format t "~&;;; Creating new patch directory : ~A~%" patch-dir)
  (Specware::make-directory patch-dir))

(format t "~&;;;~%")
(format t "~&;;;     ===~%")
(format t "~&;;;~%")
