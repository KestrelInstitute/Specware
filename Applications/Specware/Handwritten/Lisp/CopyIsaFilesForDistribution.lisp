;;; Loaded from BuildDistribution_{$LISP}.lisp 
;;; Moves a variety of files to the distribution directory.

;;; Assumes distribution dir is something like:
;;;   C:/SpecwareReleases/Specware-4-1-5/Windows/Specware4
;;;   Also assumes the directory contains only stuff that
;;    generate-application has just placed in it.

(in-package :cl-user)

;;; ============ SPECWARE LIBRARY  ============

(format t "~&~%")
(format t "~&;;; Getting Isabelle Interface library files ...~%")

(specware::copy-directory (in-specware-dir     "Library/Isa/")
			  (in-distribution-dir "Library/Isa/"))
(delete-dir-if-present    (in-distribution-dir "Library/Isa/CVS/"))


;;; ============ EXAMPLES ============

(format t "~&;;;~%")
(format t "~&;;; Getting Isabelle Interface Examples ...~%")
(specware::copy-directory (in-specware-dir     "UserDoc/isabelle-interface/example/")
			  (in-distribution-dir "Examples/IsabelleInterface/"))
(delete-dir-if-present    (in-distribution-dir "Examples/IsabelleInterface/CVS"))
(delete-dir-if-present    (in-distribution-dir "Examples/IsabelleInterface/Isa"))

;;; ============ DOCUMENTATION ============

(format t "~&;;;~%")
(format t "~&;;; Getting Isabelle Interface Documentation ...~%")

(specware::copy-file      (in-specware-dir     "UserDoc/isabelle-interface/SpecwareIsabelleInterface.pdf")
		          (in-distribution-dir "Documentation/SpecwareIsabelleInterface.pdf"))

;;; ============ Start-up Scripts ============
#+darwin
(progn
  (format t "~&;;;~%")
  (format t "~&;;; Getting Isabelle Specware Start-up Scripts ...~%")

  (specware::copy-file (in-specware-dir "Release/Mac/SBCL/Isabelle_Specware")
		       (in-distribution-dir "Isabelle_Specware.terminal"))
  (specware::copy-file (in-specware-dir "Release/Mac/SBCL/XEmacs_Specware")
		       (in-distribution-dir "XEmacs_Specware"))
  )