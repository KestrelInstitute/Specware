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
(format t "~&;;; Getting Isabelle Interface library files ...~%")

(copy-dist-directory (in-specware-dir     "Library/Isa/")
			  (in-distribution-dir "Library/Isa/"))


;;; ============ EXAMPLES ============

(format t "~&;;;~%")
(format t "~&;;; Getting Isabelle Interface Examples ...~%")
(copy-dist-directory (in-specware-dir     "UserDoc/isabelle-interface/example/")
                     (in-distribution-dir "Examples/IsabelleInterface/"))
(delete-dir-if-present (in-distribution-dir "Examples/IsabelleInterface/Isa"))

;;; ============ DOCUMENTATION ============

(format t "~&;;;~%")
(format t "~&;;; Getting Isabelle Interface Documentation ...~%")

(copy-dist-file (in-specware-dir     "UserDoc/isabelle-interface/SpecwareIsabelleInterface.pdf")
                (in-distribution-dir "Documentation/SpecwareIsabelleInterface.pdf"))

;;; ============ Start-up Scripts ============
#+darwin
(progn
  (format t "~&;;;~%")
  (format t "~&;;; Getting Isabelle Specware Start-up Scripts ...~%")

  (copy-dist-file (in-specware-dir "Release/Mac/sbcl/Isabelle_Specware")
                  (in-distribution-dir "Isabelle_Specware.terminal"))
  (copy-dist-directory (in-specware-dir "Release/Mac/sbcl/Isabelle_Specware.app/")
                       (in-distribution-dir "Isabelle_Specware.app/"))
  (copy-dist-file (in-specware-dir "Release/Mac/sbcl/XEmacs_Specware")
                  (in-distribution-dir "XEmacs_Specware"))
  )
#+linux
(progn
  (format t "~&;;;~%")
  (format t "~&;;; Getting Isabelle Specware Start-up Scripts ...~%")

  (copy-dist-file (in-specware-dir "Release/Linux/SBCL/Isabelle_Specware")
                  (in-distribution-dir "Isabelle_Specware"))
  (copy-dist-file (in-specware-dir "Release/Linux/SBCL/XEmacs_Specware")
                  (in-distribution-dir "XEmacs_Specware"))
  )