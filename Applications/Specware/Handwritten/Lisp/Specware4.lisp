(defpackage "SPECWARE")
(in-package "SPECWARE")

(defvar Specware4 (sys:getenv "SPECWARE4"))

;; The following defines functions such as:
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory
(load (make-pathname
       :defaults (concatenate 'string Specware4 "/Applications/Handwritten/Lisp/load-utilities")
       :type     "lisp"))

;; The following uses make-system from load-utilities above.
;; It defines goto-file-position, used by IO.lisp (and some chart-parsing code) below.
(make-system "../../UI/Emacs/Handwritten/Lisp") 

;; The following list should be generated automatically!
;; The list is used only in this file.
;;; ---------------
(defvar HandwrittenFiles
  '(
    "Library/Base/Handwritten/Lisp/Boolean.lisp"
    "Library/Base/Handwritten/Lisp/Integer.lisp"
    "Library/Base/Handwritten/Lisp/Nat.lisp"
    "Library/Base/Handwritten/Lisp/Char.lisp"
    "Library/Base/Handwritten/Lisp/List.lisp"
    "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Base/Handwritten/Lisp/Option.lisp"
    "Library/Base/Handwritten/Lisp/System.lisp"
    "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
    )
  )

;; This loads functions that are assumed by the MetaSlang to Lisp compiler
(compile-and-load-lisp-file (concatenate 'string
  Specware4 "/Applications/Handwritten/Lisp/meta-slang-runtime"))

(map 'list #'(lambda (file)
  (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
  HandwrittenFiles
)

;; Define functions for saving/restoring the
;; Specware state to/from the lisp environment
(compile-and-load-lisp-file "specware-state")

;; Now load the generated lisp code.  This also initializes the Specware
;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
(compile-and-load-lisp-file "../../lisp/Specware4.lisp")

;; Stephen's Toplevel aliases 
(compile-and-load-lisp-file "toplevel")

;; Debugging utilities
(compile-and-load-lisp-file "debug")

;; Load the parser library and the language specific parser files (grammar etc.)
(make-system (concatenate 'string
			  Specware4 "/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))
(make-system (concatenate 'string
			  Specware4 "/Languages/SpecCalculus/Parser/Handwritten/Lisp"))

;;; Preload the base specs
(user::sw "/Library/Base")

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/Specware/Specware4~2%")

(defun user::boot ()
  (user::sw "/Applications/Specware/Specware4")
  )
