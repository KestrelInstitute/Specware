(defpackage "SPECWARE")
(defpackage "SPECCAT")
(in-package "SPECWARE")

(defvar Specware4 (sys:getenv "SPECWARE4"))

;; The following defines functions such as:
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory
(load (make-pathname
  :defaults
    (concatenate 'string Specware4 "/Applications/Handwritten/Lisp/load-utilities")
  :type "lisp"))

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
(compile-and-load-lisp-file (concatenate 'string
  Specware4 "/Applications/Specware/Handwritten/Lisp/specware-state"))

(defun SPECCAT::colimit-1 (x) (x))

;; Now load the generated lisp code.  
(compile-and-load-lisp-file "../../lisp/PSL.lisp")

;; Stephen's toplevel aliases 
(compile-and-load-lisp-file (concatenate 'string
  Specware4 "/Applications/Specware/Handwritten/Lisp/toplevel"))

;; Debugging utilities
(compile-and-load-lisp-file (concatenate 'string
  Specware4 "/Applications/Specware/Handwritten/Lisp/debug"))

(make-system (concatenate 'string
    Specware4 "/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))
(make-system (concatenate 'string
    Specware4 "/Languages/PSL/Parser/Handwritten/Lisp"))

(make-system "../../../Specware/UI/Emacs/Handwritten/Lisp")

(user::sw "/Library/Base")

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/PSL/PSL (but it probably won't work)~2%")
 
(defun user::boot ()
  (user::sw "/Applications/PSL/PSL")
)
