(defpackage "SPECWARE")
(in-package "SPECWARE")

#+allegro(setq comp:*cltl1-compile-file-toplevel-compatibility-p* t) ; default is WARN, which would be very noisy

(defvar Specware4 #+allegro(sys:getenv "SPECWARE4")
                  #+cmu (cdr (assoc :SPECWARE4 ext:*environment-list*))
		  )

;; Used in printing out the license and about-specware command
(defvar user::Specware-version "4.0")
(defvar user::Specware-version-name "Specware-4-0")
(defvar user::Specware-patch-level "1")

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-0")

;; The following defines functions such as:
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory
(load (make-pathname
       :defaults (concatenate 'string Specware4 "/Applications/Handwritten/Lisp/load-utilities")
       :type     "lisp"))

(load (make-pathname
       :defaults (concatenate 'string Specware4 "/Provers/Snark/Handwritten/Lisp/snark-system")
       :type     "lisp"))

;(snark:make-snark-system t)

;; Snark puts us in another package .. so we go back
(in-package "SPECWARE")

;; The following uses make-system from load-utilities above.
;; It defines goto-file-position, used by IO.lisp (and some chart-parsing code) below.
(make-system (concatenate 'string Specware4 "/Applications/Specware/UI/Emacs/Handwritten/Lisp"))

;; The following list should be generated automatically. That is, the
;; files listed below define functions that are declared in specs
;; used by Specware. Specware should generate the list of runtime files
;; needed by specs referenced in an application.
;;
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

(map 'list #'(lambda (file)
  (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
  HandwrittenFiles
)

;; The following are specific to Specware and languages that
;; extend Specware. The order is significant: specware-state
;; must be loaded before the generated lisp file.
;;
;; The list below is used only in this file.

(defvar SpecwareRuntime
  '(
     ;; Functions that are assumed by the MetaSlang to Lisp compiler
     "Applications/Handwritten/Lisp/meta-slang-runtime"

     ;; Functions for saving/restoring the Specware state to/from the lisp environment
     "Applications/Specware/Handwritten/Lisp/specware-state"

     ;; The generated lisp code.  This also initializes the Specware
     ;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
     "Applications/Specware/lisp/Specware4.lisp"

     ;; Toplevel aliases 
     "Applications/Specware/Handwritten/Lisp/toplevel"

     ;; Debugging utilities
     "Applications/Specware/Handwritten/Lisp/debug"
   )
)

(map 'list #'(lambda (file)
  (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
  SpecwareRuntime
)

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
