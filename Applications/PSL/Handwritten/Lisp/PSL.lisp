(defpackage "SPECWARE")
(in-package "SPECWARE")

(declaim (optimize (speed 3) (debug 2) (safety 1)))

#+allegro
(setq comp:*cltl1-compile-file-toplevel-compatibility-p* t) ; default is WARN, which would be very noisy
#+cmu
(setq ext:*gc-verbose* nil)
#+cmu
(setq extensions:*bytes-consed-between-gcs* 10000000)
#+mcl
(egc t)                 ; Turn on ephemeral gc

;; Used in printing out the license and about-specware command
(defvar cl-user::Specware-version "4.0")
(defvar cl-user::Specware-version-name "Specware-4-0")
(defvar cl-user::Specware-patch-level "1")

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-0")

;; The following defines functions such as:
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory
(load (make-pathname
       :defaults "../../../Handwritten/Lisp/load-utilities"
       :type     "lisp"))

(defvar Specware4 (specware::getenv "SPECWARE4"))

(load (make-pathname
       :defaults (concatenate 'string Specware4
                              "/Provers/Snark/Handwritten/Lisp/snark-system")
       :type     "lisp"))

(snark:make-snark-system t)

(declaim (optimize (speed 3) (debug 2) (safety 1)))

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
    "Library/Base/Handwritten/Lisp/Char.lisp"
    "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Base/Handwritten/Lisp/System.lisp"
    "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsSTHarray.lisp"
    "Library/Structures/Data/Monad/Handwritten/Lisp/State.lisp"
    "Languages/XML/Handwritten/Lisp/Chars.lisp"  ; unicode predicates for XML
    "Languages/XML/Handwritten/Lisp/Magic.lisp"  ; escapes from metaslang type system
    )
  )

(map 'list #'(lambda (file)
           (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
     HandwrittenFiles
     )

(defpackage "UTILITIES")
(defpackage "MAP-SPEC")
(defpackage "ANNSPEC")
(defpackage "METASLANG")

#||
#+allegro
(progn (setf (get 'LIST-SPEC::|!exists|-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       ;(setf (get 'UTILITIES::occursT 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(nil t))
       (setf (get 'LIST-SPEC::|!map|-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'LIST-SPEC::filter-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'MAP-SPEC::foldi-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       ;(setf (get 'LIST-SPEC::foldl-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'ANNSPEC::foldriAQualifierMap-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE)
     '(t nil nil))
       (setf (get 'METASLANG::equallist? 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(nil nil t)))
||#

;; The following are specific to Specware and languages that
;; extend Specware. The order is significant: specware-state
;; must be loaded before the generated lisp file.
;;
;; The list below is used only in this file.

(defvar SpecwareRuntime
  '(
    ;; Functions that are assumed by the MetaSlang to Lisp compiler
    "Applications/Handwritten/Lisp/meta-slang-runtime"

    ;; XML support -- this provides hooks for reading/writing ad hoc structures
    ;; that are not grounded in normal base specs such as Boolean, Integer, etc.
    "Languages/XML/Handwritten/Lisp/AdHoc.lisp"

    ;; The generated lisp code.  This also initializes the Specware
    ;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
    "Applications/PSL/lisp/PSL.lisp"

    ;; XML support -- this calls code generated in Specware4.lisp for various XML definitions
    ;; maybe interface would be a better name
    "Languages/XML/Handwritten/Lisp/Support.lisp"

    ;; Toplevel aliases 
    "Applications/Specware/Handwritten/Lisp/toplevel"

    ;; Debugging utilities
    "Applications/Specware/Handwritten/Lisp/debug"

    ;; Test harness
    "Applications/Handwritten/Lisp/test-harness"
    )
  )

(defpackage "SNARK")

(map 'list #'(lambda (file)
           (list 33 file)
           (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
     SpecwareRuntime
     )

;; Load the parser library and the language specific parser files (grammar etc.)
(make-system (concatenate 'string
              Specware4 "/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))

(make-system (concatenate 'string
              Specware4 "/Languages/PSL/Parser/Handwritten/Lisp"))

;;; Initialization includes preloading the base spec.
(Specware::initializeSpecware-0)

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/PSL/PSL~2%")

(defun cl-user::boot ()
  (cl-user::sw "/Applications/PSL/PSL")
  )
