(defpackage :Specware (:use :cl))	; Most systems default to this but not sbcl until patch loaded below
(in-package :Specware)

(declaim (optimize (speed 3) (debug 2) (safety 1) #+cmu(c::brevity 3)))
;; (declaim (optimize (speed 0) (debug 3) (safety 3)))

(setq *load-verbose* nil)		; Don't print loaded file messages
(setq *compile-verbose* nil)		; or lisp compilation

#+allegro
(setq comp:*cltl1-compile-file-toplevel-compatibility-p* t) ; default is WARN, which would be very noisy
#+cmu
(setq ext:*gc-verbose* nil)
#+cmu
(setq extensions:*bytes-consed-between-gcs* (* 2 50331648))
#+sbcl
(setf (sb-ext:bytes-consed-between-gcs) 50331648)
#+cmu
(setq extensions:*efficiency-note-cost-threshold* 30)
#+sbcl
(setq sb-ext:*efficiency-note-cost-threshold* 30)
#+cmu
(setq c::*compile-print* nil)
#+sbcl
(setq sb-ext::*compile-print* nil)
#+sbcl
(declaim (optimize (sb-ext:inhibit-warnings 3)))
;#+mcl
;(egc t)					; Turn on ephemeral gc
#+mcl
(ccl::set-lisp-heap-gc-threshold (* 16777216 4))
#+sbcl
(setq sb-fasl:*fasl-file-type* "sfsl")	; Default is "fasl" which conflicts with allegro
#+sbcl
(setq sb-debug:*debug-beginner-help-p* nil)

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
(load (make-pathname :defaults "../../../Handwritten/Lisp/load-utilities"
		     :type     "lisp"))

(defvar Specware4 (specware::getenv "SPECWARE4"))

#+cmu
(compile-and-load-lisp-file (concatenate 'string
					 Specware4 "/Applications/Handwritten/Lisp/cmucl-patch"))
#+sbcl
(compile-and-load-lisp-file (concatenate 'string
					 Specware4 "/Applications/Handwritten/Lisp/sbcl-patch"))

(defun ignore-warning (condition)
   (declare (ignore condition))
   (muffle-warning))

(defpackage "SNARK")

(handler-bind ((warning #'ignore-warning))
  (load (make-pathname
	 :defaults (concatenate 'string Specware4
				"/Provers/Snark/Handwritten/Lisp/snark-system")
	 :type     "lisp")))

(handler-bind ((warning #'ignore-warning))
  (snark:make-snark-system t))

(declaim (optimize (speed 3) (debug 2) (safety 1)))
;; (declaim (optimize (speed 0) (debug 3) (safety 3)))

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
(progn (setf (get 'LIST-SPEC::exists-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       ;(setf (get 'UTILITIES::occursT 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(nil t))
       (setf (get 'LIST-SPEC::map-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'LIST-SPEC::filter-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'MAP-SPEC::foldi-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       ;(setf (get 'LIST-SPEC::foldl-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'ANNSPEC::foldriAQualifierMap-1-1-1 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE)
	 '(t nil nil))
       (setf (get 'METASLANG::equallist? 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(nil nil t)))
||#

;; The following are specific to Specware and languages that
;; extend Specware. 
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
    "Applications/Specware/lisp/Specware4.lisp"

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


;(handler-bind ((warning #'ignore-warning))
  (map 'list #'(lambda (file)
	       (list 33 file)
	       (compile-and-load-lisp-file (concatenate 'string Specware4 "/" file)))
     SpecwareRuntime
     );)

;; Load the parser library and the language specific parser files (grammar etc.)
(make-system (concatenate 'string
			  Specware4 "/Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))

(make-system (concatenate 'string
			  Specware4 "/Languages/SpecCalculus/Parser/Handwritten/Lisp"))

;;; Initialization includes preloading the base spec.
;;; (Specware::initializeSpecware-0) ; Now happens in startup actions (see bootstrap script)

#+allegro
(defun start-java-connection? ()
  (format t "Checking  command-line arguments: ~a~%" (system:command-line-arguments))
  (when (member "socket" (system:command-line-arguments)
		:test 'equal)
    (load (concatenate 'string
	    Specware4 "/Gui/src/Lisp/specware-socket-init"))))

#+allegro
(push 'start-java-connection? excl:*restart-actions*)

;;; Load base in correct location
#+allegro
(push  'Specware::initializeSpecware-0 cl-user::*restart-actions*)
#+cmu
(push  'Specware::initializeSpecware-0 ext:*after-save-initializations*)
#+mcl
(push  'Specware::initializeSpecware-0 ccl:*lisp-startup-functions*)
#+sbcl
(push  'Specware::initializeSpecware-0 sb-int:*after-save-initializations*)

;;; Set gc parameters at startup
#+mcl
(push  #'(lambda () (ccl::set-lisp-heap-gc-threshold (* 16777216 4)))
       ccl:*lisp-startup-functions*)

#+sbcl
(push  #'(lambda () (setq sb-debug:*debug-beginner-help-p* nil)
	            (setf (sb-ext:bytes-consed-between-gcs) 50331648))
       sb-int:*after-save-initializations*)

;;; Clear load environment vars
#+cmu
(progn (setq ext:*environment-list* ())
       (setq lisp::lisp-environment-list ()))


;;; Set temporaryDirectory
#+allegro
(push  'setTemporaryDirectory cl-user::*restart-actions*)

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/Specware/Specware4~2%")

(defun cl-user::boot ()
  (cl-user::sw "/Applications/Specware/Specware4")
  )
