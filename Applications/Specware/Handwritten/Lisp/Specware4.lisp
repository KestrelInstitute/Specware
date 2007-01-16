;;; This file is used to load the files for a specware image.
;;;
;;; (Do not confuse it with the file ../../lisp/Specware4.lisp
;;;  that is generated from .sw sources.)
;;;
;;; <Specware4>/Release/BuildScripts/LoadSpecware.lisp is a clone of this file
;;; that is used for distribution builds.

(defpackage "SPECWARE" (:use "CL"))   ; Most systems default to this but not sbcl until patch loaded below
(in-package "SPECWARE")

(declaim (optimize (speed 3) (debug #+sbcl 3 #-sbcl 2) (safety 1) #+cmu(c::brevity 3)))

(setq *load-verbose* nil)		; Don't print loaded file messages
(setq *compile-verbose* nil)		; or lisp compilation

#+allegro (progn
	    (setq comp:*cltl1-compile-file-toplevel-compatibility-p* t) ; default is WARN, which would be very noisy
	    (setq excl:*record-source-file-info* nil)                   ; workaround for annoying bug
	    ;; make sure various modules are loaded for swank:
	    (require :scm)                                              ; ???
	    ;; "efmacs" seems to stand for something like "external format macros"
	    ;; its used by xml, mime, etc.
	    (cl-user::eol-convention *standard-output*)                 ; loads efmacs.fasl
	    (require :inspect)
	    (require :streama)
	    )

#+cmu     (progn
	    (setq ext:*gc-verbose* nil)
	    (setq extensions:*bytes-consed-between-gcs* (* 2 50331648))
	    (setq extensions:*efficiency-note-cost-threshold* 30)
	    (setq c::*compile-print* nil)
	    )

#+sbcl    (progn
	    (setf (sb-ext:bytes-consed-between-gcs) 50331648)
	    (setq sb-ext:*efficiency-note-cost-threshold* 30)
	    (declaim (sb-ext:muffle-conditions sb-ext:compiler-note
					       sb-int:simple-style-warning
					       sb-int:package-at-variance))
	    (setq sb-ext::*compile-print* nil)
	    (declaim (optimize (sb-ext:inhibit-warnings 3)))
	    (setq sb-fasl:*fasl-file-type* "sfsl")	                ; Default is "fasl" which conflicts with allegro
	    (setq sb-debug:*debug-beginner-help-p* nil)

	    #+windows
	    ;; Preload for efficiency and flexibility
	    (eval-when (:compile-toplevel :load-toplevel :execute)
	      (require 'sb-bsd-sockets)
	      (require 'sb-introspect)
	      (require 'sb-posix))

	    (setq sb-debug:*debug-beginner-help-p* nil)
	    )

#+mcl     (progn
	    (ccl:egc nil)		                                ; Turn off ephemeral gc as it is inefficient
	    (ccl:gc-retain-pages t)	                                ; Don't give up pages after gc as likely to need them soon
	    (ccl::set-lisp-heap-gc-threshold (* 16777216 3))            ; Increase free space after a gc
	    )

;; Used in printing out the license and about-specware command
(defvar cl-user::Specware-version "4.2.0")
(defvar cl-user::Specware-version-name "Specware-4-2")
(defvar cl-user::Specware-patch-level "0")

;; Used in patch detection and about-specware command
(defvar Major-Version-String "4-2")

;; The following defines functions such as:
;;;   specware::getenv
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory

(let ((utils (make-pathname :defaults "../../../Handwritten/Lisp/load-utilities" :type "lisp")))
  (load utils)
  (compile-and-load-lisp-file utils))

(defparameter Specware4 (specware::getenv "SPECWARE4"))

(defparameter *Specware-dir*
    (let ((dir (substitute #\/ #\\ Specware4)))
      (if (eq (schar dir (1- (length dir))) #\/)
	  dir
	(concatenate 'string dir "/"))))

(defun in-specware-dir (file) (concatenate 'string *Specware-dir* file))

#+cmu
(compile-and-load-lisp-file (in-specware-dir "Applications/Handwritten/Lisp/cmucl-patch"))
#+sbcl
(compile-and-load-lisp-file (in-specware-dir "Applications/Handwritten/Lisp/sbcl-patch"))

(defun ignore-warning (condition)
   (declare (ignore condition))
   (muffle-warning))

(handler-bind ((warning #'ignore-warning))
  (load (make-pathname
         :defaults (in-specware-dir "Provers/Snark/Handwritten/Lisp/snark-system")
         :type     "lisp")))

(format t "Loading Snark.")
(handler-bind ((warning #'ignore-warning))
  (cl-user::make-or-load-snark-system))
(format t "~%Finished loading Snark.")
(finish-output t)

(declaim (optimize (speed 3) (debug #+sbcl 3 #-sbcl 2) (safety 1)))

;; Snark puts us in another package .. so we go back
(in-package "SPECWARE")

;; The following uses make-system from load-utilities above.
;; It defines goto-file-position, used by IO.lisp (and some chart-parsing code) below.
(make-system (in-specware-dir "Applications/Specware/UI/Emacs/Handwritten/Lisp"))

;; We need to preload the (artificial to Allegro) :emacs-mule external 
;; character format.
;; Otherwise, Specware distribution images created by generate-application 
;; (see BuildDistribution_ACL.lisp) will complain at startup that :emacs-mule
;; cannot be found.
#+Allegro (excl::find-external-format :emacs-mule)

;; The following list should be generated automatically. That is, the
;; files listed below define functions that are declared in specs
;; used by Specware. Specware should generate the list of runtime files
;; needed by specs referenced in an application.
;;
;; The list is used only in this file.
;;; ---------------
(defvar HandwrittenFiles
  '(
    ; "Library/Base/Handwritten/Lisp/Boolean.lisp"
    "Library/Base/Handwritten/Lisp/Integer.lisp"
    "Library/Base/Handwritten/Lisp/Nat.lisp"
    "Library/Base/Handwritten/Lisp/Char.lisp"
    "Library/Base/Handwritten/Lisp/System.lisp"
    "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Unvetted/Handwritten/Lisp/Double.lisp"
    "Library/Unvetted/Handwritten/Lisp/Complex.lisp"
    "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
    "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsSTHarray.lisp"
    ;"Library/Structures/Data/Sets/Handwritten/Lisp/SetAsCachedHArray.lisp"
    "Library/Structures/Data/Sets/Handwritten/Lisp/SetAsSTHarray.lisp"
    "Library/Structures/Data/Monad/Handwritten/Lisp/State.lisp"
    "Languages/XML/Handwritten/Lisp/Chars.lisp"  ; unicode predicates for XML
    "Languages/XML/Handwritten/Lisp/Magic.lisp"  ; escapes from metaslang type system
    "Provers/DP/Handwritten/Lisp/Rational.lisp"
    )
  )

(map 'list #'(lambda (file) (compile-and-load-lisp-file (in-specware-dir file)))
     HandwrittenFiles
     )

(defpackage "UTILITIES")
(defpackage "MAP-SPEC")
(defpackage "ANNSPEC")
(defpackage "METASLANG")
(defpackage :TypeChecker)

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


(defpackage "PROVER")
(defvar prover::wildCounter 0) ; to suppress annoying compiler warning

;; The following are specific to Specware and languages that
;; extend Specware. The order is significant: specware-state
;; must be loaded before the generated lisp file.
;;
;; The list below is used only in this file.

(defvar SpecwareRuntime
  '(
    ;; Functions that are assumed by the MetaSlang to Lisp compiler
    "Library/SpecwareRuntime"

    ;; XML support -- this provides hooks for reading/writing ad hoc structures
    ;; that are not grounded in normal base specs such as Boolean, Integer, etc.
    "Languages/XML/Handwritten/Lisp/AdHoc.lisp"

    ;; Preface.lisp defines misc things called by Specware4.lisp code, 
    ;; so that compiling Specware4.lisp won't genereate compiler warnings.
    "Applications/Specware/Handwritten/Lisp/Preface.lisp"

    ;; The generated lisp code.  This also initializes the Specware
    ;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
    "Applications/Specware/lisp/Specware4.lisp"

    ;; XML support -- this calls code generated in Specware4.lisp for various XML definitions
    ;; maybe interface would be a better name
    "Languages/XML/Handwritten/Lisp/Support.lisp"

    ;; Toplevel commands 
    "Applications/Specware/Handwritten/Lisp/toplevel"

    ;; Debugging utilities
    "Applications/Specware/Handwritten/Lisp/debug"

    ;; Specware Shell
    "Applications/Specware/Handwritten/Lisp/sw-shell"

    ;; Test harness
    "Applications/Handwritten/Lisp/test-harness"

    ;; XML-RPC
    "Library/IO/XmlRpc/s-xml/package"
    "Library/IO/XmlRpc/s-xml/xml"
    "Library/IO/XmlRpc/s-xml-rpc/base64"
    "Library/IO/XmlRpc/s-xml-rpc/package"
    "Library/IO/XmlRpc/s-xml-rpc/sysdeps"
    "Library/IO/XmlRpc/s-xml-rpc/xml-rpc"
    "Library/IO/XmlRpc/s-xml-rpc/extensions"
    "Library/IO/XmlRpc/load-xml-rpc"

    )
  )

;(handler-bind ((warning #'ignore-warning))
  (map 'list #'(lambda (file)
		 (compile-and-load-lisp-file (in-specware-dir file)))
       SpecwareRuntime
       );)

;; Load the parser library and the language specific parser files (grammar etc.)
(make-system (in-specware-dir "Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))

(make-system (in-specware-dir "Languages/SpecCalculus/Parser/Handwritten/Lisp"))

;;; Initialization includes preloading the base spec.
;;; (Specware::initializeSpecware-0) ; Now happens in startup actions (see bootstrap script)

#+allegro
(defun start-java-connection? ()
  (format t "Checking  command-line arguments: ~a~%" (system:command-line-arguments))
  (when (member "socket" (system:command-line-arguments)
		:test 'equal)
    (load (in-specware-dir "Gui/src/Lisp/specware-socket-init"))))

#+allegro
(push 'start-java-connection? excl:*restart-actions*)

;;; Load base in correct location at startup
(push  'Specware::initializeSpecware-0 
       #+allegro cl-user::*restart-actions*
       #+cmu     ext:*after-save-initializations*
       #+mcl     ccl:*lisp-startup-functions*
       #+sbcl    sb-ext:*init-hooks*)

;(Specware::initializeSpecware-0)

#+sbcl
(defvar *sbcl-home* (specware::getenv "SBCL_HOME"))
#+sbcl
(push  #'(lambda () (setq sb-debug:*debug-beginner-help-p* nil)
	            (setf (sb-ext:bytes-consed-between-gcs) 50331648)
		    (specware::setenv "SBCL_HOME" *sbcl-home*)
		    )
       sb-ext:*init-hooks*)

;;; Set temporaryDirectory at startup
(push 'setTemporaryDirectory 
      #+allegro cl-user::*restart-actions*
      #+cmu     ext:*after-save-initializations*
      #+mcl     ccl:*lisp-startup-functions*
      #+sbcl    sb-ext:*init-hooks*)

(defvar *using-slime-interface?* t)
(when *using-slime-interface?*
  ;; Preload slime lisp support

  ;; per instructions in swank-loader.lisp
  (cl:defpackage :swank-loader
		 (:use :cl)
		 (:export :load-swank 
			  :*source-directory*
			  :*fasl-directory*))
  )
;; Repeat the when test so the defparameter below can 
;; be read after the defpackage above has been evaluted.
(when *using-slime-interface?*
  (defparameter SWANK-LOADER::*FASL-DIRECTORY*
    (format nil "~a/Library/IO/Emacs/slime/" 
	    (specware::getenv "SPECWARE4")))

  (let ((loader (in-specware-dir "Library/IO/Emacs/slime/swank-loader.lisp")))
    (load loader :verbose t)))
(setq *using-slime-interface?* nil)	; Gets set to t when initialized

(format t "~2%To bootstrap, run (boot)~%")
(format t "~%That will run :sw /Applications/Specware/Specware4~2%")

;;;#+allegro
;;;(excl:without-package-locks
;;; (setf (symbol-function 'TPL:TOP-LEVEL-READ-EVAL-PRINT-LOOP)
;;;   #'swshell::specware-shell0))

(defun cl-user::boot ()
  (let ((val (cl-user::swl "/Applications/Specware/Specware4")))
    (unless val
      (funcall (intern "EVAL-IN-EMACS" "EMACS")
	       "(delete-continuation)"))
    val)
  )

(declaim (optimize (speed 2) (debug 3) (safety 2)))
