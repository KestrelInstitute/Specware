;;; This file is used to load the files for a specware image.
;;;
;;; (Do not confuse it with the file ../../lisp/Specware4.lisp
;;;  that is generated from .sw sources.)
;;;
;;; <Specware4>/Release/BuildScripts/LoadSpecware.lisp is a clone of this file
;;; that is used for distribution builds.

;(push :case-sensitive *features*)
#+case-sensitive
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun set-readtable-invert ()
    (setq *readtable* (copy-readtable *readtable*))
    (setf (readtable-case *readtable*) :invert))
  (set-readtable-invert))

(defpackage :SpecToLisp)
(defpackage :Specware (:use :cl)   ; Most systems default to this but not sbcl until patch loaded below
  #+case-sensitive
  (:nicknames :specware))
(in-package :Specware)

#+case-sensitive
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun set-readtable-invert ()
    (setq *readtable* (copy-readtable *readtable*))
    (setf (readtable-case *readtable*) :invert)))

(defvar SpecToLisp::SuppressGeneratedDefuns nil) ;; note: defvar does not redefine if var already has a value

(declaim (optimize (speed 3) (debug #+sbcl 2 #-sbcl 3) (safety 1) #+cmu(c::brevity 3)))

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
            ; (setq sb-ext:*derive-function-types* t) ; test
	    ; (setf (sb-ext:bytes-consed-between-gcs) 50331648)
	    (setq sb-ext:*efficiency-note-cost-threshold* 30)
	    (declaim (sb-ext:muffle-conditions sb-ext:compiler-note
					       sb-int:simple-style-warning
					       sb-int:package-at-variance))
            ;; (defun lgen-lisp-redefinition-warning (warning)
            ;;   (and (typep warning 'sb-kernel::redefinition-with-defun)
            ;;        (let* ((new-location (sb-kernel::redefinition-warning-new-location warning))
            ;;               (new-namestring (and new-location
            ;;                                    (sb-c:definition-source-location-namestring new-location))))
            ;;          (string= new-namestring "lgen_lisp_tmp.lisp"
            ;;                   :start1 (- (length new-namestring) (length "lgen_lisp_tmp.lisp")))
            ;;          )))
            (deftype sw-uninteresting-redefinition ()
              '(or (satisfies sb-kernel::uninteresting-ordinary-function-redefinition-p)
                (satisfies sb-kernel::uninteresting-macro-redefinition-p)
                (satisfies sb-kernel::uninteresting-generic-function-redefinition-p)
                (satisfies sb-kernel::uninteresting-method-redefinition-p)
                ;;(satisfies lgen-lisp-redefinition-warning)
                sb-int:package-at-variance
                ))

            (setq sb-ext:*muffled-warnings* 'sw-uninteresting-redefinition)
	    (setq sb-ext::*compile-print* nil)
	    (declaim (optimize (sb-ext:inhibit-warnings 3)))
	    (setq sb-fasl:*fasl-file-type* "sfsl")	                ; Default is "fasl" which conflicts with allegro
	    (setq sb-debug:*debug-beginner-help-p* nil)

	    ;; Preload for efficiency and flexibility
	    (eval-when (:compile-toplevel :load-toplevel :execute)
	      (let ((sb-fasl:*fasl-file-type* "fasl"))
                ;; The following four lines load hunchentoot and supercede the next four requires
                ;; (load "quicklisp")
                ;; (load "/Users/westfold/quicklisp/setup.lisp")
                ;; (pushnew :hunchentoot-no-ssl *features*)
                ;; (funcall (find-symbol "QUICKLOAD" :ql) "hunchentoot")

		(require :sb-bsd-sockets)
		(require :sb-introspect)
		(require :sb-posix)
                (require :sb-cltl2)
                ;; :sb-sprof may need to be removed if running on windows
		#-win32 (require :sb-sprof)
                (require :asdf)
                (require :sb-grovel)
                ))

	    (setq sb-debug:*debug-beginner-help-p* nil)
	    ;; Temporary because of race condition bug with slime
            ;; (setq *features* (remove :sb-thread *features*))
            )

#+mcl     (progn
	    (ccl:egc nil)		                                ; Turn off ephemeral gc as it is inefficient
	    (ccl:gc-retain-pages t)	                                ; Don't give up pages after gc as likely to need them soon
	    (ccl::set-lisp-heap-gc-threshold (* 16777216 3))            ; Increase free space after a gc
	    )

;; The following defines functions such as:
;;;   Specware::getenv
;;    compile-and-load-lisp-file
;;    load-lisp-file
;;    make-system
;;    change-directory
;;    current-directory

(let ((utils (make-pathname :defaults "../../../Handwritten/Lisp/load-utilities"
                            :type "lisp"))
      (utils_fasl (make-pathname :defaults "../../../Handwritten/Lisp/load-utilities"
                                 :type sb-fasl:*fasl-file-type*)))
  (if (probe-file utils_fasl)
      (load utils_fasl)
    (load utils))
  (when (compile-file-if-needed utils)
    (format t "Recompiling load-utilities\n")
    (load utils_fasl)))

(defparameter Specware4 (substitute #\/ #\\ (convert-pathname-from-cygwin (getenv "SPECWARE4"))))

(if (null Specware::Specware4)
    (warn "SPECWARE4 environment var not set")
  (format t "~&SPECWARE4 = ~S~%" Specware::Specware4))

(defparameter *Specware-dir*
    (let ((dir (substitute #\/ #\\ Specware4)))
      (if (eq (schar dir (1- (length dir))) #\/)
	  dir
	(concatenate 'string dir "/"))))

(defun in-specware-dir (file) (concatenate 'string *Specware-dir* file))

;;; Get version information from canonical source...
(let ((version-file (in-specware-dir "Applications/Specware/Handwritten/Lisp/SpecwareVersion.lisp")))
  (if (probe-file version-file)
      (load version-file)
    (error "in LoadSpecware.lisp:  Cannot find ~A" version-file)))

#+cmu
(compile-and-load-lisp-file (in-specware-dir "Applications/Handwritten/Lisp/cmucl-patch"))
#+sbcl
(compile-and-load-lisp-file (in-specware-dir "Applications/Handwritten/Lisp/sbcl-patch"))

(defun ignore-warning (condition)
   (declare (ignore condition))
   (muffle-warning))

;; (let ((*readtable* (copy-readtable nil)))
;;   (handler-bind ((warning #'ignore-warning))
;;     (load (make-pathname
;;            :defaults (in-specware-dir "Provers/Snark/Handwritten/Lisp/snark-system")
;;            :type     "lisp")))
;;   (format t "Loading Snark.")
;;   (handler-bind ((warning #'ignore-warning))
;;     (cl-user::make-or-load-snark-system))
;;   (format t "~%Finished loading Snark.")
;;   (finish-output t)
;;   )

(declaim (optimize (speed 3) (debug #+sbcl 3 #-sbcl 2) (safety 1)))

;; Snark puts us in another package .. so we go back
(in-package :Specware)

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
    ;; Functions that are assumed by the MetaSlang to Lisp compiler
    "Library/SpecwareRuntime"

    ; "Library/Base/Handwritten/Lisp/Boolean.lisp"
  ;;  "Library/Base/Handwritten/Lisp/meta-slang-runtime.lisp"
  ;;  "Library/Base/Handwritten/Lisp/Integer.lisp"
;    "Library/Base/Handwritten/Lisp/Nat.lisp"
  ;;  "Library/Base/Handwritten/Lisp/Character.lisp"
  ;;  "Library/Legacy/Utilities/Handwritten/Lisp/System.lisp"
  ;;  "Library/Base/Handwritten/Lisp/String.lisp"
    "Library/Unvetted/Handwritten/Lisp/Double.lisp"
    "Library/Unvetted/Handwritten/Lisp/Complex.lisp"
 ;;   "Library/IO/Primitive/Handwritten/Lisp/IO.lisp"
 ;;   "Library/Legacy/Utilities/Handwritten/Lisp/State.lisp"
 ;;   "Library/Legacy/Utilities/Handwritten/Lisp/IO.lisp"
 ;;   "Library/Legacy/Utilities/Handwritten/Lisp/Lisp.lisp"
 ;;   "Library/Algorithms/Handwritten/Lisp/Thread.lisp"
    "Library/Legacy/DataStructures/Handwritten/Lisp/HashTable.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsSTHarray.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsBTHarray.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsBTVector.lisp"
    "Library/Structures/Data/Maps/Handwritten/Lisp/MapAsVector.lisp"
    ;"Library/Structures/Data/Sets/Handwritten/Lisp/SetAsCachedHArray.lisp"
    "Library/Structures/Data/Sets/Handwritten/Lisp/SetAsSTHarray.lisp"
  ;;  "Library/Structures/Data/Monad/Handwritten/Lisp/State.lisp"
    ;; "Languages/XML/Handwritten/Lisp/Chars.lisp"  ; unicode predicates for XML
    ;; "Languages/XML/Handwritten/Lisp/Magic.lisp"  ; escapes from metaslang type system
    "Provers/DP/Handwritten/Lisp/Rational.lisp"
    )
  )

(map 'list #'(lambda (file) (compile-and-load-lisp-file (in-specware-dir file)))
     HandwrittenFiles
     )

(defpackage :Utilities)
(defpackage :Map-Spec)
(defpackage :Annspec)
(defpackage :MetaSlang)
(defpackage :TypeChecker)
(defpackage :PrettyPrint)
(defpackage :System-Spec)

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


(defpackage :Prover)
(defvar Prover::wildCounter 0) ; to suppress annoying compiler warning

;; The following are specific to Specware and languages that
;; extend Specware. The order is significant: specware-state
;; must be loaded before the generated lisp file.
;;
;; The list below is used only in this file.

(defvar SpecwareRuntime
  '(
    ;; XML support -- this provides hooks for reading/writing ad hoc structures
    ;; that are not grounded in normal base specs such as Boolean, Integer, etc.
    ;; "Languages/XML/Handwritten/Lisp/AdHoc.lisp"

    ;; Preface.lisp defines misc things called by Specware4.lisp code,
    ;; so that compiling Specware4.lisp won't genereate compiler warnings.
    "Applications/Specware/Handwritten/Lisp/Preface.lisp"

    ;; The generated lisp code.  This also initializes the Specware
    ;; state in the lisp environment. See SpecCalculus/Semantics/Specware.sw.
    "Applications/Specware/lisp/Specware4.lisp"

    ;; XML support -- this calls code generated in Specware4.lisp for various XML definitions
    ;; maybe interface would be a better name
    ;; "Languages/XML/Handwritten/Lisp/Support.lisp"

    ;; Toplevel commands
    "Applications/Specware/Handwritten/Lisp/toplevel"

    ;; Debugging utilities
    "Applications/Specware/Handwritten/Lisp/debug"
    "Applications/Specware/Handwritten/Lisp/pprint-terms"

    ;; Specware Shell
    "Applications/Specware/Handwritten/Lisp/transform-shell" ; creates    MetaSlangRewriter package
    "Applications/Specware/Handwritten/Lisp/sw-shell"        ; references MetaSlangRewriter package
    "Applications/Specware/Handwritten/Lisp/pprint-terms"

    ;; Test harness
    "Applications/Handwritten/Lisp/test-harness"

;;; CEM 2014-07-22: This has code copyrighted by others.
;;; Moving the actual XmlRpc directory to SpecwareArchive for now.
;;; However, this particuar block of code was part of the Specware build.
;;;    ;; XML-RPC
;;;    "Library/IO/XmlRpc/s-xml/package"
;;;    "Library/IO/XmlRpc/s-xml/xml"
;;;    "Library/IO/XmlRpc/s-xml-rpc/base64"
;;;    "Library/IO/XmlRpc/s-xml-rpc/package"
;;;    "Library/IO/XmlRpc/s-xml-rpc/sysdeps"
;;;    "Library/IO/XmlRpc/s-xml-rpc/xml-rpc"
;;;    "Library/IO/XmlRpc/s-xml-rpc/extensions"
;;;    "Library/IO/XmlRpc/load-xml-rpc"

    )
  )

;(handler-bind ((warning #'ignore-warning))
  (map 'list #'(lambda (file)
		 (if (equal file "Applications/Specware/lisp/Specware4.lisp")
                   (progn
                     (format t "~&;;; Possibly running lisp compiler on Specware--<n>.lisp files.~%")
                     (format t "~&;;; If lisp compilation is needed it takes about 30 seconds...~%")
                     (finish-output t)
                     (time
                      (progn
                        (compile-and-load-lisp-file (in-specware-dir file))
                        (format t "Done compiling."))))
                   (compile-and-load-lisp-file (in-specware-dir file))))
       SpecwareRuntime
       );)

;; Load the parser library and the language specific parser files (grammar etc.)
(make-system (in-specware-dir "Library/Algorithms/Parsing/Chart/Handwritten/Lisp"))

(make-system (in-specware-dir "Languages/SpecCalculus/Parser/Handwritten/Lisp"))

(make-system (in-specware-dir "Languages/MetaSlang/CodeGen/Handwritten/Lisp"))

;;; Initialization includes preloading the base spec.
;;; (Specware::initializeSpecware-0) ; Now happens in startup actions (see bootstrap script)

#+allegro
(defun start-java-connection? ()
  (format t "Checking  command-line arguments: ~a~%" (user-command-line-arguments))
  (when (member "socket" (user-command-line-arguments)
		:test 'equal)
    (load (in-specware-dir "Gui/src/Lisp/specware-socket-init"))))

#+allegro
(push 'start-java-connection? excl:*restart-actions*)


#+case-sensitive
(push  'set-readtable-invert
       #+allegro cl-user::*restart-actions*
       #+cmu     ext:*after-save-initializations*
       #+mcl     ccl:*lisp-startup-functions*
       #+sbcl    sb-ext:*init-hooks*)

;;; Load base in correct location at startup
(push  'Specware::initializeSpecware-0
       #+allegro cl-user::*restart-actions*
       #+cmu     ext:*after-save-initializations*
       #+mcl     ccl:*lisp-startup-functions*
       #+sbcl    sb-ext:*init-hooks*)

;(Specware::initializeSpecware-0)

;;================================================================================
;; Problems with REQUIRE under SBCL:
;;
;; SB-IMPL::MODULE-PROVIDE-CONTRIB used SBCL_HOME to resolve REQUIRE's, and
;; expects it to be something like "/usr/local/lib/sbcl", with a subdir per
;; module, e.g. "sb-bsd-sockets".
;;
;; But at startup, sbcl sets SBCL_HOME to the directory of the executed image.
;; If you are running sbcl directly, this will probably be something like
;; "/usr/local/lib/sbcl", and requires will work.
;;
;; But if you are running a saved image, it will refer to some random directory
;; where that image was saved, and all requires will fail.
;;
;; So we cache *sbcl-home* here to a reasonable value and restore SBCL_HOME to
;; that after sbcl has begun running again.

;; Unfortunately, this introduces a new problem: it assumes the build-time sbcl
;; dir is the same as the run-time sbcl dir, but there is no guarantee of that.
;; In fact, if the run-time sbcl dir differs from the build-time sbcl dir,
;; and the executed sbcl image is not on either such directory, it is not clear
;; if there is any way at all to find the sbcl modules!  Bletch.
;;================================================================================

#+sbcl (progn
	 (defvar *sbcl-home* (Specware::getenv "SBCL_HOME")) ; see note above
	 (push  #'(lambda ()
		    (setq sb-debug:*debug-beginner-help-p* nil)
	            ;(setf (sb-ext:bytes-consed-between-gcs) 50331648)
		    (Specware::setenv "SBCL_HOME" *sbcl-home*) ; see note above
		    )
		sb-ext:*init-hooks*)
	 )

;;; Set temporaryDirectory at startup
(push 'setTemporaryDirectory
      #+allegro cl-user::*restart-actions*
      #+cmu     ext:*after-save-initializations*
      #+mcl     ccl:*lisp-startup-functions*
      #+sbcl    sb-ext:*init-hooks*)

(defun check-for-cygwin ()
  (when System-Spec::msWindowsSystem?
    (let ((n-specware4 (Specware::getenv "SPECWARE4")))
      (when (string= "/cygdrive/" (subseq n-specware4 0 10))
        ;(setq Specware4 n-specware4)
        ;(setq *Specware4* n-specware4)
        (setq cygwin? t)
        (Specware::setenv "SPECWARE4" (Specware::from-cygwin-name n-specware4))))))

(push 'check-for-cygwin
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
  (eval
   `(defparameter ,(intern "*FASL-DIRECTORY*" "SWANK-LOADER")
     (format nil "~a/Library/IO/Emacs/slime/" (Specware::getenv "SPECWARE4"))))
  (let ((loader (in-specware-dir "Library/IO/Emacs/slime/swank-loader.lisp"))
        (hooks (in-specware-dir "Library/IO/Emacs/slime/contrib/swank-listener-hooks.lisp")))
    (load loader :verbose t)
    (funcall (read-from-string "swank-loader:init") :setup nil :reload t :load-contribs t)
    (compile-and-load-lisp-file hooks))
  )
(setq *using-slime-interface?* nil)	; Gets set to t when initialized

;; this is just confusing...
;; (format t "~2%To bootstrap, run (boot)~%")
;; (format t "~%That will run :sw /Applications/Specware/Specware4~2%")

;;;#+allegro
;;;(excl:without-package-locks
;;; (setf (symbol-function 'TPL:TOP-LEVEL-READ-EVAL-PRINT-LOOP)
;;;   #'swshell::specware-shell0))

(defun cl-user::boot ()
  ;#+sbcl (setf (sb-ext:bytes-consed-between-gcs) (* 4 (sb-ext:bytes-consed-between-gcs)))
  (let ((cl:*print-pretty* nil)
        (val (and (cl-user::sw "/Applications/Specware/Specware4")
                  (progn ;(format t "Full garbage collection...")
                         ;(system-spec::garbageCollect t)
                         (terpri t)
                         (cl-user::swl "/Applications/Specware/Specware4")))))
    (unless val
      (funcall (intern #+case-sensitive "eval-in-emacs"
                       #-case-sensitive "EVAL-IN-EMACS"
                       :Emacs)
               "(delete-continuation)"))
    val))
;(trace load)
(declaim (optimize (speed 1) (debug 3) (safety 3)))
