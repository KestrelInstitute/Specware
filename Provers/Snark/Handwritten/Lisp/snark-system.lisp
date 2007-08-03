;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: snark-system.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(unless (find-package :common-lisp)
  (rename-package (find-package :lisp) :common-lisp '(:lisp :cl)))

(unless (find-package :common-lisp-user)
  (rename-package (find-package :user) :common-lisp-user '(:user :cl-user)))

(in-package :common-lisp-user)

;;; load files from the same directory that this file was loaded from

(defparameter *snark-system-pathname* *load-truename*)

(defparameter *snark-files2*
  '("definline-system"
    "mvlet-system"
    "progc-system"
    "collectors-system"
    "doubly-linked-list-system"
    "queues-system"
    "sparse-array-system"
    "package-defs1"
    "snark-pkg"))

(defparameter *snark-lisp-files2*
    '("definline"
      "mvlet"
      "progc"
      "collectors"
      "doubly-linked-list"
      "queues"
      "sparse-array"
      "sparse-vector"))

(defparameter *snark-files*
  '("useful"
    "counters"
    "ordered-sets"
    "davis-putnam3"
    "assoc-cache"
    #+(or mcl cmu) "metering"
    #-allegro-runtime "profiling"
    "map-file"
    "sparse-vector-expression"
    "numbering"
    "posets"
    "topological-sort"
    "solve-sum"
    "permutations"
    "clocks"
    "agenda"
    "globals"
    "options"
    "terms"
    "rows"
    "row-contexts"
    "constants"
    "functions"
    "variables"
    "subst"
    "substitute"
    "symbol-table"
    "assertion-analysis"
    "jepd-relations-tables" "jepd-relations" "date-reasoning2"
    "constraints"
    "connectives"
    "wffs"
    "nonhorn-magic-set"
    "dp-refute"
    "dp-sorts"
    "sorts-functions"
    "sorts"
    "kif"
    "cycl"
    "argument-bag-ac"
    "argument-list-a1"
    "unify"
    "unify-bag" "subsume-bag"
    "unify-vector"
    "equal"
    "variant"
    "alists"
    "plists"
    "term-hash"
    "path-index"
    "term-memory"
;;  "instance-graph" "instance-graph2"
    "weight"
    "eval"
    "read"
    "input"
    "output"
    "simplification-ordering"
    "symbol-ordering"
    "recursive-path-ordering" "ac-rpo"
    "knuth-bendix-ordering"
    "rewrite"
    "rewrite-code"
    "rewrite-code-chars"
    "rewrite-code-numbers"
    "rewrite-code-lists"
    "resolve-code"
    "resolve-code-tables"
    "main"
    "subsume" "subsume-clause"
    "interactive"
    "utilities"
    "tptp"
    "backward-compatibility"
    "coder"
    ;;("examples" "overbeek-test")
    ;;("examples" "front-last-example")
    ;;("examples" "steamroller-example")
    ;;("examples" "reverse-example")
    ;;("examples" "hot-drink-example")
    ;;("examples" "coder-examples")
    "patches"
    ))

(defvar *compile-me* nil)

(defvar *snark-fasl-type*
  #+allegro "fasl"
  #+mcl     "dfsl"
  #+cmu     "x86f"
  #+sbcl    sb-fasl:*fasl-file-type*
  #+clisp   "fas")

(defun need-to-recompile-snark-system ()
  (or
   (loop for name in *snark-lisp-files2*
       thereis
	 (let* ((dir (if (consp name)
			 (append (pathname-directory *snark-system-pathname*) (butlast name))
		       (pathname-directory *snark-system-pathname*)))
		(name (if (consp name) (first (last name)) name))
		(file (make-pathname :directory dir :name name :defaults *snark-system-pathname*)))
	   (> (file-write-date file)
	      (let ((fasl-file (probe-file (make-pathname :defaults file
							  :type *snark-fasl-type*))))
		(if fasl-file (or (file-write-date fasl-file)
				  0)
		  0)))))
   (loop for name in *snark-files*
       thereis
	 (let* ((dir (if (consp name)
			 (append (pathname-directory *snark-system-pathname*) (butlast name))
		       (pathname-directory *snark-system-pathname*)))
		(name (if (consp name) (first (last name)) name))
		(file (make-pathname :directory dir :name name :defaults *snark-system-pathname*)))
	   (> (file-write-date file)
	      (let ((fasl-file (probe-file (make-pathname :defaults file
							  :type *snark-fasl-type*))))
		(if fasl-file (or (file-write-date fasl-file)
				  0)
		  0)))))))

(defun make-snark-system (&optional (*compile-me* *compile-me*))
  (pushnew :snark *features*)
  #+cmu (setf extensions::*gc-verbose* nil)
  (when (eq *compile-me* :optimize)
    (proclaim (print '(optimize (safety 1) (space 1) (speed 3) (debug 1)))))
  (dolist (name *snark-files2*)
    (let* ((dir (if (consp name)
                    (append (pathname-directory *snark-system-pathname*) (butlast name))
                    (pathname-directory *snark-system-pathname*)))
           (name (if (consp name) (first (last name)) name))
           (file (make-pathname :directory dir :name name :defaults *snark-system-pathname*)))
      (load file)))
  (setf *package* (find-package :snark))
  #+gcl (shadow '(#:assert #:substitute #:variable))
  (dolist (name *snark-files*)
    (let* ((dir (if (consp name)
                    (append (pathname-directory *snark-system-pathname*) (butlast name))
                    (pathname-directory *snark-system-pathname*)))
           (name (if (consp name) (first (last name)) name))
           (file (make-pathname :directory dir :name name :defaults *snark-system-pathname*)))
      (load (if *compile-me*
                (compile-file file)
                (or (probe-file (compile-file-pathname file)) file)))))
;;#-(or symbolics mcl) (load "/home/pacific1/stickel/spice/build.lisp")
;;  (setf *package* (find-package :snark-user))
  (setf *print-pretty* nil)
  (funcall (intern (symbol-name :initialize) :snark)))

(defun make-or-load-snark-system ()
  (cond
   ((need-to-recompile-snark-system)
    (make-snark-system t)
    (make-snark-system t))
   (t (make-snark-system nil))))

#+ignore
(defun fix-snark-files ()
  (let ((dir (pathname-directory cl-user::*snark-system-pathname*)))
  (dolist (x (append
              (directory 
               (make-pathname :directory (append dir (list "src")) :name :wild :type "lisp"))
              (directory 
               (make-pathname :directory (append dir (list "Private")) :name :wild :type "lisp"))
              (directory 
               (make-pathname :directory (append dir (list "examples")) :name :wild :type "lisp"))
              (directory 
               (make-pathname :directory (append dir (list "examples")) :name :wild :type "kif"))))
    (ccl:set-mac-file-type x :text)
    (ccl:set-mac-file-creator x :ccl2))))

;;; snark-system.lisp EOF
