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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(unless (find-package :common-lisp)
  (rename-package (find-package :lisp) :common-lisp '(:lisp :cl)))

(unless (find-package :common-lisp-user)
  (rename-package (find-package :user) :common-lisp-user '(:user :cl-user)))

(in-package :common-lisp-user)

;;; load snark files from the directory that this file was loaded from

(defparameter *snark-source-directory* (pathname-directory *load-truename*))

(defparameter *snark-source-extension* "lisp")

(defparameter *snark-binary-directory*
	      #-gcl       *snark-source-directory*  
	      #+(and gcl solaris)       "/home/pacific1/stickel/snark/bin-solaris/"
	      #+(and gcl (not solaris)) "/home/pacific1/stickel/snark/bin-sunos/"
	      )

(defparameter *snark-binary-extension*
	      #+(and symbolics (not imach))  "bin"
	      #+(and symbolics imach)        "ibin"
	      #+lucid                        "sbin"
	      #+allegro                      "fasl"
	      #+lispworks                    "wfasl"
	      #+gcl                          "o"
	      #+eclipse                      "c"
	      #+(and mcl powerpc)            "pfsl"
	      #+(and mcl (not powerpc))      "fasl"
	      #+(and (or cmu sbcl) sparc)    "sparcf"
	      #+(and (or cmu sbcl) x86)      "x86f"
              #+clisp                        "fas"
	      )

(load (make-pathname :directory *snark-source-directory*
		     :name "package-defs1"
		     :type *snark-source-extension*))

(defpackage :snark
  (:use :common-lisp :mes)
;;(:nicknames :hpkb)
  (:import-from :common-lisp-user #+(or lucid cmu sbcl) quit)
  (:shadowing-import-from :mes "TERPRI")
  #-gcl (:shadow "ASSERT" "SUBSTITUTE" "VARIABLE" "ROW" "ROWS")
  (:export
   "*HASH-DOLLAR-PACKAGE*" "*HASH-DOLLAR-READTABLE*" "HASH-DOLLAR-PRIN1" "HASH-DOLLAR-PRINT"
   "BOOLEAN"
   "CAN-BE-CONSTANT-NAME-P"
   "CAN-BE-FREE-VARIABLE-NAME-P"
   "DECLARE-CANCELLATION-LAW"
   "DECLARE-SNARK-OPTION"
   "DERIVATION-SUBSORT-FORMS"
   "FUNCTION-LOGICAL-SYMBOL-P"
   "FUNCTION-SYMBOL-P"
   "INPUT-FUNCTION"
   "INPUT-CONSTANT-SYMBOL"
   "INPUT-FUNCTION-SYMBOL"
   "INPUT-PREDICATE-SYMBOL" "INPUT-RELATION-SYMBOL"
   "INPUT-PROPOSITION-SYMBOL"
   "SET-OPTIONS"
   "MAKE-SNARK-SYSTEM"
   "MAP-ROWS"
   "MATCHES-COMPOUND"		;rewrite-compiler
   "MATCHES-CONSTANT"		;rewrite-compiler
   "NONE"
   "PRINT-AGENDAS"
   "PRINT-ANCESTRY"
   "PRINT-CLOCKS"
   "PRINT-OPTIONS"
   "PRINT-REWRITES"
   "PRINT-ROW"
   "PRINT-ROWS"
   "PRINT-CLAUSE-IN-TPTP-FORMAT" "PRINT-FOF-IN-TPTP-FORMAT"
   "PRINT-ROW-TERM"
   "PRINT-SUMMARY"
   "PRINT-SYMBOL-ORDERING"
   "PRINT-SYMBOL-TABLE"
   "PRINT-TERM"
   "READ-ASSERTION-FILE" "READ-CYCL-ASSERTION-FILE" "READ-KM-ASSERTION-FILE"
   "READ-KM->CYCL-ASSERTION-FILE" "READ-KM->KIF-ASSERTION-FILE"
   "REFUTE-FILE"
   "SORT-NAME-P"
   "SORTAL"
   "TEMPORAL"
   "TERM-TO-LISP"
   "TOP-SORT"
   "TOTAL-RUN-TIME"
   "VAR"

   "PROG->"

   "INITIALIZE" "ASSUME" "PROVE" "CLOSURE" "PROOF" "PROOFS" "ANSWER" "ANSWERS"

   "GIVE" "FACTOR" "RESOLVE" "HYPERRESOLVE" "NEGATIVE-HYPERRESOLVE"
   "PARAMODULATE" "PARAMODULATE-BY" "UR-RESOLVE" "REWRITE" "CONDENSE"
   "ROW" "ROWS" "NAME-ROW" "LAST-ROW" "IT" "MARK-AS-GIVEN"
   "DELETE-ROW" "DELETE-ROWS"
   "ASSERT-REWRITE"

   "PUSH-ROW-CONTEXT" "POP-ROW-CONTEXT" "NEW-ROW-CONTEXT"

   "DEREFERENCE"
   "VARIABLE-P" "CONSTANT-P" "COMPOUND-P" "HEAD" "ARGS" "ARG1" "ARG2"
   "MAKE-COMPOUND" "MAKE-COMPOUND*"
   "EQUAL-P" "UNIFY"
   "CONSTANT-SORT" "VARIABLE-SORT" "TERM-SORT"
   "CONSTANT-NAME"
   "FUNCTION-NAME" "FUNCTION-ARITY"
   "ROW-NAME" "ROW-NUMBER" "ROW-NAME-OR-NUMBER" "ROW-WFF" "ROW-ANSWER" "ROW-CONSTRAINTS"
   "ROW-CONSTRAINED-P" "ROW-ANCESTRY" "ROW-REASON" "ROW-REWRITES-USED" "ROW-PARENTS"

   "CONSTANT-DOCUMENTATION" "CONSTANT-AUTHOR" "CONSTANT-SOURCE"
   "FUNCTION-DOCUMENTATION" "FUNCTION-AUTHOR" "FUNCTION-SOURCE"
   "SORT-DOCUMENTATION" "SORT-AUTHOR" "SORT-SOURCE"
   "ROW-DOCUMENTATION" "ROW-AUTHOR" "ROW-SOURCE" "ROW-INPUT-WFF"

   "FALSE" "TRUE"
   "FORALL" "ALL" "EXISTS" "SOME"
   "IFF" "IMPLIED-BY" "IMPLIES" "NAND" "NOR" "XOR"
   "ANSWER-IF"
   "=>" "<=>" "/="
   "?" "?X" "?Y" "?Z" "?U" "?V" "?W"
   "---"

   "ASSERTION" "ASSUMPTION" "~CONCLUSION" "COMBINE" "EMBED"

   "ALIST" "PLIST"

   "CHAR-LIST-TO-STRING" "CHAR-STRING-TO-LIST"

   "LISTOF" "LIST-TO-TERM" "TERM-TO-LIST" "LIST-TO-ATOM"
   "NTHREST" "SINGLE" "DOUBLE" "TRIPLE" "ITEM" "SUBLIST"

   "POSITIVE" "NEGATIVE" "ZERO" "NATURAL" "EVEN" "ODD" "APPROX"
   "NONNEGATIVE" "POSITIVE-INTEGER" "NEGATIVE-INTEGER"
   "=<" "==" "=/="

   "DECLARE-CONSTANT-SYMBOL" "DECLARE-PROPOSITION-SYMBOL"
   "DECLARE-FUNCTION-SYMBOL" "DECLARE-PREDICATE-SYMBOL" "DECLARE-RELATION-SYMBOL"
   "DECLARE-VARIABLE-SYMBOL"
   "LITERAL-ORDERING-A" "LITERAL-ORDERING-N" "LITERAL-ORDERING-P"

   "DECLARE-NUMBER" "DECLARE-CHARACTER" "DECLARE-STRING"

   "DECLARE-ORDERING-GREATERP"

   "DECLARE-SORT"
   "DECLARE-SUBSORT" "DECLARE-SUBSORTS"
   "DECLARE-DISJOINT-SORTS" "DECLARE-DISJOINT-SUBSORTS"
   "DECLARE-SORT-INTERSECTION"

   "CHECKPOINT-THEORY" "UNCHECKPOINT-THEORY" "RESTORE-THEORY"
   "SUSPEND-SNARK" "RESUME-SNARK"

   "FIFO" "LIFO"
   "ROW-DEPTH" "ROW-SIZE" "ROW-WEIGHT" "ROW-LEVEL"
   "ROW-SIZE+DEPTH" "ROW-WEIGHT+DEPTH"
   "ROW-SIZE+DEPTH+LEVEL" "ROW-WEIGHT+DEPTH+LEVEL"
   "ROW-WEIGHT-LIMIT-EXCEEDED" "ROW-WEIGHT-BEFORE-SIMPLIFICATION-LIMIT-EXCEEDED"
   "ROW-WFF&ANSWER-WEIGHT+DEPTH" "ROW-NEG-SIZE+DEPTH"

   "LOAD-KIF-FILE"
   "IN-LANGUAGE" "IN-KB"
   "WHEN-SYSTEM"
   "DEFRELATION" "DEFFUNCTION" "DEFOBJECT"
   "CLASS" "INSTANCE-OF" "SUBCLASS-OF"
   "NTH-DOMAIN" "DOMAIN" "RANGE" "DOMAINS"
   "NTH-DOMAIN-SUBCLASS-OF" "DOMAIN-SUBCLASS-OF" "RANGE-SUBCLASS-OF"
   "SLOT-VALUE-TYPE" "NTH-ARGUMENT-NAME" "DOMAIN-NAME" "RANGE-NAME"
   "ARITY" "FUNCTION-ARITY" "RELATION-ARITY" "BINARY-RELATION"
   "RELATION" "INDIVIDUAL" "SLOT"
   "HAS-AUTHOR" "HAS-SOURCE" "MY-SOURCE"
   "HAS-DOCUMENTATION" "HAS-NAME"
   "DISJOINT-WITH" "THE-PARTITION" "TEMPLATE-SLOT-VALUE"
   "SUBRELATION-OF" "SUBINVERSE-OF" "INVERSE"
   "UNDEFINED"

   "DECLARE-JEPD-RELATIONS"
   "DECLARE-RCC8-RELATIONS"
   "DECLARE-TIME-RELATIONS"
   "REGION" "TIME-INTERVAL" "TIME-POINT" "DATE-INTERVAL" "DATE-POINT"
   "RCC8-DC" "RCC8-EC" "RCC8-PO" "RCC8-TPP" "RCC8-NTPP" "RCC8-TPPI" "RCC8-NTPPI" "RCC8-EQ"
   "RCC8-DR" "RCC8-PP" "RCC8-P" "RCC8-PPI" "RCC8-PI" "RCC8-O" "RCC8-C"
   "TIME-II-BEFORE" "TIME-II-DURING" "TIME-II-OVERLAPS" "TIME-II-MEETS" "TIME-II-STARTS"
   "TIME-II-FINISHES" "TIME-II-EQUAL" "TIME-II-FINISHED-BY" "TIME-II-STARTED-BY"
   "TIME-II-MET-BY" "TIME-II-OVERLAPPED-BY" "TIME-II-CONTAINS" "TIME-II-AFTER"
   "TIME-II-CONTAINED-BY"
   "TIME-PP-BEFORE" "TIME-PP-EQUAL" "TIME-PP-AFTER"
   "TIME-PI-BEFORE" "TIME-PI-STARTS" "TIME-PI-DURING" "TIME-PI-FINISHES" "TIME-PI-AFTER"
   "TIME-PI-CONTAINED-BY"
   "TIME-IP-BEFORE" "TIME-IP-STARTED-BY" "TIME-IP-CONTAINS" "TIME-IP-FINISHED-BY" "TIME-IP-AFTER"
   "TIME-II-STARTS-BEFORE" "TIME-II-STARTS-EQUAL" "TIME-II-STARTS-AFTER"
   "TIME-II-FINISHES-BEFORE" "TIME-II-FINISHES-EQUAL" "TIME-II-FINISHES-AFTER"
   "TIME-II-SUBSUMES" "TIME-II-SUBSUMED-BY"
   "TIME-II-DISJOINT" "TIME-II-INTERSECTS"
   "TIME-PI-DISJOINT" "TIME-PI-INTERSECTS"
   "TIME-IP-DISJOINT" "TIME-IP-INTERSECTS"

   "THE-CHARACTER" "THE-STRING"
   "THE-LIST" "THE-CONS" "THE-NULL"
   "THE-NUMBER" "THE-REAL" "THE-COMPLEX"
   "THE-RATIONAL" "THE-FLOAT"
   "THE-INTEGER" "THE-RATIO"
   "THE-EVEN" "THE-ODD"
   "THE-POSITIVE" "THE-POSITIVE-INTEGER"  
   "THE-NEGATIVE" "THE-NEGATIVE-INTEGER"
   "THE-NONNEGATIVE" "THE-NONNEGATIVE-INTEGER" "THE-NATURAL"
   "THE-ZERO"
   ))

(defpackage :snark-user
  (:use :common-lisp :snark)
  (:shadowing-import-from :snark "ASSERT"))

(defparameter *snark-files*
	      '("mvlet"
                "useful"
                "counters"
		"collectors"
                "ordered-sets"
		"davis-putnam3"
		"assoc-cache"
		"map-file"
		#+(or mcl cmu) "metering"
                #-allegro-runtime "profiling"
		"progc"
		"queues"
                "sparse-array4"
                "sparse-array"
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
;;              "instance-graph" "instance-graph2"
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
		;; ("examples" "overbeek-test")
		;; ("examples" "front-last-example")
		;; ("examples" "steamroller-example")
		;; ("examples" "reverse-example")
                ;; ("examples" "hot-drink-example")
		"patches"
		))

(defparameter snark:*hash-dollar-package* nil)

(defvar *cycl-package* (or (find-package :cycl)
                           (make-package :cycl :use '(:common-lisp))))

(defvar *km-package* (or (find-package :km)
                         (make-package :km :use '(:common-lisp))))

(defun snark::snark-file-source-directory (file)
  (if (atom file)
      *snark-source-directory*
      (append *snark-source-directory* (butlast file))))

(defun snark::snark-file-binary-directory (file)
  (if (atom file)
      *snark-binary-directory*
      (append *snark-binary-directory* (butlast file))))

(defun snark::snark-file-name (file)
  (if (atom file)
      file
      (first (last file))))

(defun snark:make-snark-system (&optional compile)
  (pushnew :snark *features*)
  #+cmu (setf extensions::*gc-verbose* nil)
  (setf *package* (find-package :snark))
  #+gcl (shadow '(#:assert #:substitute #:variable))
  (when (eq compile :optimize)
    (proclaim (print '(optimize (safety 1) (space 1) (speed 3) (debug 1)))))
  
  #-eclipse
  (dolist (file *snark-files*)
    (let* ((name (snark::snark-file-name file))
           (srcfile (make-pathname :directory (snark::snark-file-source-directory file)
				   :name name
				   :type *snark-source-extension*))
	   (binfile (make-pathname :directory (snark::snark-file-binary-directory file)
				   :name name
				   :type  *snark-binary-extension*))
           (snark:*hash-dollar-package* nil))
      (when compile
	(compile-file srcfile :output-file binfile))
      (load binfile :verbose t :print compile)))
  
  #+eclipse
  (dolist (file *snark-files*)
    (let* ((name (snark::snark-file-name file))
           (srcfile (make-pathname :directory (snark::snark-file-source-directory file)
                                   :name name
                                   :type *snark-source-extension*))
           (snark:*hash-dollar-package* nil))
      (load srcfile :verbose t :print t)))
  
  #+eclipse
  (when compile
    (dolist (file *snark-files*)
      (let* ((name (snark::snark-file-name file))
             (srcfile (make-pathname :directory (snark::snark-file-source-directory file)
				     :name name
				     :type *snark-source-extension*))
	     (binfile (make-pathname :directory (snark::source-file-binary-directory file)
				     :name name
				     :type *snark-binary-extension*))
             (snark:*hash-dollar-package* nil))
        (compile-file srcfile :output-file binfile
                      'eclipse::loader-name (intern (format nil "~A-LOADER" file))
                      ))))
  
  ;;#-(or symbolics mcl) (load "/home/pacific1/stickel/spice/build.lisp")
  (setf *package* (find-package :snark-user))
  (snark:initialize))

(defun make-snark-system (&optional compile)
  (snark:make-snark-system compile))

#+ignore
(defun fix-snark-files ()
  (dolist (x (append
              (directory (make-pathname :directory cl-user::*snark-source-directory*
                                        :name :wild
                                        :type "lisp"))
              (directory (make-pathname :directory (append cl-user::*snark-source-directory*
                                                           '("Private"))
                                        :name :wild
                                        :type "lisp"))
              (directory (make-pathname :directory (append cl-user::*snark-source-directory*
                                                           '("examples"))
                                        :name :wild
                                        :type "lisp"))
              (directory (make-pathname :directory (append cl-user::*snark-source-directory*
                                                           '("examples"))
                                        :name :wild
                                        :type "kif"))))
    (ccl:set-mac-file-type x :text)
    (ccl:set-mac-file-creator x :ccl2)))

;;; snark-system.lisp EOF
