;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: package-defs1.lisp
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

;;(unless (find-package :common-lisp)
;;  (rename-package (find-package :lisp) :common-lisp '(:lisp :cl)))

;;(unless (find-package :common-lisp-user)
;;  (rename-package (find-package :user) :common-lisp-user '(:user :cl-user)))

(in-package :common-lisp-user)

(defpackage :mes
  (:use :common-lisp :mes-sparse-array)
  #+genera (:import-from :future-common-lisp
	    future-common-lisp:declaim
	    future-common-lisp:constantly)
  (:shadow "TERPRI")
  (:export

    ;; defined in useful.lisp
    "DEFINLINE"
    "FLOAT-INTERNAL-TIME-UNITS-PER-SECOND"
    "CARC" "CDRC" "CAARCC" "CADRCC" "CDARCC" "CDDRCC"
    "NEQ" "NEQL" "NEQUAL" "NEQUALP"
    "DOTAILS" "DOPAIRS" "IFF" "IMPLIES" "LCONS" "SETQ-ONCE"
    "ASSOC/EQ" "UNROLL-ASSOC" "UNROLL-ASSOC/EQ"
    #+(OR LUCID GENERA) "DECLAIM"
    #+(OR LUCID GENERA) "CONSTANTLY"
    "KWOTE" "MKLIST" "FIRSTN" "CONSN"
    "CONS-UNLESS-NIL" "LIST-P" "SAME-LENGTH-P" "INTEGERS-BETWEEN"
    "PERCENTAGE" "PRINT-CURRENT-TIME"
    "LEAP-YEAR-P" "DAYS-PER-MONTH" "MONTH-NUMBER"
    "COMMENT" "NOCOMMENT" "TERPRI-COMMENT"
    "*TERPRI-INDENT*" "TERPRI-COMMENT-INDENT" "TERPRI-INDENT"
    "UNIMPLEMENTED"
    "*HASH-DOLLAR-PACKAGE*" "*HASH-DOLLAR-READTABLE*"
    "HASH-DOLLAR-PRIN1" "HASH-DOLLAR-PRINT"

    ;; defined in assoc-cache.lisp
    "MAKE-ASSOC-CACHE" "ASSOC-CACHE-PUSH" "ASSOC-CACHE-ENTRIES"

    ;; defined in map-file.lisp
    "MAPNCONC-FILE-FORMS" "MAPNCONC-FILE-LINES" "READ-FILE"

    ;; defined in profiling.lisp
    "PROFILE"

    ;; defined in mvlet.lisp
    "MVLET" "MVLET*"

    ;; defined in progc.lisp
    "PROG->"
    "WRAP-PROGN" "WRAP-BLOCK"

    ;; defined in counters.lisp
    "MAKE-COUNTER"
    "INCREMENT-COUNTER" "DECREMENT-COUNTER"
    "COUNTER-VALUE" "COUNTER-VALUES"
    "PRINCF"

    ;; defined in collectors.lisp
    ;; "MAKE-COLLECTOR" "COLLECTOR-VALUE" "COLLECT-ITEM" "COLLECT-LIST"
    "COLLECT" "NCOLLECT"
    "PUSHNEW-UNLESS-NIL"

    ;; defined in sparse-vector-expression.lisp
    "SPARSE-VECTOR-EXPRESSION-P"
    "MAP-SPARSE-VECTOR-EXPRESSION"
    "MAP-SPARSE-VECTOR-EXPRESSION-WITH-INDEXES"
    "MAP-SPARSE-VECTOR-EXPRESSION-INDEXES-ONLY"
    "OPTIMIZE-SPARSE-VECTOR-EXPRESSION"
    "UNIOND"

    ;; defined in numbering.lisp
    "NONCE"
    "INITIALIZE-NUMBERINGS" "MAKE-NUMBERING"
    "*STANDARD-EQL-NUMBERING*" "*STANDARD-EQUAL-NUMBERING*"

    ;; defined in ordered-sets.lisp
    "ORDERED-SET" "MAKE-ORDERED-SET" "ORDERED-SET-P"
    "OSET-INSERT" "OSET-INSERT-KEY"
    "OSET-MEMBER" "OSET-DELETE"
    "OSET-FIND-KEY" "OSET-DELETE-KEY"
    "OSET-FIRST" "OSET-DELETE-FIRST"
    "OSET-LAST" "OSET-DELETE-LAST"
    "OSET-FIND-IF" "OSET-DELETE-IF"
    "MAPC-OSET" "MAPCAR-OSET" "MAPNCONC-OSET"
    "OSET-ELEMENTS" "OSET-SIZE"
    "OSET-FIRST*" "OSET-LAST*" "OSET-NEXT*" "OSET-PREV*"
    "OSET-MEMBER*" "OSET-FIND-KEY*" "OSET-DELETE*" "OSET-ELEMENT*"
    "OSET-EQUAL-P" "OSET-SUBSET-P" "OSET-INTERSECTION" "OSET-UNION" "OSET-DIFFERENCE"

    ;; defined in posets.lisp
    "MAKE-POSET"
    "DECLARE-POSET-GREATERP" "DECLARE-POSET-LESSP"
    "POSET-GREATERP" "POSET-LESSP" "POSET-EQUIVALENT"
    "POSET-SUPERIORS" "POSET-INFERIORS"

    ;; defined in topological-sort.lisp
    "TOPOLOGICAL-SORT*" "TOPOLOGICAL-SORT"

    ;; defined in sorted-sets.lisp
    "SORTED-INSERT" "SORTED-DELETE"
    "SORTED-ADJOIN" "SORTED-REMOVE"
    "SORTED-SET-P" "SORTED-MEMBER" "SORTED-SUBSETP"
    "SORTED-UNION" "SORTED-INTERSECTION"
    "SORTED-SET-DIFFERENCE" "SORTED-SET-EXCLUSIVE-OR"

    ;; defined in queues.lisp
    "MAKE-QUEUE" "QUEUE-LENGTH" "QUEUE-EMPTY-P"
    "QUEUE-FIRST" "QUEUE-LAST"
    "ENQUEUE" "DEQUEUE"
    "QUEUE-DELETE" "QUEUE-DELETE/EQ"
    "MAPNCONC-QUEUE" "DO-QUEUE"

    ;; defined in agenda.lisp
    "MAKE-AGENDA" "AGENDA-LENGTH" "AGENDA-ENTRIES"
    "AGENDA-INSERT" "AGENDA-DELETE"
    "AGENDA-FIRST" "POP-AGENDA" "AGENDA-LAST" "MAPNCONC-AGENDA" "AGENDA-DELETE-IF"
    "AGENDAS-FIRST" "POP-AGENDAS"
    "PRINT-AGENDA" "PRINT-AGENDAS"
    "*AGENDA*" "*AGENDAS*"

    ;; defined in structure-sets.lisp
    "DEFSTRUCTSET" "INSERT-X" "DELETE-X" "ALL-X" "SOME-X" "THE-X" "MAP-X"

    ;; defined in permutations.lisp
    "PERMUTATION-P" "PERMUTE" "PERMUTE-RANDOMLY" "PERMUTATIONS"
    "ALL-INSERTIONS" "ALL-PERMUTATIONS"

    ;; defined in clocks.lisp
    "INITIALIZE-CLOCKS" "PRINT-CLOCKS"
    "WITH-CLOCK-ON" "WITH-CLOCK-OFF"
    "TOTAL-RUN-TIME"

    ;; defined in csp.lisp
    "MAKE-CSP-VARIABLE" "MAKE-CSP-CONSTRAINT" "MAKE-CSP"
    "SOLVE-CSP"
    "CSP-VARIABLE-NAME" "CSP-VARIABLE-VALUE"

    ))

(do-external-symbols (symbol :mes-sparse-array)
  (export (list symbol) :mes))

;;; package-defs1.lisp EOF
