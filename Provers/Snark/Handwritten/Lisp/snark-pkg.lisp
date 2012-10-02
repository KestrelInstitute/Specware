;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: common-lisp-user -*-
;;; File: snark-pkg.lisp
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

(in-package :common-lisp-user)

;;; package definitions for snark system

(defpackage :snark
  (:use :common-lisp :mes)
  (:shadowing-import-from :mes "TERPRI")
  #-gcl (:shadow "ASSERT" "SUBSTITUTE" "VARIABLE" "ROW" "ROWS"))

(in-package :snark)
(export
 '(*hash-dollar-package* *hash-dollar-readtable* hash-dollar-prin1 hash-dollar-print
   boolean
   can-be-constant-name-p
   can-be-free-variable-name-p
   declare-cancellation-law
   declare-snark-option
   derivation-subsort-forms
   function-logical-symbol-p
   function-symbol-p
   input-function
   input-constant-symbol
   input-function-symbol
   input-relation-symbol
   input-predicate-symbol	;old name
   input-proposition-symbol
   set-options
   make-snark-system
   map-rows
   matches-compound		;rewrite-compiler
   matches-constant		;rewrite-compiler
   none
   print-agendas
   print-ancestry
   print-clocks
   print-options
   print-rewrites
   print-row
   print-rows
   print-clause-in-tptp-format print-fof-in-tptp-format
   print-row-term
   print-summary
   print-symbol-ordering
   print-symbol-table
   print-term
   read-assertion-file
   read-km->cycl-assertion-file read-km->kif-assertion-file
   refute-file
   sort-name-p
   sortal
   temporal
   term-to-lisp
   top-sort
   total-run-time
   var

   prog->

   initialize assume prove closure proof proofs answer answers

   give factor resolve hyperresolve negative-hyperresolve
   paramodulate paramodulate-by ur-resolve rewrite condense
   row rows name-row last-row it mark-as-given
   delete-row delete-rows
   assert-rewrite

   push-row-context pop-row-context new-row-context

   dereference
   variable-p constant-p compound-p head args arg1 arg2
   make-compound make-compound*
   equal-p unify
   constant-sort variable-sort term-sort
   constant-name
   function-name function-arity
   row-name row-number row-name-or-number row-wff row-answer row-constraints
   row-constrained-p row-ancestry row-reason row-rewrites-used row-parents

   constant-documentation constant-author constant-source
   function-documentation function-author function-source
   sort-documentation sort-author sort-source
   row-documentation row-author row-source row-input-wff

   false true
   forall all exists some
   iff implied-by implies nand nor xor
   |equal|
   answer-if
   => <=> /=
   ? ?x ?y ?z ?u ?v ?w
   ---

   assertion assumption ~conclusion combine embed

   alist plist

   char-list-to-string char-string-to-list

   listof list-to-term term-to-list list-to-atom
   nthrest single double triple item sublist

   positive negative zero natural even odd approx
   nonnegative positive-integer negative-integer
   =< == =/=

   declare-constant declare-proposition
   declare-function declare-relation
   declare-variable

   ;; old names
   declare-constant-symbol declare-proposition-symbol
   declare-function-symbol declare-predicate-symbol declare-relation-symbol
   declare-variable-symbol

   declare-number declare-character declare-string

   declare-ordering-greaterp

   declare-sort
   declare-subsort declare-subsorts
   declare-disjoint-sorts declare-disjoint-subsorts
   declare-sort-intersection

   literal-ordering-a literal-ordering-n literal-ordering-p

   checkpoint-theory uncheckpoint-theory restore-theory
   suspend-snark resume-snark suspend-and-resume-snark

   fifo lifo
   row-depth row-size row-weight row-level
   row-size+depth row-weight+depth
   row-size+depth+level row-weight+depth+level
   row-weight-limit-exceeded row-weight-before-simplification-limit-exceeded
   row-wff&answer-weight+depth row-neg-size+depth

   load-kif-file
   in-language in-kb
   when-system
   defrelation deffunction defobject
   class instance-of subclass-of
   nth-domain domain range domains
   nth-domain-subclass-of domain-subclass-of range-subclass-of
   slot-value-type nth-argument-name domain-name range-name
   arity function-arity relation-arity binary-relation
   relation individual slot
   has-author has-source my-source
   has-documentation has-name
   disjoint-with the-partition template-slot-value
   subrelation-of subinverse-of inverse
   undefined

   declare-jepd-relations
   declare-rcc8-relations
   declare-time-relations
   region time-interval time-point date-interval date-point
   rcc8-dc rcc8-ec rcc8-po rcc8-tpp rcc8-ntpp rcc8-tppi rcc8-ntppi rcc8-eq
   rcc8-dr rcc8-pp rcc8-p rcc8-ppi rcc8-pi rcc8-o rcc8-c
   time-ii-before time-ii-during time-ii-overlaps time-ii-meets time-ii-starts
   time-ii-finishes time-ii-equal time-ii-finished-by time-ii-started-by
   time-ii-met-by time-ii-overlapped-by time-ii-contains time-ii-after
   time-ii-contained-by
   time-pp-before time-pp-equal time-pp-after
   time-pi-before time-pi-starts time-pi-during time-pi-finishes time-pi-after
   time-pi-contained-by
   time-ip-before time-ip-started-by time-ip-contains time-ip-finished-by time-ip-after
   time-ii-starts-before time-ii-starts-equal time-ii-starts-after
   time-ii-finishes-before time-ii-finishes-equal time-ii-finishes-after
   time-ii-subsumes time-ii-subsumed-by
   time-ii-disjoint time-ii-intersects
   time-pi-disjoint time-pi-intersects
   time-ip-disjoint time-ip-intersects

   the-character the-string
   the-list the-cons the-null
   the-number the-real the-complex
   the-rational the-float
   the-integer the-ratio
   the-even the-odd
   the-positive the-positive-integer  
   the-negative the-negative-integer
   the-nonnegative the-nonnegative-integer the-natural
   the-zero
   quit
   ))

(defpackage :snark-user
  (:use :common-lisp :snark)
  (:shadowing-import-from :snark "ASSERT"))

;;; snark-pkg.lisp EOF
