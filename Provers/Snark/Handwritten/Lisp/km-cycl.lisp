;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: km-cycl.lisp
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
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>, Susan Buchman.

(in-package :snark)

#|
KM->CycL translator

Guide to Expansion:

I. Overview of important functions.
   A. Router. 

      Although in general every KM function is handled by the same
recursive function, there are of course slight differences in each
"main" KM command (a "main" command is one that can stand on its own
or appear first in a KM expression. "every" is an example of a "main"
command. "of" is an example of a non-"main" command). Therefore, most
main commands have their own function, from which the more general
recursive function is called. Router takes a KM expression, determines
which main function is being used, and calls the appropriate function.

   B. proc2

     proc2 is the general recursive function which translates the
expressions.

   C.

|#

;;; km->cycL translator , version 0.1 (as of 2000-08-17)
;;; send comments to susan buchman, buchman@ai.sri.com

;;; the procedure km->cycL translates a list Km expressions represented
;;; as a list of symbols, and returns a list of the cycL expressions
;;; which are equivalent (see example below).

;; things to fix:
;; exactly command
;; when a SLOT is itself an (Every ..) expression (see quoted km code)
;; clost but still a problem with teh numbering

;;; assert-test-suite.lisp-script sample usage:
;;;  (defpackage :cycl)
;;;  (defpackage :km)
;;;  (initialize-km->cycl)		;redo when changing the package for CycL or KM symbols
;;;  (initialize)
;;;  (use-cycl-symbols t)		;do after initialize
;;;
;;;  (use-resolution t)			;these inference options for illustration only
;;;  (assert-sequential t)		;you may have different requirements
;;;  (prove-sequential t)
;;;  (assume-sequential t)
;;;
;;;  (load "~buchman/c2.lisp")		;this file
;;;  (initialize-km->cycl)
;;;  (mapc #'eval (read-km->cycl-assertion-file "~buchman/v.lisp"))

(declaim (special *hash-dollar-package*))

;;; global variables *km-a-symbol*, *cycl-true-symbol*, etc. are initially undefined
;;; they are initialized to the corresponding KM or CycL symbol by executing
;;; (initialize-km->cycl) with SNARK functions KM-PACKAGE and CYCL-PACKAGE
;;; used to specify the names of the packages used for KM and CycL symbols

(eval-when (:compile-toplevel :load-toplevel)
  (defparameter *km->cycl-km-symbols*
    '(
      (*km-a-symbol*               "#$a")
      (*km-a+-symbol*              "#$a+")
      (*km-abs-symbol*             "#$abs")
      (*km-add-list-symbol*        "#$add-list")
      (*km-aggregation-function-symbol* "#$aggregation-function")
      (*km-allof-symbol*           "#$allof")
      (*km-allof2-symbol*          "#$allof2")
      (*km-all-classes-symbol*     "#$all-classes")
      (*km-all-instances-symbol*   "#$all-instances")
      (*km-all-prototypes-symbol*  "#$all-prototypes")
      (*km-all-subclasses-symbol*  "#$all-subclasses")
      (*km-all-subslots-symbol*    "#$all-subslots")
      (*km-all-superclasses-symbol* "#$all-superclasses")
      (*km-all-supersituations-symbol* "#$all-supersituations")
      (*km-all-true-symbol*        "#$all-true")
      (*km-an-symbol*              "#$an")
      (*km-and-symbol*             "#$and")
      (*km-andify-symbol*          "#$andify")
      (*km-are-symbol*             "#$are")
      (*km-assertions-symbol*      "#$assertions")
      (*km-at-least-symbol*        "#$at-least")
      (*km-at-most-symbol*         "#$at-most")
      (*km-average-symbol*         "#$average")
      (*km-a-prototype-symbol*     "#$a-prototype")
      (*km-assert-symbol*          "#$assert")
      (*km-cardinality-symbol*     "#$cardinality")
      (*km-covers-symbol*          "#$covers")
      (*km-class-symbol*           "#$Class")
      (*km-classes-symbol*         "#$classes")
      (*km-clone-symbol*           "#$clone")
      (*km-cloned-from-symbol*     "#$cloned-from")
      (*km-constraint-symbol*      "#$constraint")
      (*km-curr-situation-symbol*  "#$curr-situation")
      (*km-default-fluent-status-symbol* "#$default-fluent-status")
      (*km-definition-symbol*      "#$definition")
      (*km-delete-symbol*          "#$delete")
      (*km-del-list-symbol*        "#$del-list")
      (*km-difference-symbol*      "#$difference")
      (*km-do-symbol*              "#$do")
      (*km-domain-symbol*          "#$domain")
      (*km-domain-of-symbol*       "#$domain-of")
      (*km-do-and-next-symbol*     "#$do-and-next")
      (*km-do-script-symbol*       "#$do-script")
      (*km-difference-symbol*      "#$difference")
      (*km-elements-symbol*        "#$elements")
      (*km-else-symbol*            "#$else")
      (*km-end-prototype-symbol*   "#$end-prototype")
      (*km-evaluate-symbol*        "#$evaluate")
      (*km-evaluate-all-symbol*    "#$evaluate-all")
      (*km-evaluate-paths-symbol*  "#$evaluate-paths")
      (*km-every-symbol*           "#$every")
      (*km-exactly-symbol*         "#$exactly")
      (*km-exp-symbol*             "#$exp")
      (*km-fifth-symbol*           "#$fifth")
      (*km-first-symbol*           "#$first")
      (*km-floor-symbol*           "#$floor")
      (*km-fluent-instancep-symbol* "#$fluent-instancep")
      (*km-fluent-status-symbol*   "#$fluent-status")
      (*km-fluent-status-of-symbol* "#$fluent-status-of")
      (*km-forall-symbol*          "#$forall")
      (*km-forall2-symbol*         "#$forall2")
      (*km-format-symbol*          "#$format")
      (*km-fourth-symbol*          "#$fourth")
      (*km-frame-symbol*           "#$frame")
      (*km-global-situation-symbol* "#$global-situation")
      (*km-graph-symbol*           "#$graph")
      (*km-has-symbol*             "#$has")
      (*km-has-definition-symbol*  "#$has-definition")
      (*km-has-value-symbol*       "#$has-value")
      (*km-if-symbol*              "#$if")
      (*km-ignore-result-symbol*   "#$ignore-result")
      (*km-includes-symbol*        "#$includes")
      (*km-instance-symbol*        "#$instance")
      (*km-instances-symbol        "#$instances")
      (*km-instance-of-symbol*     "#$instance-of")
      (*km-inverse-symbol*         "#$inverse")
      (*km-inverse2-symbol*        "#$inverse2")
      (*km-inverse3-symbol*        "#$inverse3")
      (*km-in-every-situation-symbol* "#$in-every-situation")
      (*km-in-situation-symbol*    "#$in-situation")
      (*km-is-symbol*              "#$is")
      (*km-is-superset-of-symbol*  "#$is-superset-of")
      (*km-is-true-symbol*         "#$is-true")
      (*km-isa-symbol*             "#$isa")
      (*km-it-symbol*              "#$It")
      (*km-it2-symbol*             "#$It2")
      (*km-km-format-symbol*       "#$km-format")
      (*km-last-symbol*            "#$last")
      (*km-log-symbol*             "#$log")
      (*km-make-phrase*            "#$make-phrase")
      (*km-make-sentence*          "#$make-sentence")
      (*km-max-symbol*             "#$max")
      (*km-members-symbol*         "#$members")
      (*km-min-symbol*             "#$min")
      (*km-must-symbol*            "#$must")
      (*km-must-be-a-symbol*       "#$must-be-a")
      (*km-mustnt-be-a-symbol*     "#$mustnt-be-a")
      (*km-ncs-list-symbol*        "#$ncs-list")
      (*km-new-context-symbol*     "#$new-context")
      (*km-name-symbol*            "#$name")
      (*km-new-situation-symbol*   "#$new-situation")
      (*km-next-situation-symbol*  "#$next-situation")
      (*km-not-symbol*             "#$not")
      (*km-number-symbol*          "#$number")
      (*km-numberp-symbol*         "#$numberp")
      (*km-oneof-symbol*           "#$oneof")
      (*km-oneof2-symbol*          "#$oneof2")
      (*km-of-symbol*              "#$of")
      (*km-or-symbol*              "#$or")
      (*km-partition-symbol*       "#$partition")
      (*km-pcs-list-symbol*        "#$pcs-list")
      (*km-pluralize-symbol*       "#$pluralize")
      (*km-prev-situation-symbol*  "#$prev-situation")
      (*km-print-symbol*           "#$print")
      (*km-product-symbol*         "#$product")
      (*km-protoparts-symbol*      "#$protoparts")
      (*km-protopart-of-symbol*    "#$protopart-of")
      (*km-prototypes-symbol*      "#$prototypes")
      (*km-prototype-of-symbol*    "#$prototype-of")
      (*km-quote-symbol*           "#$quote")
      (*km-quotient-symbol*        "#$quotient")
      (*km-range-symbol*           "#$range")
      (*km-range-of-symbol*        "#$range-of")
      (*km-reverse-symbol*         "#$reverse")
      (*km-second-symbol*          "#$second")
      (*km-self-symbol*            "#$Self")
      (*km-set-constraint-symbol*  "#$set-constraint")
      (*km-set-unification-symbol* "#$set-unification")
      (*km-situation-specific-symbol* "#$situation-specific")
      (*km-slot-symbol*            "#$slot")
      (*km-some-symbol*            "#$some")
      (*km-some-true-symbol*       "#$some-true")
      (*km-s\l\o\t-symbol*         "#$Slot")
      (*km-sqrt-symbol*            "#$sqrt")
      (*km-subclasses-symbol*      "#$subclasses")
      (*km-subsituations-symbol*   "#$subsituations")
      (*km-subslots-symbol*        "#$subslots")
      (*km-sum-symbol*             "#$sum")
      (*km-subsumes-symbol*        "#$subsumes")
      (*km-superclasses-symbol*    "#$superclasses")
      (*km-supersituations-symbol* "#$supersituations")
      (*km-superslots-symbol*      "#$superslots")
      (*km-the-symbol*             "#$the")
      (*km-the1-symbol*            "#$the1")
      (*km-the2-symbol*            "#$the2")
      (*km-the3-symbol*            "#$the3")
      (*km-\t\h\en-symbol*         "#$theN")
      (*km-the+-symbol*            "#$the+")
      (*km-thelast-symbol*         "#$thelast")
      (*km-theoneof-symbol*        "#$theoneof")
      (*km-theoneof2-symbol*       "#$theoneof2")
      (*km-then-symbol*            "#$then")
      (*km-thesituation-symbol*    "#$TheSituation")
      (*km-thevalue-symbol*        "#$TheValue")
      (*km-thevalues-symbol*       "#$TheValues")
      (*km-thing-symbol*           "#$Thing")
      (*km-third-symbol*           "#$third")
      (*km-true-symbol*            "#$t")
      (*km-unification-symbol*     "#$unification")
      (*km-value-symbol*           "#$value")
      (*km-where-symbol*           "#$where")
      (*km-with-symbol*            "#$with")

      (*km-=-symbol*               "#$=")
      (*km-/=-symbol*              "#$/=")
      (*km->-symbol*               "#$>")
      (*km-<-symbol*               "#$<")
      (*km->=-symbol*              "#$>=")
      (*km-<=-symbol*              "#$<=")
      (*km-+-symbol*               "#$+")
      (*km---symbol*               "#$-")
      (*km-*-symbol*               "#$*")
      (*km-/-symbol*               "#$/")
      (*km-^-symbol*               "#$^")
      (*km-&-symbol*               "#$&")
      (*km-==-symbol*              "#$==")
      (*km-&+-symbol*              "#$&+")
      (*km-&!-symbol*              "#$&!")
      (*km-&?-symbol*              "#$&?")
      (*km-&&-symbol*              "#$&&")
      (*km-===-symbol*             "#$===")
      (*km-&&!-symbol*             "#$&&!")
      (*km-<>-symbol*              "#$<>")

      (*km-args-symbol*            "#$:args")
      (*km-seq-symbol*             "#$:seq")
      (*km-set-symbol*             "#$:set")
      (*km-triple-symbol*          "#$:triple")

      (*km-1-to-1-symbol*          "#$1-to-1")
      (*km-1-to-n-symbol*          "#$1-to-N")
      (*km-n-to-1-symbol*          "#$N-to-1")
      (*km-n-to-n-symbol*          "#$N-to-N")

      (*km-checkkboff-symbol*      "#$checkkboff")
      (*km-checkkbon-symbol*       "#$checkkbon")
      (*km-comments-symbol*        "#$comments")
      (*km-disable-classification-symbol* "#$disable-classification")
      (*km-enable-classification-symbol* "#$enable-classification")
      (*km-fail-noisily-symbol*    "#$fail-noisily")
      (*km-fail-quitely-symbol*    "#$fail-quietly")
      (*km-install-all-subclasses-symbol* "#$install-all-subclasses")
      (*km-load-kb-symbol*         "#$load-kb")
      (*km-nocomments-symbol*      "#$nocomments")
      (*km-reset-kb-symbol*        "#$reset-kb")
      (*km-save-kb-symbol*         "#$save-kb")
      (*km-scan-kb-symbol*         "#$scan-kb")
      (*km-setq-symbol*            "#$setq")
      (*km-showme-symbol*          "#$showme")
      (*km-showme-all-symbol*      "#$showme-all")
      (*km-showme-here-symbol*     "#$showme-here")
      (*km-show-bindings-symbol*   "#$show-bindings")
      (*km-show-context-symbol*    "#$show-context")
      (*km-trace-symbol*           "#$trace")
      (*km-untrace-symbol*         "#$untrace")
      (*km-write-kb*               "#$write-kb")
      ))
  
  (defparameter *km->cycl-cycl-symbols*
    '(
      (*cycl-true-symbol*          "#$True")
      (*cycl-false-symbol*         "#$False")
      (*cycl-not-symbol*           "#$not")
      (*cycl-and-symbol*           "#$and")
      (*cycl-or-symbol*            "#$or")
      (*cycl-xor-symbol*           "#$xor")
      (*cycl-implies-symbol*       "#$implies")
      (*cycl-equivalent-symbol*    "#$equivalent")
      (*cycl-forall-symbol*        "#$forAll")
      (*cycl-exists-symbol*        "#$thereExists")
      (*cycl-arg1-isa-symbol*      "#$arg1Isa")
      (*cycl-arg2-isa-symbol*      "#$arg2Isa")
      (*cycl-arg3-isa-symbol*      "#$arg3Isa")
      (*cycl-arg4-isa-symbol*      "#$arg4Isa")
      (*cycl-arg5-isa-symbol*      "#$arg5Isa")
      (*cycl-arity-symbol*         "#$arity")
      (*cycl-genls-symbol*         "#$genls")
      (*cycl-isa-symbol*           "#$isa")
      (*cycl-result-isa-symbol*    "#$resultIsa")
      (*cycl-collection-symbol*    "#$Collection")
      (*cycl-thing-symbol*         "#$Thing")
      ))

  (proclaim (cons 'special (mapcar #'car *km->cycl-km-symbols*)))
  (proclaim (cons 'special (mapcar #'car *km->cycl-cycl-symbols*))))

(defvar *cycl->kif-constants*)
(defvar *cycl->kif-functions*)

(defvar *km->cycl-initialized* nil)
(defvar *km->kif-initialized* nil)

(defun initialize-km->cycl ()
  (unless *km->cycl-initialized*
    (let ((*hash-dollar-package* (km-package)))
      (dolist (x *km->cycl-km-symbols*)
        (set (first x) (read-from-string (second x)))))
    (let ((*hash-dollar-package* (cycl-package)))
      (dolist (x *km->cycl-cycl-symbols*)
        (set (first x) (read-from-string (second x)))))
    (setf *km->cycl-initialized* t)))

(defun initialize-km->kif ()
  (unless *km->kif-initialized*
    (initialize-km->cycl)
    (setf *cycl->kif-constants*
          (list (cons *cycl-true-symbol* 'true)
                (cons *cycl-false-symbol* 'false)
                (cons *cycl-collection-symbol* 'class)
                (cons *cycl-thing-symbol* 'thing)))
    (setf *cycl->kif-functions*
          (list (cons *cycl-not-symbol* 'not)
                (cons *cycl-and-symbol* 'and)
                (cons *cycl-or-symbol* 'or)
                (cons *cycl-implies-symbol* '=>)
                (cons *cycl-equivalent-symbol* '<=>)
                (cons *cycl-arity-symbol* 'arity)
                (cons *cycl-genls-symbol* 'subclass-of)
                (cons *cycl-isa-symbol* 'instance-of)
                (cons *cycl-result-isa-symbol* 'range)))
    (setf *km->kif-initialized* t)))

(defun cycl->kif (form)
  (cond
   ((atom form)
    (or (cdr (assoc form *cycl->kif-constants*)) form))
   ((eq *cycl-xor-symbol* (first form))
    (list 'not (list '<=> (mapcar #'cycl->kif (rest form)))))
   ((eq *cycl-forall-symbol* (first form))
    (list* 'forall (list (second form)) (mapcar #'cycl->kif (rest (rest form)))))
   ((eq *cycl-exists-symbol* (first form))
    (list* 'exists (list (second form)) (mapcar #'cycl->kif (rest (rest form)))))
   ((eq *cycl-arg1-isa-symbol* (first form))
    (let ((v (mapcar #'cycl->kif (rest form))))
      (list* 'nth-domain (first v) 1 (rest v))))
   ((eq *cycl-arg2-isa-symbol* (first form))
    (let ((v (mapcar #'cycl->kif (rest form))))
      (list* 'nth-domain (first v) 2) (rest v)))
   ((eq *cycl-arg3-isa-symbol* (first form))
    (let ((v (mapcar #'cycl->kif (rest form))))
      (list* 'nth-domain (first v) 3) (rest v)))
   ((eq *cycl-arg4-isa-symbol* (first form))
    (let ((v (mapcar #'cycl->kif (rest form))))
      (list* 'nth-domain (first v) 4) (rest v)))
   ((eq *cycl-arg5-isa-symbol* (first form))
    (let ((v (mapcar #'cycl->kif (rest form))))
      (list* 'nth-domain (first v) 5) (rest v)))
   (t
    (cons (or (cdr (assoc (first form) *cycl->kif-functions*)) (first form))
          (mapcar #'cycl->kif (rest form))))))

(defun read-km->cycl-assertion-file (filespec &key verbose)
  ;; returns a list of calls on 'assertion' with CycL wffs as arguments
  ;; like read-cycl-assertion-file, but in this case the wffs are the
  ;; result of translating KM wffs in the file to CycL
  ;;
  ;; (map-cycl-data 'eval (extract-cycl-data cycl-assertions))
  ;; is the way to interpret and assert the result of this function
  (initialize-km->cycl)
  (mapcan (lambda (assertion)
	    (let* ((wff (assertion-wff assertion))
                   (options (append (rest (rest assertion)) 
				    ;(list :input-wff wff)
				    )))
	      (when verbose
		(format t "~3%#||CONVERTING FROM KM:")
		(let ((*print-pretty* t)
;;		      (*package* (km-package))
		      (*readtable* *hash-dollar-readtable*))
		  (terpri) (princ "   ") 
		  (princ wff)
		  )
		(format t "~%TO CYCL:||#"))
	      (mapcan (lambda (x)
			(when verbose
			  (let ((*print-pretty* t)
;;				(*package* (km-package))
				(*readtable* *hash-dollar-readtable*))
			    (terpri) (princ "   ") (princ x)))
                        (when x		;km->cycl bug produces nil assertions
			  (list (list* 'assertion x options))))
		      (km->cycl (list wff)))))
          (read-assertion-file
           filespec
           :package (km-package)
           :readtable *hash-dollar-readtable*)))

(defun read-km->kif-assertion-file (filespec &key verbose)
  (initialize-km->kif)
  (mapcar #'cycl->kif (read-km->cycl-assertion-file filespec :verbose verbose)))

(defun test-km-conversion (filespec &key verbose)
  (initialize)
  (use-cycl-symbols t)
  (declare-sort *cycl-collection-symbol*)
  (map-cycl-data
   (if verbose (lambda (x) (eval (print x))) #'eval)
   (extract-cycl-data (read-km->cycl-assertion-file filespec :verbose verbose))))

(defun km-test0 (&optional (verbose t))
  (test-km-conversion "nori:research:snark:temp.km"
                      :verbose verbose))

(defun km-test1 (&optional (verbose t))
  (test-km-conversion #+mcl "nori:research:snark:test-suite1.km"
                      #-mcl "~stickel/km/test-suite1.km"
                      :verbose verbose))

(defun km-test2 (&optional (verbose t))
  (test-km-conversion #+mcl "nori:research:snark:test-suite2.km"
                      #-mcl "~stickel/km/test-suite2.km"
                      :verbose verbose)
  (use-resolution)
  (prove '(forall (x) (implies (km::|Car| x) (exists (y) (and (km::|parts| x y) (km::|Engine| y)))))))

(defun km-test3 (&optional (verbose t))
  (test-km-conversion #+mcl "nori:research:snark:virus.km"
		      #-mcl "~stickel/km/virus.km"
		      :verbose verbose))

(defun km-test4 (&optional (verbose t))
  (test-km-conversion #+mcl "nori:research:snark:walk.km"
                      #-mcl"~stickel/km/walk.km"
                      :verbose verbose))
(defun test-km->kif ()
  (initialize-km->kif)
  (read-km->kif-assertion-file "nori:research:snark:temp.km"))



(defstruct trans
  km
  snark)

;; takes in a list of km statments; returns
;; a list of structs trans, for which trans-km is
;; the original km expression, and trans-snark is 
;; a _list_ of the equivalent expressions

(defvar base '())
(defvar vary '())
(defvar *declaration-mode* '())
(defvar slotlist '())
(defvar worker '())
(defvar current '())
(defvar counter '())
(defvar cholder '())
(defvar z1 '())
(defvar z2 '())
(defvar temp '())
(defvar andlst '())
(defvar all '())
(defvar special '())
(defvar temp2 '())
(defvar tempbase '())
(defvar fs-translated '())
(defvar temp1 '())
(defvar unholder '())
(defvar q '())
(defvar temp3 '())
(defvar holder '())
(defvar aritylst '())


(defun km->snark (lst)
  (ks-helper lst '()))

(defun ks-helper (lst newlst)
  (if (null lst)
      newlst
    (ks-helper (Cdr lst) 
	       (cons (make-trans :km (car lst)
				 :snark (my-map #'assert-proc (router (Car lst)))) newlst))))


(defun assert-proc (x)
  (list (list 'assertion x)))	;MES

;;km->cycL applies the translator to each of the elements of a list
;; (of km expressions)

(defun km->cycL (lst)
  (my-map #'router lst))

;;router determines which function will handle the translation
;; of the km input

(defun router (x)
  (progn
    (setf base 1)
    (setf vary "Y")
    (setf aritylst '())
    (cond ((atom x)	;MES
	   nil)
	  ((and (eql (car x) *km-every-symbol*) 
		(eql (third x) *km-has-symbol*))
	   (progn 
	     (setf *declaration-mode* t)
	     (setf slotlist '())
	     (setf worker (mn (every-> x 1)))
	     (append worker aritylst)))
	  ((eql (second x) *km-has-symbol*)
	   (slot-class x))
	  ((and (eql (car x) *km-every-symbol*) 
		(eql (third x) *km-has-definition-symbol*))
	   (setf *declaration-mode* t)
	   (setf temp (mn (every-def-> x 1)))
	   (append temp aritylst))
	  ((eql (car x) *km-a-symbol*)
	   (progn
	     (setf *declaration-mode* '())
	     (a-> x)))
	  ((and (eql (first x) *km-allof-symbol*) (eql (length x) 4))
	   (alloffunc x))
	  ((and (eql (first x) *km-allof-symbol*) (eql (length x) 6))
	   (allof-complicated-func x))
	  ((and (consp x) (eql (second x) *km-=-symbol*))
	   ())
	  ((and (consp x) (eql (first x) *km-if-symbol*))
	   (if-func x))
	  ((and (consp x) (eql (second x) *km-and-symbol*))
	   (if (eql (length x) 3) 
	       (append (router (car x)) (router (third x)))
	     (append (router (car x))
		     (router (cddr x)))))

)))


(defun if-func (x)
  (if (= (length x) 4)
      (list (cons
	     *cycl-implies-symbol*
	     (append (router (second x))
		     (router (fourth x)))))
    (list
     (list *cycl-and-symbol*
	   (list *cycl-implies-symbol*
		 (router (second x))
		 (router (fourth x)))
	   (list *cycl-implies-symbol*
		 (list *cycl-not-symbol*
		       (router (second x))
		       (router (sixth x))))))))




;;slot-class is used to decide whether a km expression
;; of the form (<expr> has <...) is a referring to
;; an instance or a class. it does this by checking the
;; first expression in the list of properies (instance-of 
;; vs. Superclasses). if <expr> is a slotname, it dispatches
;; to slot-print, which is an iterative procedure that returns
;; the desired cycL expression (similarly for Classes and class-print).

(defun slot-class (x)
  (cond ((and (eql (car (third x)) *km-instance-of-symbol*) 
	      ;(eql (first (second (third x))) *km-s\l\o\t-symbol*)
	      )
	 (slot-print x base))
	(T
	 (class-print x))))


(defun slot-print (lst base)
  (replace-tree
   (my-map
    #'(lambda (y)
	(setf aritylst (cons (list *cycl-arity-symbol* (car y) 2) aritylst))
	(mapcar #'(lambda (z) 
		     (proc2 z base (car y) (+ base 1)))
		 (cadr y)))
    (cddr lst))
   'cycl::?X1
   (first lst)))
  

  
(defun class-print (x)
  (append (list (list *cycl-isa-symbol* (car x) *cycl-collection-symbol*))
	  (my-map #'(lambda (y)
		      (my-map #'(lambda (z)
				  (class-print-helper 
				   (car y) z (car x)))
			      (cadr y)))
		  (cddr x))))

(defun class-print-helper (title value name)
   (cond
   ((eql title *km-superclasses-symbol*)
    (list 
     (list *cycl-genls-symbol* name value)))
   ((eql title *km-subclasses-symbol*)
    (list
     (list *cycl-isa-symbol* value name)))))
	

;;my-map2 is much like a normal mapping procedure, except
;; that it is specialized to pass the parameters we need, 
;; so that they do not have to be set, which causes problems
;; (if that makes any sense). 
;; it takes a procedure, a lst, a lst, a symbol, and an integer.


(defun my-map2 (proc items andlst title counter)
  (mapcar (lambda (item) (funcall proc item andlst title counter)) items))


(defun my-map (proc lst)
  (mapcan (lambda (item) (append (funcall proc item) nil)) lst))

;; varmaker is a procedure which takes an integer, n, and returns
;; the string (hoping to figure out how to make this a symbol)
;; "?xn"

(defun varmaker (count)
  (if *declaration-mode*
      (intern (format nil "?X~D" count) (cycl-package))		;MES
      (intern (format nil "a~D" count) (km-package))))

;; varmaker-self is necessary because when km uses 'Self', we need to
;; know whether we talking about variables or constants.

(defun varmaker-self (count)
  (if *declaration-mode*
      (intern (format nil "?X~D" count) (cycl-package))		;MES
      (intern (format nil "a~D" count) (km-package))))



;;mn is a maintenance procedure. the lists returned by my-map2 are 
;; often nested in unnessary one-element lists
;; --for example, (((x))) when we just want (x)
;; i haven't been able to figure out how to do this manually
;; -- i'm probably missing a car somewhere -- but until then, this works


(defun mn (x)
  (my-map #'make-nice x))


(defun make-nice (x)
  (if (not (consp x))
      x
    (if (= 1 (length x))
	(make-nice (car x))
      (if (not (or 
		(eql (first x) *cycl-implies-symbol*)
		(eql (first x) *cycl-equivalent-symbol*)))
	  (my-map #'make-nice x)
	(list x)))))


(setf current '())

(setf counter 1)

;; every-> is the function calle by router 
;; when it finds and (every <Class> has (..))
;; i takes a list of symbols in km and returns a list of lists
;; in cycL


(defun every-> (lst base)
  (mapcar
   #'(lambda (x)
       (list *cycl-implies-symbol* 
	     (list *cycl-isa-symbol* (varmaker base) (second lst))  x))
  (my-map
   #'(lambda (y)
       (setf aritylst (cons (list *cycl-arity-symbol* (car y) 2) aritylst))
       (mapcar #'(lambda (z) 
		    (proc2 z base (car y) (+ base 1)))
		(cadr y)))
   (cdddr lst)))
  
  )

;;every->def is essentially the same as every->, except it uses
;; 'equivalent' instead of 'implies'
;; this is for (every <Class> has-defintion...)

(defun every-def-> (lst base)
  (mapcar
   #'(lambda (x)
       (list *cycl-equivalent-symbol* 
	     (list *cycl-isa-symbol* (varmaker base) (second lst))  x))
   (my-map
    #'(lambda (y) 
	(mapcar #'(lambda (z) (proc2 z base (car y) (+ 1 base)))
		 (cadr y)))
    (cdddr lst)))
  )

(setf our-const 1)
 
;; a-> is for

(defun a-> (lst)
  (progn
    (setf counter 1)
    (setf cholder 1)
    (setf base 1)
    (if (eql (length lst) 2)
	(list (list *cycl-isa-symbol* (varmaker counter) (second lst)))
      (list (append (list *cycl-and-symbol* 
			  (list *cycl-isa-symbol* 
				(varmaker counter) (second lst)))
		    (my-map #'(lambda (x)
				(mapcar 
				 #'(lambda (y)
				     (progn
				       (setf counter (+ 1 counter))
				       (proc2 y cholder (car x)  counter)))
				 (cadr x)))
			    (cdddr lst)))))))


;; proc2 is the main procedure. because the treatment of certain km commands
;; varies depending on whether they are being called in teh context of
;; 'every' or not, we sometimes have dual functions... one called from router,
;; and one called from proc2. PUT AN EXAMPLE OF WHY THIS IS NECESSARY HERE

(defun proc2 (x cholder title counter)
   (cond 
    ((eql title *km-instance-of-symbol*)
     (if (eql x *km-s\l\o\t-symbol*)
	 (list *cycl-and-symbol*
	       (list *cycl-arity-symbol* (varmaker cholder) 2)
	       (list *cycl-isa-symbol* (varmaker cholder) x))
       (list *cycl-isa-symbol* (varmaker cholder) x)))
    ((eql x *km-self-symbol*)
     (list title (varmaker cholder) (varmaker base)))
    (t
     (case (test x)
       (a-simple
	  (progn
	    (setf z1 (list *cycl-isa-symbol* (varmaker  counter) (second x)))
	    (setf z2 (list title (varmaker cholder) (varmaker  counter)))
	   (if *declaration-mode*
	       (list *cycl-exists-symbol*  (varmaker  counter)
		     (list *cycl-and-symbol* z1 z2))
	     (list *cycl-and-symbol* z1 z2))))
    (simple
     (list title (varmaker cholder) x))
    (a-cont
     (setf temp (list title (varmaker cholder) 
                      (varmaker counter)))
     (setf cholder counter)
     (if *declaration-mode*
	   (list *cycl-exists-symbol*  (varmaker  counter)
		 (append (list *cycl-and-symbol* 
			       (list *cycl-isa-symbol* 
				     (varmaker counter) (second x))
			       temp)
			 (my-map #'(lambda (x)
				     (mapcar 
				      #'(lambda (y)
					  (progn
					    (setf counter (+ 1 counter))
					    (proc2 y cholder (car x)  
						   counter)))
				      (cadr x)))
				 (cdddr x))))
	   (append (list *cycl-and-symbol*)
		    (list (list *cycl-isa-symbol* 
				(varmaker counter) (second x))
			  temp)
		    (my-map #'(lambda (x)
				(mapcar 
				 #'(lambda (y)
				     (progn
				       (setf counter 
					     (+ 1 counter))
				       (proc2 y cholder (car x)  
					      counter)))
				 (cadr x)))
			    (cdddr x)))))
	
	(mba
	   (setf temp (list title (varmaker cholder) 
			    (varmaker counter)))
	   (setf cholder counter)
	   (list *cycl-forall-symbol* (varmaker counter)
		 (list *cycl-implies-symbol*
		       temp
		       (append (list *cycl-and-symbol*)
			       (list (list *cycl-isa-symbol* 
					   (varmaker counter) (second x)))
			       
			       (my-map #'(lambda (x)
					   (mapcar 
					    #'(lambda (y)
						(progn
						  (setf counter 
							(+ 1 counter))
						  (proc2 y cholder (car x)  
							 counter)))
					    (cadr x)))
				       (cdddr x))))))
	(the-of
	   (setf vary (concatenate 'string vary "Y"))
	   (setf unholder '())
	   (setf temp2 (the-func x '() counter))
	   (setf (cdr (my-last unholder))
		 (list (list *cycl-implies-symbol*
		       (append (list *cycl-and-symbol*)
			       temp2)
		       (list title
			     (varmaker cholder)
			     (varmaker2 counter)))))
	   (car unholder))
	(Self
	 (if (= (length x) 1)
	     (list title (varmaker cholder) (varmaker base))
	   (proc2 (make-the *km-self-symbol* (cdr x)) cholder title counter)))
	(e-with
	 (progn
	   (setf tempbase counter)
	   (list *cycl-forall-symbol* (varmaker counter)
		 (list 
		  *cycl-implies-symbol*
		  (cons *cycl-and-symbol*
			(cons 
			 (list 
			  *cycl-isa-symbol* (varmaker counter) (second x))
			  (my-map
			   #'(lambda (y) 
			       (mapcar #'(lambda (z) 
					    (progn
					   (proc2 z tempbase (car y) 
						  (setf counter 
							(+ counter 1)))))
					(cadr y)))
			   (cdddr x))))))))
	(allof-simple
	 (let ((firstsort (second x))
	       (secondsort (fourth x)))
	   (setf unholder '())
	   (setf fs-translated (the-func firstsort '() counter))
	   (setf it (varmaker2 counter)) ;; added this line, might cause probs?
	   (setf q (it-func secondsort '() counter it))
	   (setf (cdr (my-last unholder)) 
		 (list 
		  (list *cycl-implies-symbol* 
			(cons *cycl-and-symbol*  (append  fs-translated q))
			(list title (varmaker cholder) it))))
	   (car unholder)))
	(ifthen
	 (if (eql (length x) 6)
	     (progn
	       (setf unholder '())
	       (setf temp1 (proc2 (second x) cholder title counter))
	       (setf vary (concatenate 'string vary "yyy"))
	       (setf temp2 (proc2 (fourth x) cholder title counter))
	       (list 
		*cycl-implies-symbol*
		temp1
		temp2))
	   'here))
	 
	(==
	 (setf unholder '())
	 (if (consp (third x))
	     (progn
	       (setf temp1 (the-func (first x) unholder counter))
	       ;;changed this 8-9
	       (setf vary (concatenate 'string vary "Y"))
	       (setf temp2 (the-func (third x) unholder counter))
	       (list unholder
		     (list
		      *cycl-equivalent-symbol*
		      temp1
		      temp2)))
	   (progn
	     (setf temp1 (the-func (first x) unholder counter))
	     (list 
	      (list
	       *cycl-implies-symbol*
	       temp1
	       (list 'figure 'this 'out))))))
	(notf
	 (cons *km-not-symbol*
	       (proc2 (second x) cholder title counter)))
	(andf
	 (cons *cycl-and-symbol*
	       (list (proc2 (first x) cholder title counter)
		     (proc2 (third x) cholder title counter))))
	(orf
	 (cons *cycl-or-symbol*
	       (append (proc2 (first x) cholder title counter)
		       (proc2 (third x) cholder title counter))))
	(isa
	 (setf temp (proc2 (first x) cholder title counter))
	 (cons *cycl-and-symbol* 
	       (cons (list *cycl-isa-symbol* (varmaker2 counter) (third x)) 
		     temp)))
	(forall-term
	 ())
	(allof-complex
	 (car (allof-complicated-func x)))
	(triple
	 (setf unholder '())
	 (cond ((and (consp (second x)) (consp (fourth x)))
		(progn
		  (setf temp1 (the-func (second x) '() counter))
		  (setf vary (concatenate 'string vary "Y"))
		  (setf temp2 (the-func (fourth x) '() counter))
		  (setf (cdr (my-last unholder))
			(list (list
			       *cycl-implies-symbol*
			       (append (list *cycl-and-symbol*)
				    temp1
				    temp2)
			       (list title (varmaker cholder) 
				     (list *km-triple-symbol*
					   (car (last (first temp1))) 
				   (third x) 
				   (car (last (first temp2))))))))
		  (car unholder)))
	       ((and (consp (second x)))
		(progn
		  (setf temp1 (the-func (second x) '() counter))
		  (setf vary (concatenate 'string vary "Y"))
		  (setf (cdr (my-last unholder))
			(list (list
			       *cycl-implies-symbol*
			       (append (list *cycl-and-symbol*)
				    temp1)
			       (list title (varmaker cholder) 
				     (list *km-triple-symbol*
					   (car (last (first temp1))) 
				   (third x) 
				   (fourth x))))))
		  (car unholder)))
	       ((and (consp (fourth x)))
		(progn
		  (setf temp2 (the-func (fourth x) '() counter))
		  (setf (cdr (my-last unholder))
			(list (list
			       *cycl-implies-symbol*
			       (append (list *cycl-and-symbol*)
				       temp2)
			       (list title (varmaker cholder) 
				     (list *km-triple-symbol*
					   (second x)
					   (third x) 
					   (car (last (first temp2))))))))
		  (car unholder)))
	       (T
		(list title (varmaker cholder)
		      (list *km-triple-symbol*
			    (second x)
			    (third x)
			    (fourth x))))))
	(mnba
	  (progn 
	   (setf temp (list title (varmaker cholder) 
			    (varmaker counter)))
	   (setf cholder counter)
	   (list *cycl-forall-symbol* (varmaker counter)
		 (list *cycl-implies-symbol*
		       temp
		       (list *cycl-not-symbol*
			     (append (list *cycl-and-symbol*)
				     (list (list *cycl-isa-symbol* 
						 (varmaker counter) (second x)))
				     
			       (my-map #'(lambda (x)
					   (mapcar 
					    #'(lambda (y)
						(progn
						  (setf counter 
							(+ 1 counter))
						  (proc2 y cholder (car x)  
							 counter)))
					    (cadr x)))
				       (cdddr x))))))))
	(oneof
         (setf unholder '())
         (setf fs-translated (the-func firstsort '() counter))
	 (let ((firstsort (second x))
	       (secondsort (fourth x)))
	    (if (eql secondsort *km-true-symbol*)
		(progn
		  (setf it (varmaker2 counter)) 
		  (setf unholder (third (translate-forall->exists unholder)))
		  (setf (cdr (last (my-last2 unholder)))
			(list 
			 (cons *cycl-and-symbol*  
			       (append  fs-translated 
					(list 
					 (list 
					  title (varmaker cholder) it))))))
		  
		  unholder)
	      (progn
		(setf it (varmaker2 counter)) ;; added this line, might cause probs?
		(setf q (it-func secondsort '() counter it))
		(setf unholder (third (translate-forall->exists unholder)))
		(setf (cdr (last (my-last2 unholder)))
		      (list 
		       (cons *cycl-and-symbol*  
			     (append  fs-translated q
				      (list (list title (varmaker cholder) it))))))
		
		unholder))))
	(the+
	 (proc2 (cons *km-a-symbol* (cdr x)) cholder title counter))
	(&&
	 (if (eql (length x) 3)
	     (cons *cycl-and-symbol*
		   (cons
		    (proc2 (car (first x)) cholder title counter)
		    (list (proc2 (car (third x)) cholder title counter))))
	  (progn
	    (format t "hre")
	    (cons *cycl-and-symbol*
	     (cons
	      (proc2 (car (first x)) cholder title counter)
	      (list (proc2 (cddr x) cholder title counter)))))))
        (otherwise
         (LIST 'ERRRRRRRRRRRRRRRORRRRRRRRRRRRRRRRRRRR (IF (ATOM X) X (FIRST X))))
))))
	 



;;allof doesn't really make sense on its own as a concept yet
;; once i figure out how to make sets, it should have a more concrete
;; meaning

(defun alloffunc (x)
  (let ((firstsort (second x))
	(secondsort (fourth x)))
    (setf unholder '())
    (setf fs-translated (the-func firstsort '() counter))
    (setf q (it-func secondsort '() counter (varmaker2 counter)))
    (setf (cdr (my-last unholder)) 
	 (list (cons *cycl-and-symbol*  (append  fs-translated q))))
    unholder))


#| 
allof-complicated-func takes an allof expression of the form

(allof <expr1> [where <expr0>] must <expr2>)

|#

(defun allof-complicated-func (x)
  (setf it (varmaker2 counter))
  (setf unholder '())
  (setf temp1 (the-func (second x) '() counter))
  (setf temp2 (it-func (fourth x) '() counter it))
  (setf temp3 (it-func (sixth x) '() counter it))
  (list
  (list *cycl-not-symbol*
	(list *cycl-exists-symbol*
	      (varmaker2 counter)
	      unholder
	      (cons *cycl-and-symbol*
		    (append 
		;     (the-func (second x) '() counter)
		;     (it-func (fourth x) '() counter it)
		     temp1 temp2
		     (list (cons
			    *cycl-not-symbol*
			    (list 
			     (cons 
			      *cycl-and-symbol*
			      ;(it-func (sixth x) '() counter it)
			      temp3
			      ))))))))))

  

(defun it-func (x lst counter it)
  (cond ((eql (first x) *km-it-symbol*)
	 (list (list *cycl-isa-symbol* it (third x))))
	((eql (second x) *km-=-symbol*)
	 (progn
	   (setf vary (concatenate 'string vary "y"))
	   (if (eql (car (last (first x))) *km-it-symbol*)
	       (list (list (second (first x)) it (third x)))
	     (progn
	       (setf temp (the-func (car (last (first x))) '()  counter))
	       (setf (second (nth (- (length  temp) 1) temp)) it)
	       (cons (list (nth (- (length (first x)) 3) (first x))
			   (varmaker2 counter)
			   (third x))
		     temp)))))
	((eql (second x) *km-isa-symbol*)
	 (setf vary (concatenate 'string vary "y"))
      	 (setf holder (list *cycl-isa-symbol*
			    (varmaker2 counter)
			    (third x)))
	 (setf temp (the-func (first x) '() counter))
	 (setf (second (nth (- (length temp) 1) temp)) it)
	 (cons holder temp))
	((eql (second x) *km-and-symbol*)
	 (append
	       (it-func (first x) '() counter it)
	       (it-func (third x) '() counter it)
	       ))))
		   
		  
	    

(defun make-the (newlst lst)
  (if (null lst)
      newlst
    (if (eql 1 (length lst))
        (list *km-the-symbol* (car lst) *km-of-symbol* newlst)
      (make-the (list *km-the-symbol* (second lst) (first lst) 
		      *km-of-symbol* newlst) (cddr lst)))))




(defun the-func (x lst counter)
  (progn 
    (setf unholder (list (append 
			  (list 
			   *cycl-forall-symbol* 
			   (varmaker2 counter)) unholder)))
    (cond
     ((eql (first x) *km-a-symbol*)
      (append 
       lst
       (list (list *cycl-isa-symbol* (varmaker2 counter) (second x)))))
     ((eql (third x) *km-of-symbol*)
      (cond ((and (consp (fourth x))
		(not (eql (length (fourth x)) 1)))
	     (if (eql (first (fourth x)) *km-self-symbol*)
		 (the-func (make-the *km-self-symbol* (cdr (fourth x)))
			   (append lst
				   (list (list (second x) 
					       (varmaker2 (+ 1 counter)) 
					       (varmaker2  counter)))) 
			   (+ 1 counter))
	       
	       (the-func 
		(fourth x)
	      (append lst
		      (list (list (second x) 
				  (varmaker2 (+ 1 counter)) 
				(varmaker2 counter)))) 
	      (+ 1 counter))))
	  ((or
	    (eql (fourth x) *km-self-symbol*) 
	    (and (consp (fourth x)) (eql (length (fourth x)) 1)))
	   (append lst 
		   (list (list (second x) (varmaker-self base) (varmaker2 counter)))))
	  (T
	   (append lst
		   (list (list (second x) (fourth x) (varmaker2 counter)))))))
   
   ((eql (third x) *km-with-symbol*)
    (append lst (the-with (cdddr x) '() (+ 1 counter))))
   ((eql (fourth x) *km-of-symbol*)
    (cond ((and (consp (fifth x))
	    (not (eql (length (fifth x)) 1)))
	   (if (eql (first (fifth x)) *km-self-symbol*)
	       (the-func (make-the *km-self-symbol* (cdr (fifth x)))
			 (append 
			  lst 
			  (list (list *cycl-isa-symbol* 
				      (varmaker2 counter) (second x)))
			  (list (list (third x) (varmaker2 (+ 1 counter))
				      (varmaker2 counter))))
			 (+ 1 counter))
	     (the-func (fifth x)
		       (append lst 
			       (list (list *cycl-isa-symbol*
					   (varmaker2 counter) (second x)))
			       (list (list (third x) (varmaker2 (+ 1 counter))
					   (varmaker2 counter))))
		       (+ 1 counter))))
	  (T
	   (append lst (list (list *cycl-isa-symbol* 
				   (varmaker2 counter) (second x)))
		   (list (list (third x) 
			       (varmaker-self base) 
			       (varmaker2 counter))))))))))
			    
   

  
(defun the-with (x lst counter)
  (if (null (cdr x))
      (append lst
	      (list (list *cycl-isa-symbol* (varmaker2 counter) 
			  *cycl-thing-symbol*))
	      (list (list (caar x) (varmaker2 counter) 
			  (the-func (cadar x) '() (+ 1 counter)))))
    (the-with 
     (cdr x) 
     (append lst
	     (list (list *cycl-isa-symbol* 
			 (varmaker2 counter) *cycl-thing-symbol*))
	     (list (list (caar x) (varmaker2 counter) 
			 (the-func (cadar x) '() (+ 1 counter)))))
     (+ 1 counter))))


;;equaltest


(defun equaltest (x)
  (cond ((eql x *km-=-symbol*)
	 'kmequal)
	((eql x *km-and-symbol*)
	 'kmand)
	((eql x *km-or-symbol*)
	 'kmor)))


;;test


(defun test (x)
  (cond ((and (not (eql x *km-self-symbol*)) (not (consp x)))
	 'simple)
        ((and (consp x) (= 2 (length x)) (eql (first x) *km-a-symbol*))
         'a-simple)
        ((and (consp x) (eql (first x) *km-a-symbol*) 
	      (eql (third x) *km-with-symbol*))
         'a-cont)
        ((and (consp x) (eql (first x) *km-the-symbol*))
         'the-of)
	((and (consp x) (eql (first x) *km-must-be-a-symbol*))
	 'mba)
	((and (consp x) (eql (first x) *km-self-symbol*))
	 'Self)
	((and (consp x) (eql (first x) *km-every-symbol*)
	      (eql (third x) *km-with-symbol*)) 
	 'e-with)
	((and (consp x) (eql (first x) *km-the-symbol*) 
	      (eql (third x) *km-with-symbol*))
	 'e-with)
	((and (consp x) (= (length x) 4)
	      (eql (first x) *km-allof-symbol*)
	      (eql (third x) *km-where-symbol*))
	 'allof-simple)
	((and (consp x) (eql (first x) *km-forall-symbol*))
	 'forall-term)
	((and (consp x) (= (length x) 6) (eql (first x) *km-allof-symbol*))
	 'allof-complex)
	((and (consp x) (eql (first x) *km-if-symbol*))
	 'ifthen)
	((and (consp x) (eql (second x) *km-=-symbol*))
	 '==)
	((and (consp x) (eql (first x) *km-not-symbol*))
	 'notf)
	((and (consp x) (eql (second x) *km-and-symbol*))
	 'andf)
	((and (consp x) (eql (second x) *km-isa-symbol*))
	 'isa)
	((and (consp x) (eql (first x) *km-triple-symbol*))
	 'triple)
	((and (consp x) (eql (first x) *km-mustnt-be-a-symbol*))
	 'mnba)
	((and (consp x) (eql (first x) *km-oneof-symbol*))
	 'oneof)
	((and (consp x) (eql (first x) *km-the+-symbol*))
	 'the+)
	((and (consp x) (eql (first x) *km-a+-symbol*))
	 'the+) ;; a+ and the+ are synonyms
	((and (consp x) (eql (second x) *km-&&-symbol*))
	 '&&)
))


(setf a '())


(defun translate-forall->exists (x)
  (if (not (consp (car (last x))))
      (list *cycl-exists-symbol*  (second x))
    (cons *cycl-exists-symbol* 
	  (cons  (second x) 
		(list (translate-forall->exists (car (last x))))))))



;; return-deepest-nested is a specialty function, used only
;; in oneof.. where to overwrite the last existentially quantified
;; variable in the list (because in oneof we want to assert its existence
;; instead).

(defun return-deepest-nested (x)
  (if (not (consp (car (last (car (last x))))))
      x
    (return-deepest-nested (car (last x)))))





(defun varmaker2 (count)
  (intern (format nil "?Y~D-~D" (length vary) count) (cycl-package)))	;MES

;; finds the outermost list s.t. the last member of the list
;; is not a list

(defun my-last (x)
  (if (consp (car (last x)))
      (my-last (car (last x)))
    (last x)))

(defun my-last2 (x)
  (if (= (length x) 2)
      x
    (my-last2 (car (last x)))))

(defun replace-tree (tree old new)
  (if (null tree)
      nil
    (if (not (consp (car tree)))
	(if (eql (car tree) old)
	    (cons new (replace-tree (cdr tree) old new))
	  (cons (car tree) (replace-tree (cdr tree) old new)))
      (cons
       (replace-tree (car tree) old new)
       (replace-tree (cdr tree) old new)))))
  

#|
7-27  every-with
7-27 the-with
7-27 pondered if..then -- don't think it's possible, talk to mark
7-27 considered the functions of p.22 in km guide
      <allof, oneof,forall,allof..must,theoneof>
     they all seem really similar -- should think carefully about
     a core form that will translate easily to all of them

7-31 finished allof-simple
8-1  thoughts on all-of-complex : it is a test, and therefore
     left off working on a-o-c.. make sure it works in cases of small It
   ((the color of It) = Red). actually, know it doesn't, so fix it...
8-2 finished all-of-complex as it's own function, need to incorp into proc2
8-3 did if...then, not, and, or and the rather tricky ==
8-3 wrote if.. then as its own function, as it has a different meaning
    when outside an every expression
8-3 worked on forall
8-4 lots of testing, worked on triple, looked over the papers vinay 
    gave me
8-7 finished triple, checking out the walking axioms..
8-7 got arity completely working (it was assinge every literal an arity
    throught ... has)
8-8 finished must-be-a
8-8 finished mustnt-be-a
8-8 finished oneof.. where
8-8 finished the+ 
8-8 goals for tomorrow:  /=, includes, isa-superset-of <- will have
    to use limited definition of a set
8-9 worked on questions, 
8-10 mucho examples! vinay sent me 6 example kbs, playing with those
8-14 worked more on the examples, which led me to deal with &&, a+,
     moer possibilites for "the"

|#

;;; km-cycl.lisp EOF
