(in-package :user)

;; These are functions / variables related to the saving/restoring of
;; the Specware state to/from the lisp environment.  This must be loaded
;; before the generated lisp code for Specware, since when the latter is
;; loaded, it initializes the state by calling a function below.

;; It might be better to provide a single function to set lisp vars from
;; within Specware. Essentially a call to setq. Provided it was wrapped
;; inside a state monad, there would be no problem with referential
;; transparency. How would one declare the variable? Would it be an op?

(defpackage "SPECCALC")
(defpackage "SPECWARE")

(defvar *specware-global-context* nil)
(defun specware-state ()
  (vector *specware-global-context*
      (svref SpecCalc::initialSpecwareState 1)
      (svref SpecCalc::initialSpecwareState 2)))

(defun SPECWARE::saveSpecwareState (glob loc optUri)
  (SPECWARE::saveSpecwareState-1 (vector glob loc optUri)))

(defun SPECWARE::saveSpecwareState-1 (State)
  (setq user::*specware-global-context* (svref State 0))
  (cons '(:|Ok|) State))

(defun SPECWARE::restoreSavedSpecwareState (globalContext localContext optURI)
  (SPECWARE::restoreSavedSpecwareState-1 (vector globalContext localContext optURI)))

(defun SPECWARE::restoreSavedSpecwareState-1 (State)
  (cons '(:|Ok|)
     (vector *specware-global-context*
	         (svref SpecCalc::initialSpecwareState 1)
	         (svref SpecCalc::initialSpecwareState 2))))

;; When the following boolean is true, then all exceptions (not just Fail)
;; take the user into the Lisp debugger.
(defvar SpecCalc::specwareWizard? nil)
