(in-package :user)
(defpackage :SpecCalc)

;; Toplevel Lisp aliases for Specware

;; The lisp code supporting the saving/restoring of the Specware state
;; to/from the lisp environment can be found in specware-state.lisp.
;; The latter must be loaded before this and the generated lisp code for
;; Specware.

(defun sw0 (x)
   (Specware::runSpecwareURI x))
(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun sw-re-init ()
   (setq *specware-global-context* nil))
(top-level:alias "sw-init" () (sw-re-init))

(defun sw (x)
   (Specware::evaluateURI_fromLisp x))
(top-level:alias ("sw" :case-sensitive) (x) (sw (string x)))

(defun swl (x &optional y)
   (Specware::evaluateLispCompile_fromLisp x
                         (if y (cons :|Some| y)
                               '(:|None|))))
(top-level:alias ("swl" :case-sensitive) (x &optional y)
   (swl (string x) (if y (string y) nil)))

(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
   (if b? (setq SpecCalc::specwareWizard? b)
           (princ SpecCalc::specwareWizard?)))

(top-level:alias ("swpath" :case-sensitive) (&optional str)
  (if (null str)
      (princ (sys:getenv "SWPATH"))
    (princ (setf (sys:getenv "SWPATH") (string str)))))
