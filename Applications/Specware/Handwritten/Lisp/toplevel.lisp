(in-package :user)
(defpackage :SpecCalc)

;; Toplevel Lisp aliases for Specware

;; The lisp code supporting the saving/restoring of the Specware state
;; to/from the lisp environment can be found in specware-state.lisp.
;; The latter must be loaded before this and the generated lisp code for
;; Specware.

(defvar *last-uri-loaded* nil)
(defvar *last-swl-args* nil)

(defun sw0 (x)
   (Specware::runSpecwareURI x))
(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defun sw-re-init ()
   (setq *specware-global-context* nil))
(top-level:alias "sw-init" () (sw-re-init))

(defun list-loaded-units ()
   (Specware::listLoadedUnits))
(top-level:alias ("list" :case-sensitive) () (list-loaded-units))

(defun sw (x)
   (Specware::evaluateURI_fromLisp x))

(top-level:alias ("sw" :case-sensitive) (&optional x)
  (if x
    (sw (setq *last-uri-loaded* (string x)))
    (if *last-uri-loaded*
      (sw *last-uri-loaded*)
      (format t "No previous unit evaluated~%"))))

(defun show (x)
   (Specware::evaluatePrint_fromLisp x))
(top-level:alias ("show" :case-sensitive) (&optional x)
  (if x
    (show (setq *last-uri-loaded* (string x)))
    (if *last-uri-loaded*
      (show *last-uri-loaded*)
      (format t "No previous unit evaluated~%"))))

;; Not sure if an optional URI make sense for swl
(defun swl (x &optional y)
   (Specware::evaluateLispCompile_fromLisp x
                         (if y (cons :|Some| y)
                               '(:|None|))))
(top-level:alias ("swl" :case-sensitive) (&optional &rest args)
   (let ((r-args (if (not (null args))
		     args
		   *last-swl-args*)))
   (if r-args
       (progn (setq *last-swl-args* args)
	      (funcall 'swl (string (first r-args))
		       (if (not (null (second r-args)))
			   (string (second r-args)) nil)))
     (format t "No previous unit evaluated~%"))))

(top-level:alias ("wiz" :case-sensitive) (&optional (b nil b?))
   (if b? (princ (setq SpecCalc::specwareWizard? b))
          (princ SpecCalc::specwareWizard?)))

(top-level:alias ("swpath" :case-sensitive) (&optional str)
  (if (null str)
      (princ (sys:getenv "SWPATH"))
    (princ (setf (sys:getenv "SWPATH") (string str)))))
