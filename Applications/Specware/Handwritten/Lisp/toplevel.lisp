(in-package :user)
(defpackage :SpecCalc)

;; These are Stephen's toplevel Lisp aliases for Specware

(defun fix_URI (uri)
  (let ((end? (- (length uri) 3)))
    (if (and (>= end? 0) (string-equal uri ".sw" :start1 end?))
	(subseq uri 0 end?)
      uri)))

(defun maybe-add-extension (str ext)
  (if (find #\. str)
      str
    (concatenate 'string str ext)))

(defun sw0 (x) (Specware::runSpecwareURI (fix_URI x)))

(top-level:alias ("sw0" :case-sensitive) (x) (sw0 (string x)))

(defvar *specware-global-context* nil)
(defun specware-state ()
  (vector *specware-global-context*
	  (svref SpecCalc::initialSpecwareState 1)
	  (svref SpecCalc::initialSpecwareState 2)))

(defun sw-re-init ()
  (setq *specware-global-context* nil))

(top-level:alias "sw-init" () (sw-re-init))

(defun sw (x)
  (let ((result (Specware::runSpecwareURIenv (fix_URI x) (specware-state))))
    (setq *specware-global-context* (svref (cdr result) 0))
    (let ((pV11 (car result))) 
      (block 
	  nil 
	(if (eq (car pV11) :|Ok|) 
	    (return nil) 
	  (if (eq (car pV11) :|Exception|) 
	      (return "Specware toplevel handler failed")))
	(error "Nonexhaustive match failure in Specware.runSpecwareURI")))))

(top-level:alias ("sw" :case-sensitive) (x) (sw (string x)))

(defun swl (x &optional y)
  (let ((result (Specware::compileSpecwareURIenv (fix_URI x)
						 (if y
						     (cons :|Some| y)
						   '(:|None|))
						 (specware-state))))
    (setq *specware-global-context* (svref (cdr result) 0))
    (let ((pV11 (car result))) 
      (block 
	  nil 
	(if (eq (car pV11) :|Ok|) 
	    (return nil) 
	  (if (eq (car pV11) :|Exception|) 
	      (return pV11)))
	(error "Nonexhaustive match failure in Specware.runSpecwareURI")))))


(defpackage "SPECWARE")

(defun SPECWARE::saveSpecwareState (glob loc optUri)
  (SPECWARE::saveSpecwareState-1 (vector glob loc optUri)))

(defun SPECWARE::saveSpecwareState-1 (State)
  (setq user::*specware-environment* State)
  (cons '(:|Ok|) State))