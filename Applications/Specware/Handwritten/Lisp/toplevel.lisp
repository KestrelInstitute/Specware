(in-package :user)
(defpackage :SpecCalc)

;; These are Stephen's toplevel Lisp aliases for Specware

;; The lisp code supporting the saving/restoring of the Specware state
;; to/from the lisp environment can be found in specware-state.lisp.
;; The latter must be loaded before this and the generated lisp code for
;; Specware.

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

(top-level:alias ("swl" :case-sensitive) (x &optional y)
  (swl (string x) (and y (maybe-add-extension (string y) ".lisp"))))

;; the 'x' is for experimental.
(top-level:alias ("swx" :case-sensitive) (x) (swx (string x)))
(defun swx (x) (Specware::evaluateURIfromLisp (string x)))
