(in-package :user)

;; These are Stephen's toplevel Lisp aliases for Specware

(defun sw (x) (Specware::runSpecwareURI (fix_URI x)))

(top-level:alias ("sw" :case-sensitive) (x) (sw (string x)))

(defvar *specware-environment* SpecCalc::initialSpecwareState)

(defun sw-re-init ()
  (setq *specware-environment* SpecCalc::initialSpecwareState))

(top-level:alias "sw-init" () (sw-re-init))

(defun swe (x)
  (let ((result (Specware::runSpecwareURIenv (fix_URI x) *specware-environment*)))
    (setq *specware-environment* (cdr result))
    (let ((pV11 (car result))) 
      (block 
	  nil 
	(if (eq (car pV11) :|Ok|) 
	    (return nil) 
	  (if (eq (car pV11) :|Exception|) 
	      (return "Specware toplevel handler failed")))
	(error "Nonexhaustive match failure in Specware.runSpecwareURI")))))

(top-level:alias ("swe" :case-sensitive) (x) (swe (string x)))

(defun swl (x &optional y)
  (let ((result (Specware::compileSpecwareURIenv (fix_URI x)
						 (if y
						     (cons :|Some| y)
						   '(:|None|))
						 *specware-environment*)))
    (setq *specware-environment* (cdr result))
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
(defun fix_URI (uri)
  (let ((end? (- (length uri) 3)))
    (if (string-equal uri ".sw" :start1 end?)
	(subseq uri 0 end?)
      uri)))

(defun maybe-add-extension (str ext)
  (if (find #\. str)
      str
    (concatenate 'string str ext)))

