
(defpackage :STRING-SPEC)
(IN-PACKAGE :STRING-SPEC)


;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.  [This wasn't true for concat-1 at least, so I restored its definition here.]

;;; Added various declarations to quiet down cmucl.
;;; See Decls.lisp for definition of macro named THE-STRING.

(defun |!length| (x)
  (declare (type lisp:simple-base-string x))
  (the lisp:fixnum 
    (array-dimension x 0)))

(defun concat (x y)
  (declare (type lisp:simple-base-string x y))
  (the lisp:simple-base-string 
    (concatenate 'string x y)))

(defun concat-1 (x)
  (declare (cons x))
  (the lisp:simple-base-string 
    (concatenate 'string 
		 (the lisp:simple-base-string (car x)) 
		 (the lisp:simple-base-string (cdr x)))))

(defun |!++| (x y)
  (declare (type lisp:simple-base-string x y))
  (the lisp:simple-base-string 
    (concatenate 'string x y)))

;;; (defun |!++|-1 (x)
;;;    (concatenate 'string (car x) (cdr x)))

(defun ^ (x y)
  (declare (type lisp:simple-base-string x y))
  (the lisp:simple-base-string 
    (concatenate 'string x y)))


;;; (defun ^-1 (x)
;;;    (concatenate 'string (car x) (cdr x)))

(defun toScreen (x)
  (declare (type lisp:simple-base-string x))
  (common-lisp::format t "~A" x))

(defun writeLine (x)
  (declare (type lisp:simple-base-string x))
  (common-lisp::format t "~A" x)
  (common-lisp::format t "~%"))

(defconstant newline
  (format nil "~c" #\newline))

;;; (defun newline (ignore)
;;;   (declare (ignore ignore))
;;;   newline)
;;; 
;;; (defun |!map| (fn) 
;;;    #'(lambda (s) 
;;;        (map 'string fn s)))

(defun |!map-1-1| (fn s) 
  (map 'string fn s))

;;; (defun all (fn) 
;;;    #'(lambda (s) 
;;;        (null (find-if (lambda (ch) (not (funcall fn ch))) s))))
;;; (defun all-1-1 (fn s) 
;;;   (null (find-if (lambda (ch) (not (funcall fn ch))) s)))

(defun sub (s n)
  (declare (type lisp:simple-base-string s) (type lisp:fixnum n))
  (elt s n))

;;; (defun sub-1 (s)
;;;     (elt (car s) (cdr s)))

(defun substring (s start end)
  (declare (type lisp:simple-base-string s) (type lisp:fixnum start end))
  (the lisp:simple-base-string (subseq s start end)))

;;; (defun substring-1 (x)
;;;     (subseq (svref x 0) (svref x 1) (svref x 2)))    

(defun explode (s) 
  ;; convert string to list
  (reduce #'cons s :from-end t :initial-value nil))

(defun implode (s) 
  (apply #'concatenate 
	 (cons 'string
	       (mapcar #'string s))))

;;; ; This is errorneous:
;;; ;(defun translate (f) 
;;; ;   #'(lambda (s) 
;;; ;       (apply #'concatenate 
;;; ;	(cons 'string
;;; ;	     (map 'string (lambda (ch) (funcall f ch)) s)))))
;;; 
;;; (defun translate (f) 
;;;    #'(lambda (s) 
;;;        (let* ((se (explode s))
;;; 	      (ses (mapcar #'(lambda (ch) (string (funcall f ch))) se)))
;;; 	 (apply #'concatenate (cons 'string ses)))))

(defun translate-1-1 (f s) 
  (let* ((chars (explode s))
	 (translated-char-strings (mapcar #'(lambda (ch) (string (funcall f ch)))
					  chars)))
    (declare (type list translated-chars))
    (the lisp:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))

(defun leq (s1 s2)
  (declare (type lisp:simple-base-string s1 s2))
  ;; result is fixnum or nil
  (string<= s1 s2))

;;; (defun leq-1 (x)  (string<= (car x) (cdr x)))

(defun lt (s1 s2)
  (declare (type lisp:simple-base-string s1 s2))
  ;; result is fixnum or nil
  (string< s1 s2))

;;; (defun lt-1 (x)  (string< (car x) (cdr x)))
;;; 
;;; ;;;(defun compare (s1 s2) 
;;; ;;;    (if (string< s1 s2)
;;; ;;;	(list :|Less|)
;;; ;;;	(if (string= s1 s2)
;;; ;;;	    (list :|Equal|)
;;; ;;;	  (list :|Greater|))))
;;; 
;;; (defun compare (s1 s2) 
;;;   (if (string= s1 s2)
;;;       '(:|Equal|)
;;;     (if (string< s1 s2)
;;; 	'(:|Less|)
;;;       '(:|Greater|))))
;;; (defun compare-1 (x) (compare (car x) (cdr x)))

(defun concatList (x)
  (the lisp:simple-base-string 
    (apply #'concatenate 'string x)))

;;; #| Tests:
;;; (funcall (all #'(lambda (ch) (isUpperCase ch))) "asdFasdf")
;;; (funcall (all #'(lambda (ch) (isUpperCase ch))) "REWR")
;;; (map 'string (lambda (ch) (toLowerCase ch)) "SDFeF")
;;; |#
;;; 
