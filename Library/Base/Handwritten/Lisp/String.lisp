
(defpackage :STRING-SPEC)
(IN-PACKAGE :STRING-SPEC)


;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.  [This wasn't true for concat-1 at least, so I restored its definition here.]

;;; Added various declarations to quiet down cmucl.

(defun |!length| (x)
  (declare (type cl:simple-base-string x))
  (the cl:fixnum (cl:length x)))

(define-compiler-macro |!length| (x)
  `(cl:length (the cl:simple-base-string ,x)))

(defun concat-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

(define-compiler-macro concat-2 (x y)
  `(concatenate 'string (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun concat (x)
  (declare (cons x))
  (the cl:simple-base-string 
    (concatenate 'string 
		 (the cl:simple-base-string (car x)) 
		 (the cl:simple-base-string (cdr x)))))

(defun ++-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

(define-compiler-macro ++-2 (x y)
  `(concatenate 'string (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

;;; (defun |!++|-1 (x)
;;;    (concatenate 'string (car x) (cdr x)))

(defun ^-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))


;;; (defun ^-1 (x)
;;;    (concatenate 'string (car x) (cdr x)))

(defun toScreen (x)
  (declare (type cl:simple-base-string x))
  (cl:format t "~A" x))

(defun writeLine (x)
  (declare (type cl:simple-base-string x))
  (cl:format t "~A" x)
  (cl:format t "~%"))

(defconstant newline
  (format nil "~c" #\newline))

;;; (defun newline (ignore)
;;;   (declare (ignore ignore))
;;;   newline)
;;; 
;;; (defun |!map| (fn) 
;;;    #'(lambda (s) 
;;;        (map 'string fn s)))

(defun map-1-1 (fn s) 
  (map 'string fn s))

;;; (defun all (fn) 
;;;    #'(lambda (s) 
;;;        (null (find-if (lambda (ch) (not (funcall fn ch))) s))))
;;; (defun all-1-1 (fn s) 
;;;   (null (find-if (lambda (ch) (not (funcall fn ch))) s)))

(defun sub-2 (s n)
  (declare (type cl:simple-base-string s) (type cl:fixnum n))
  (elt s n))

(define-compiler-macro sub-2 (s n)
  `(elt (the cl:simple-base-string ,s) (the cl:fixnum ,n)))

(defun sub (s)
  (elt (car s) (cdr s)))

(defun substring-3 (s start end)
  (declare (type cl:simple-base-string s) (type cl:fixnum start end))
  (the cl:simple-base-string (subseq s start end)))

(define-compiler-macro substring-2 (s start end)
  `(subseq (the cl:simple-base-string ,s) (the cl:fixnum ,start) (the cl:fixnum ,end)))

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

(defun translate-1-1 (f str)
  (let* ((chars (explode str))
	 (translated-char-strings 
	  (mapcar #'(lambda (ch) 
		      ;; prototypical call from specId in SpecToLisp.lisp :
		      ;; let id = translate (fn #| -> "\\|" | ## -> "\\#" | ch -> Char.toString ch) id
		      ;; e.g., this will translate some special chars (vertical-bar and hash-mark)
		      ;; into two-character strings:
		      ;;   #\|   =>   "\\!"
		      ;;   #\#   =>   "\\#"      
		      ;; and other chars to one-character strings:
		      ;;   #\A   =>   "A"
		      ;;   ...
		      ;; Note that in this prototypical case, the result of the 
		      ;; funcall is already a string, so the call to string here 
		      ;; is just the identity (i.e., result is EQ to arg).
		      (string (funcall f ch)))
		  chars)))
    (declare (type list translated-char-strings))
    (the cl:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))

(defun leq-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  ;; result is fixnum or nil
  (string<= s1 s2))

(define-compiler-macro leq-2 (x y)
  `(string<= (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun leq (x)  (string<= (car x) (cdr x)))

(defun lt-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  ;; result is fixnum or nil
  (string< s1 s2))

(define-compiler-macro lt-2 (x y)
  `(string< (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun lt (x)  (string< (car x) (cdr x)))
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
  (the cl:simple-base-string 
    (apply #'concatenate 'string x)))

;;; #| Tests:
;;; (funcall (all #'(lambda (ch) (isUpperCase ch))) "asdFasdf")
;;; (funcall (all #'(lambda (ch) (isUpperCase ch))) "REWR")
;;; (map 'string (lambda (ch) (toLowerCase ch)) "SDFeF")
;;; |#
;;; 
