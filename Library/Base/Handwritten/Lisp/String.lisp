
(defpackage :STRING-SPEC)
(IN-PACKAGE :STRING-SPEC)

(defun |!length| (x)
   (array-dimension x 0))

(defun concat (x y)
   (concatenate 'string x y))
(defun concat-1 (x)
   (concatenate 'string (car x) (cdr x)))

(defun |!++| (x y)
   (concatenate 'string x y))
(defun |!++|-1 (x)
   (concatenate 'string (car x) (cdr x)))

(defun ^ (x y)
   (concatenate 'string x y))
(defun ^-1 (x)
   (concatenate 'string (car x) (cdr x)))

(defun toScreen (x)
  (lisp::format t "~A" x))

(defun writeLine (x)
  (lisp::format t "~A" x)
  (lisp::format t "~%"))

(defconstant newline
  (format nil "~c" #\newline))

(defun newline (ignore)
  (declare (ignore ignore))
  newline)

(defun |!map| (fn) 
   #'(lambda (s) 
       (map 'string fn s)))
(defun |!map-1-1| (fn s) 
  (map 'string fn s))


(defun all (fn) 
   #'(lambda (s) 
       (null (find-if (lambda (ch) (not (funcall fn ch))) s))))
(defun all-1-1 (fn s) 
  (null (find-if (lambda (ch) (not (funcall fn ch))) s)))

(defun sub (s n)
    (elt s n))
(defun sub-1 (s)
    (elt (car s) (cdr s)))

(defun substring (s start end)
    (subseq s start end))
(defun substring-1 (x)
    (subseq (svref x 0) (svref x 1) (svref x 2)))    

(defun explode (s) 
  (reduce #'cons s :from-end t :initial-value nil))

(defun implode (s) 
  (apply #'concatenate 
	 (cons 'string
	       (mapcar 'string s))))

; This is errorneous:
;(defun translate (f) 
;   #'(lambda (s) 
;       (apply #'concatenate 
;	(cons 'string
;	     (map 'string (lambda (ch) (funcall f ch)) s)))))

(defun translate (f) 
   #'(lambda (s) 
       (let* ((se (explode s))
	      (ses (mapcar #'(lambda (ch) (string (funcall f ch))) se)))
	 (apply #'concatenate (cons 'string ses)))))
(defun translate-1-1 (f s) 
  (let* ((se (explode s))
	 (ses (mapcar #'(lambda (ch) (string (funcall f ch))) se)))
    (apply #'concatenate (cons 'string ses))))

	 
(defun leq (s1 s2)  (string<= s1 s2))
(defun leq-1 (x)  (string<= (car x) (cdr x)))

(defun lt (s1 s2)  (string< s1 s2))
(defun lt-1 (x)  (string< (car x) (cdr x)))

;;;(defun compare (s1 s2) 
;;;    (if (string< s1 s2)
;;;	(list :|Less|)
;;;	(if (string= s1 s2)
;;;	    (list :|Equal|)
;;;	  (list :|Greater|))))

(defun compare (s1 s2) 
  (if (string= s1 s2)
      '(:|Equal|)
    (if (string< s1 s2)
	'(:|Less|)
      '(:|Greater|))))
(defun compare-1 (x) (compare (car x) (cdr x)))

(defun concatList (x) (apply 'concatenate 'string x))

#| Tests:
(funcall (all #'(lambda (ch) (isUpperCase ch))) "asdFasdf")
(funcall (all #'(lambda (ch) (isUpperCase ch))) "REWR")
(map 'string (lambda (ch) (toLowerCase ch)) "SDFeF")
|#
