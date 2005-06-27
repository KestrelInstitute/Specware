(defpackage "SYSTEM-SPEC")
(defpackage "STRING-SPEC")
(IN-PACKAGE "STRING-SPEC")


;;; For each curried binary op in the spec String whose Lisp code is
;;; hand-written, there are two Lisp functions. One takes the first argument
;;; and returns a closure that takes the second argument, the other takes the
;;; two arguments in non-curried form. These double variants match Specware's
;;; Lisp code generator, which generates various variants for curried ops:
;;; each variant takes some of the curried arguments and returns a closure
;;; that takes the remaining arguments. For a curried binary op, the naming
;;; convention is that the variant that takes the first argument and return a
;;; closure has the name directly derived from the op, while the variant that
;;; takes the two arguments has that name with a "-1-1" suffix.

;;; For each (non-curried) binary op in the spec String whose Lisp code is
;;; hand-written, there are also two Lisp functions. See the comments in
;;; Integer.lisp for an explanation.


(defun explode (s) 
  ;; (reduce #'cons s :from-end t :initial-value nil)) ; ugh... uses generic sequence functions to treat string as list, then rebuilds list
  (coerce s 'list) ; let lisp do something smart
  )

(defun implode (s) 
  ;; (apply #'concatenate (cons 'string (mapcar #'string s))) ; brain damage -- hugely inefficient
  (coerce s 'string) ; let lisp do something smart
  )

(defun |!length| (x)
  (declare (type cl:simple-base-string x))
  (the cl:fixnum 
    (array-dimension x 0)))

(defun concat-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro concat-2 (x y)
  `(concatenate 'string ,(if (stringp x) x `(the cl:simple-base-string ,x)) ,y))

(defun concat (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun ++-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro ++-2 (x y)
  `(concatenate 'string ,(if (stringp x) x `(the cl:simple-base-string ,x))
		,y))

(defun |!++| (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun ^-2 (x y)
  (declare (type cl:simple-base-string x y))
  (the cl:simple-base-string 
    (concatenate 'string x y)))

;;; Putting (the cl:simple-base-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro ^-2 (x y)
  `(concatenate 'string ,x ,(if (stringp y) y `(the cl:simple-base-string ,y))))

(defun ^ (xy)
  (declare (cons xy))
  (the cl:simple-base-string 
    (concatenate 'string 
                 (the cl:simple-base-string (car xy)) 
                 (the cl:simple-base-string (cdr xy)))))

(defun |!map| (f)
  (lambda (s)
    (map 'string f (the cl:simple-base-string s))))

(defun map-1-1 (f s)
  (map 'string f (the cl:simple-base-string s)))

(defun |!exists| (p)
  (lambda (s)
    (some p s)))

(defun exists-1-1 (p s)
  (some p s))

(defun all (p)
  (lambda (s)
    (every p s)))

(defun all-1-1 (p s)
  (every p s))

(defun sub-2 (s n)
  (declare (type cl:simple-base-string s) (type cl:fixnum n))
  (elt s n))

(defun sub (sn)
  (declare (cons sn))
  (elt (the cl:simple-base-string (car sn)) (the cl:fixnum (cdr sn))))

(defun substring-3 (s start end)
  (declare (type cl:simple-base-string s) (type cl:fixnum start end))
  (the cl:simple-base-string (subseq s start end)))

(define-compiler-macro substring-3 (s start end)
  `(subseq
     (the cl:simple-base-string ,s) (the cl:fixnum ,start) (the cl:fixnum ,end)))

(defun substring (sse)
  (the cl:simple-base-string (subseq (the cl:simple-base-string (svref sse 0))
                                     (the cl:fixnum (svref sse 1))
                                     (the cl:fixnum (svref sse 2)))))

(defun concatList (x)
  (the cl:simple-base-string 
    (apply #'concatenate 'string x)))

(defun translate (f)
  (lambda (str)
    (let* ((chars (explode str))
           (translated-char-strings 
            (mapcar #'(lambda (ch) 
                        (string (funcall f ch)))
                    chars)))
      (declare (type list translated-char-strings))
      (the cl:simple-base-string 
        (apply #'concatenate 'string translated-char-strings)))))

(defun translate-1-1 (f str)
  (let* ((chars (explode str))
         (translated-char-strings 
          (mapcar #'(lambda (ch) 
                      (string (funcall f ch)))
                  chars)))
    (declare (type list translated-char-strings))
    (the cl:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))

(defun lt-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string< s1 s2) t nil))

(defun lt (s1s2)
  (if (string< (the cl:simple-base-string (car s1s2))
               (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun leq-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string<= s1 s2) t nil))

(defun leq (s1s2)
  (if (string<= (the cl:simple-base-string (car s1s2))
                (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun <-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string< s1 s2) t nil))

(define-compiler-macro <-2 (x y)
  `(string< (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun |!<| (s1s2)
  (if (string< (the cl:simple-base-string (car s1s2))
               (the cl:simple-base-string (cdr s1s2)))
   t nil))

(defun <=-2 (s1 s2)
  (declare (type cl:simple-base-string s1 s2))
  (if (string<= s1 s2) t nil))

(define-compiler-macro <=-2 (x y)
  `(string<= (the cl:simple-base-string ,x) (the cl:simple-base-string ,y)))

(defun |!<=| (s1s2)
  (if (string<= (the cl:simple-base-string (car s1s2))
                (the cl:simple-base-string (cdr s1s2)))
   t nil))

(define-compiler-macro >-2 (x y)
  `(let ((x ,x) (y ,y))
     (string< (the cl:simple-base-string y) (the cl:simple-base-string x))))

(define-compiler-macro >=-2 (x y)
  `(let ((x ,x) (y ,y))
     (string<= (the cl:simple-base-string y) (the cl:simple-base-string x))))

(defparameter newline
  (format nil "~c" #\newline))

(defun toScreen (x)
  (declare (type cl:simple-base-string x))
  (common-lisp::format t "~A" x))

(defun writeLine (x)
  (declare (type cl:simple-base-string x))
  (common-lisp::format t "~A" x)
  (common-lisp::format t "~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :BOOLEAN-SPEC)
(IN-PACKAGE :BOOLEAN-SPEC)


(defun toString (x)
  (if x "true" "false"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :INTEGER-SPEC)
(IN-PACKAGE :INTEGER-SPEC)


(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun intToString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun stringToInt (s)
  (declare (type string s))
  (multiple-value-bind (n new-index)
      (parse-integer s :junk-allowed t)
    (cond ((null n)
	   (System-Spec::fail 
	    (format nil "stringToInt could not parse ~S" 
		    s)))
	  ((< new-index (length s))
	   (System-Spec::fail
	    (format nil "stringToInt found ~D, but also extra junk in ~S" 
		    n s)))
	  ((let ((c0 (char s 0))) 
	     (or (digit-char-p c0) 
		 (eq c0 #\-)))
	   (the integer n))
	  (t
	   (System-Spec::fail
	    (format nil "stringToInt: leading ~:C in ~S is not allowed"
		    (char s 0) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :NAT-SPEC)
(IN-PACKAGE :NAT-SPEC)


(defun toString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun natToString (x)
  (declare (type integer x))
  (the string (princ-to-string x)))

(defun stringToNat (s)
  (declare (type string s))
  ;; lisp automatically returns the first value as a normal value
  (multiple-value-bind (n new-index)
      (parse-integer s :junk-allowed t)
    (cond ((null n)
	   (System-Spec::fail
	    (format nil "stringToNat could not parse ~S" 
		    s)))
	  ((< new-index (length s))
	   (System-Spec::fail
	    (format nil "stringToNat found ~D, but also extra junk in ~S" 
		    n s)))
	  ((digit-char-p (char s 0))
	   (the integer n))
	  (t
	   (System-Spec::fail
	    (format nil "stringToNat: leading ~:C in ~S is not allowed"
		    (char s 0) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(DEFPACKAGE :CHAR-SPEC)
(IN-PACKAGE :CHAR-SPEC)


(defun toString (x)
  (string x))
