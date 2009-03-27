(defpackage :SpecToLisp)
(defpackage :System-Spec)
(defpackage :String-Spec)
(in-package :String-Spec)

(defvar SpecToLisp::SuppressGeneratedDefuns nil) ; note: defvar does not redefine if var already has a value

(setq SpecToLisp::SuppressGeneratedDefuns
      (append '("STRING-SPEC::implode"
                "STRING-SPEC::explode"
                "STRING-SPEC::|!length|"
                "STRING-SPEC::|@-2|"
                "STRING-SPEC::|@|"
                "STRING-SPEC::sub-2"
                "STRING-SPEC::sub"
                "STRING-SPEC::subFromTo-3"
                "STRING-SPEC::subFromTo"
                "STRING-SPEC::++-2"
                "STRING-SPEC::|!++|"
                "STRING-SPEC::forall?-1-1"
                "STRING-SPEC::forall?"
                "STRING-SPEC::exists?-1-1"
                "STRING-SPEC::exists?|"
                "STRING-SPEC::map-1-1"
                "STRING-SPEC::|!map|"
                "STRING-SPEC::flatten"
                "STRING-SPEC::translate-1-1"
                "STRING-SPEC::translate"
                "STRING-SPEC::compare-2"
                "STRING-SPEC::compare"
                "STRING-SPEC::<-2"
                "STRING-SPEC::|!<|"
                "STRING-SPEC::<=-2"
                "STRING-SPEC::|!<=|"
                "STRING-SPEC::newline"
                "STRING-SPEC::toScreen"
                "STRING-SPEC::writeLine"
                "BOOLEAN-SPEC::show"
                "INTEGER-SPEC::intToString"
                "INTEGER-SPEC::stringToInt"
                "NAT-SPEC::natToString"
                "NAT-SPEC::stringToNat"
                "CHAR-SPEC::show"
                "String-Spec::implode"
                "String-Spec::explode"
                "String-Spec::|!length|"
                "String-Spec::@-2"
                "String-Spec::|!@|"
                "String-Spec::sub-2"
                "String-Spec::sub"
                "String-Spec::subFromTo-3"
                "String-Spec::subFromTo"
                "String-Spec::++-2"
                "String-Spec::|!++|"
                "String-Spec::forall?-1-1"
                "String-Spec::forall?"
                "String-Spec::exists?-1-1"
                "String-Spec::exists?"
                "String-Spec::map-1-1"
                "String-Spec::|!map|"
                "String-Spec::flatten"
                "String-Spec::translate-1-1"
                "String-Spec::translate"
                "String-Spec::compare-2"
                "String-Spec::compare"
                "String-Spec::<-2"
                "String-Spec::|!<|"
                "String-Spec::<=-2"
                "String-Spec::|!<=|"
                "String-Spec::newline"
                "String-Spec::toScreen"
                "String-Spec::writeLine"
                "Boolean-Spec::show"
                "Integer-Spec::intToString"
                "Integer-Spec::stringToInt"
                "Nat-Spec::natToString"
                "Nat-Spec::stringToNat"
                "Char-Spec::show")
              SpecToLisp::SuppressGeneratedDefuns))


;;; For each curried binary op, there are two Lisp functions. One takes the
;;; first argument and returns a closure that takes the second argument, the
;;; other takes the two arguments in non-curried form. These double variants
;;; match Specware's Lisp code generator, which generates various variants for
;;; curried ops: each variant takes some of the curried arguments and returns a
;;; closure that takes the remaining arguments. For a curried binary op, the
;;; naming convention is that the variant that takes the first argument and
;;; return a closure has the name directly derived from the op, while the
;;; variant that takes the two arguments has that name with a "-1-1" suffix.

;;; For each (non-curried) binary op, there are also two Lisp functions. See the
;;; comments in Integer.lisp for an explanation.


(defun implode (s) 
 (coerce s 'string))

(defun explode (s) 
 (coerce s 'list))

(defun |!length| (x)
 (declare (type cl:simple-string x))
 (the cl:fixnum 
   (array-dimension x 0)))

(defun @-2 (s n)
 (declare (type cl:simple-string s) (type cl:fixnum n))
 (elt s n))

(define-compiler-macro @-2 (s n)
  `(elt (the cl:simple-string ,s) (the cl:fixnum ,n)))

(defun |!@| (sn)
 (declare (cons sn))
 (elt (the cl:simple-string (car sn)) (the cl:fixnum (cdr sn))))

(defun sub-2 (s n)
 (declare (type cl:simple-string s) (type cl:fixnum n))
 (elt s n))

(define-compiler-macro sub-2 (s n)
  `(elt (the cl:simple-string ,s) (the cl:fixnum ,n)))

(defun sub (sn)
 (declare (cons sn))
 (elt (the cl:simple-string (car sn)) (the cl:fixnum (cdr sn))))


(defun subFromTo-3 (s start end)
 (declare (type cl:simple-string s) (type cl:fixnum start end))
 (the cl:simple-string (subseq s start end)))

(define-compiler-macro subFromTo-3 (s start end)
 `(subseq
    (the cl:simple-string ,s) (the cl:fixnum ,start) (the cl:fixnum ,end)))

(defun subFromTo (sse)
 (the cl:simple-string (subseq (the cl:simple-string (svref sse 0))
                                    (the cl:fixnum (svref sse 1))
                                    (the cl:fixnum (svref sse 2)))))

(defun ++-2 (x y)
 (declare (type cl:simple-string x y))
 (the cl:simple-string 
   (concatenate 'string x y)))

;;; Putting (the cl:simple-string ,y) gives mcl exponential compiler behavior
(define-compiler-macro ++-2 (x y)
 `(concatenate 'string ,(if (stringp x) x `(the cl:simple-string ,x))
               ,y))

(defun |!++| (xy)
 (declare (cons xy))
 (the cl:simple-string 
   (concatenate 'string 
                (the cl:simple-string (car xy)) 
                (the cl:simple-string (cdr xy)))))

(defun forall? (p)
 (lambda (s)
   (every p s)))

(defun forall?-1-1 (p s)
 (every p s))

(defun exists? (p)
 (lambda (s)
   (some p s)))

(defun exists?-1-1 (p s)
 (some p s))

(defun |!map| (f)
 (lambda (s)
   (map 'string f (the cl:simple-string s))))

(defun map-1-1 (f s)
 (map 'string f (the cl:simple-string s)))

(defun flatten (x)
 (the cl:simple-string 
   (apply #'concatenate 'string x)))

(defun translate (f)
 (lambda (str)
   (let* ((chars (explode str))
          (translated-char-strings 
           (mapcar #'(lambda (ch) 
                       (string (funcall f ch)))
                   chars)))
     (declare (type list translated-char-strings))
     (the cl:simple-string 
       (apply #'concatenate 'string translated-char-strings)))))

(defun translate-1-1 (f str)
 (let* ((chars (explode str))
        (translated-char-strings 
         (mapcar #'(lambda (ch) 
                     (string (funcall f ch)))
                 chars)))
   (declare (type list translated-char-strings))
   (the cl:simple-string 
     (apply #'concatenate 'string translated-char-strings))))

(defun String-Spec::compare-2 (s1 s2)
 (if (string< s1 s2)
     '(:|Less|)
     (if (string< s2 s1) '(:|Greater|) '(:|Equal|))))

(defun String-Spec::compare (s1s2)
 (String-Spec::compare-2 (car s1s2) (cdr s1s2)))

(defun <-2 (s1 s2)
 (declare (type cl:simple-string s1 s2))
 (if (string< s1 s2) t nil))

(define-compiler-macro <-2 (x y)
 `(string< (the cl:simple-string ,x) (the cl:simple-string ,y)))

(defun |!<| (s1s2)
 (if (string< (the cl:simple-string (car s1s2))
              (the cl:simple-string (cdr s1s2)))
  t nil))

(defun <=-2 (s1 s2)
 (declare (type cl:simple-string s1 s2))
 (if (string<= s1 s2) t nil))

(define-compiler-macro <=-2 (x y)
 `(string<= (the cl:simple-string ,x) (the cl:simple-string ,y)))

(defun |!<=| (s1s2)
 (if (string<= (the cl:simple-string (car s1s2))
               (the cl:simple-string (cdr s1s2)))
  t nil))

(define-compiler-macro >-2 (x y)
 `(let ((x ,x) (y ,y))
    (string< (the cl:simple-string y) (the cl:simple-string x))))

(define-compiler-macro >=-2 (x y)
 `(let ((x ,x) (y ,y))
    (string<= (the cl:simple-string y) (the cl:simple-string x))))

(defparameter newline
 (format nil "~c" #\newline))

(defun toScreen (x)
 ;; Note: (format t ...) goes to *standard-output*
 ;;    but (princ ... t) goes to *terminal-io*
 ;; Confusing, but that's the standard...
 ;; We want *standard-output* so it can be redirected (e.g., by the test suite)
 (declare (type cl:simple-string x))
 (princ x *standard-output*)
 (force-output *standard-output*))

(defun writeLine (x)
 ;; Note: (format t ...) goes to *standard-output*
 ;;    but (princ ... t) goes to *terminal-io*
 ;; Confusing, but that's the standard...
 ;; We want *standard-output* so it can be redirected (e.g., by the test suite)
 (declare (type cl:simple-string x))
 (princ x *standard-output*)
 (terpri *standard-output*)
 (force-output *standard-output*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :Boolean-Spec)
(in-package :Boolean-Spec)


(defun show (x)
 (if x "true" "false"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpackage :Integer-Spec)
(in-package :Integer-Spec)


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

(defpackage :Nat-Spec)
(in-package :Nat-Spec)


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

(defpackage :Char-Spec)
(in-package :Char-Spec)


(defun show (x)
 (string x))
