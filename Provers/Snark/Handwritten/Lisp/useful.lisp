;;; -*- Mode: LISP; Syntax: Common-Lisp; Package: mes -*-
;;; File: useful.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :mes)

(defmacro definline (name lambda-list &body body)
  `(progn 
     (defun ,name ,lambda-list ,@body)
     (define-compiler-macro ,name (&rest arg-list)
       (cons '(lambda ,lambda-list ,@body) arg-list))))

#+lucid
(defmacro lambda (&rest args)
  `(function (lambda ,@args)))

(defparameter float-internal-time-units-per-second (float internal-time-units-per-second))

(defmacro carc (x)
  `(car (the cons ,x)))

(defmacro cdrc (x)
  `(cdr (the cons ,x)))

(defmacro caarcc (x)
  `(carc (carc ,x)))

(defmacro cadrcc (x)
  `(carc (cdrc ,x)))

(defmacro cdarcc (x)
  `(cdrc (carc ,x)))

(defmacro cddrcc (x)
  `(cdrc (cdrc ,x)))

(defmacro neq (x y)
 `(not (eq ,x ,y)))

(defmacro neql (x y)
  `(not (eql ,x ,y)))

(defmacro nequal (x y)
  `(not (equal ,x ,y)))

(defmacro nequalp (x y)
  `(not (equalp ,x ,y)))

(defmacro dotails ((var listform &optional resultform) &body body)
  ;; dotails is just like dolist except the variable is bound
  ;; to successive tails instead of successive elements of the list
  `(do ((,var ,listform (rest ,var)))
       ((endp ,var)
        ,resultform)
     ,@body))

(defmacro dopairs ((var1 var2 listform &optional resultform) &body body)
  ;; (dopairs (x y '(a b c)) (print (list x y))) prints (a b), (a c), and (b c)
  ;; doesn't handle declarations in body correctly
  (let ((l1 (gensym)) (l2 (gensym)) (loop (gensym)))
    `(do ((,l1 ,listform) ,var1 ,var2 ,l2)
         ((endp ,l1)
          ,resultform)
       (setf ,var1 (pop ,l1))
       (setf ,l2 ,l1)
       ,loop
       (unless (endp ,l2)
         (setf ,var2 (pop ,l2))
         ,@body
         (go ,loop)))))

(definline iff (x y)
  (eq (not x) (not y)))

(defmacro implies (x y)
  `(or (not ,x) ,y))

(defmacro lcons (a* b* ab)
  ;; (lcons a* b* ab) does lazy cons of a* and b*
  ;; lcons does not evaluate a* or b* and returns nil if ab is nil
  ;; lcons does not evaluate b* and treats it as nil if (cdr ab) is nil
  ;; lcons returns ab if a* = (car ab) and b* = (cdr ab)
  ;; otherwise, lcons conses a* and b*
  ;;
  ;; lcons is useful for writing functions that map over lists
  ;; and return a modified list without unnecessary consing
  ;; for example, the following applies a substitution to a list of terms
  ;; (defun instantiate-list (terms subst)
  ;;   (lcons (instantiate-term (first terms) subst)
  ;;          (instantiate-list (rest terms) subst)
  ;;          terms))
  (assert (symbolp ab))
  (let ((tempa (gensym)) (tempb (gensym)) (tempa* (gensym)) (tempb* (gensym)))
    (setf a* (sublis (list (cons `(car ,ab) tempa)
                           (cons `(carc ,ab) tempa)
			   (cons `(first ,ab) tempa)
			   (cons `(nth 0 ,ab) tempa))
		     a*
		     :test #'equal))
    (setf b* (sublis (list (cons `(cdr ,ab) tempb)
                           (cons `(cdrc ,ab) tempb)
			   (cons `(rest ,ab) tempb)
			   (cons `(nthcdr 1 ,ab) tempb))
		     b*
		     :test #'equal))
    `(if (null ,ab)
	 nil
	 (let* ((,tempa (car ,ab))
		(,tempa* ,a*)
		(,tempb (cdrc ,ab)))
	   (if (null ,tempb)
	       (if (eql ,tempa ,tempa*)
		   ,ab
		   (list ,tempa*))
	       (let ((,tempb* ,b*))
		 (if (and (eq ,tempb ,tempb*)
			  (eql ,tempa ,tempa*))
		     ,ab
		     (cons ,tempa* ,tempb*))))))))

(defmacro setq-once (var form)
  ;; return value of var if non-nil
  ;; otherwise set var to value of form and return it
  `(or ,var (setq ,var ,form) (error "setq-once value is nil.")))

(definline assoc/eq (item alist)
  #+lucid (assoc item alist)			;depending on the implementation,
  #-lucid (assoc item alist :test #'eq)		;specifying EQ can make assoc faster
  )

(defmacro unroll-assoc (n item a-list)
  (cond
    ((<= n 0)
     `(assoc ,item ,a-list))
    (t
     (let ((x (gensym)))
       `(let ((,x ,item))
	  ,(unroll-assoc1 n x a-list))))))

(defmacro unroll-assoc/eq (n item a-list)
  (cond
    ((<= n 0)
     `(assoc/eq ,item ,a-list))
    (t
     (let ((x (gensym)))
       `(let ((,x ,item))
	  ,(unroll-assoc/eq1 n x a-list))))))

(defun unroll-assoc1 (n item a-list)
  (let ((l (gensym)))
    `(let ((,l ,a-list))
       (and ,l
	    ,(cond
	       ((<= n 0)
		`(assoc ,item ,l))
	       (t
		(let ((p (gensym)))
		  `(let ((,p (car ,l)))
		     (if (eql ,item (car ,p))
			 ,p
			 ,(unroll-assoc1 (1- n) item `(cdr ,l)))))))))))

(defun unroll-assoc/eq1 (n item a-list)
  (let ((l (gensym)))
    `(let ((,l ,a-list))
       (and ,l
	    ,(cond
	       ((<= n 0)
		`(assoc/eq ,item ,l))
	       (t
		(let ((p (gensym)))
		  `(let ((,p (car ,l)))
		     (if (eq ,item (car ,p))
			 ,p
			 ,(unroll-assoc/eq1 (1- n) item `(cdr ,l)))))))))))

#+lucid
(defmacro declaim (&rest declaration-specifiers)
  (list* 'eval-when
	 '(compile load eval)
	 (mapcar (lambda (x) `(proclaim ',x)) declaration-specifiers)))

#+lucid
(defmacro constantly (object)
  (function (lambda (&rest args)
	      (declare (ignore args))
	      object)))

(defun kwote (x)
  (list 'quote x))

(definline mklist (x)
  (if (listp x) x (list x)))

(defun firstn (list num)
  ;; return a new list that contains the first num elements of list
  (declare (type integer num))
  (cond
   ((or (eql 0 num) (atom list))
    nil)
   (t
    (cons (first list) (firstn (rest list) (1- num))))))

(defun consn (x y num)
  (declare (type integer num))
  ;; cons x and y n times
  ;; (cons 'a '(b) 3) = (a a a b)
  (dotimes (dummy num)
    (declare (type integer dummy) (ignorable dummy))
    (push x y))
  y)

(defun cons-unless-nil (x &optional y)
  ;; returns y if x is nil, otherwise returns (cons x y)
  ;; if y is omitted: returns nil if x is nil, otherwise (list x)
  (if (null x)
      y
      (cons x y)))

(defun list-p (x)
  ;; if x is a null terminated list, return its length
  ;; otherwise return nil
  (let ((n 0))
    (declare (type integer n))
    (loop
      (cond
	((null x)
	 (return n))
	((atom x)
	 (return nil))
	(t
	 (incf n)
	 (setf x (rest x)))))))

(defun same-length-p (x y)
  ;; test whether two lists are the same length
  (loop
    (cond
      ((endp x)
       (return (endp y)))
      ((endp y)
       (return nil))
      (t
       (setf x (rest x))
       (setf y (rest y))))))

(defun integers-between (low high)
  (let ((i high)
	(result nil))
    (loop
      (when (< i low)
	(return result))
      (push i result)
      (decf i))))

(defun percentage (m n)
  (values (round (* 100 m) n)))

(defun print-time (year month date hour minute second
                   &optional (destination *standard-output*) (basic nil))
  ;; per the ISO 8601 standard
  (format destination
          (if basic
              "~4D~2,'0D~2,'0DT~2,'0D~2,'0D~2,'0D"		;20020405T011216
              "~4D-~2,'0D-~2,'0DT~2,'0D:~2,'0D:~2,'0D")		;2002-04-05T01:12:16
          year month date hour minute second))

(defun print-universal-time (utime &optional (destination *standard-output*) (basic nil))
  (mvlet (((:values second minute hour date month year) (decode-universal-time utime)))
    (print-time year month date hour minute second destination basic)))

(defun print-current-time (&optional (destination *standard-output*) (basic nil))
  (print-universal-time (get-universal-time) destination basic))

(defun leap-year-p (year)
  (and (eql 0 (mod year 4))
       (implies (eql 0 (mod year 100))
                (eql 0 (mod year 400)))))

(defun days-per-month (month year)
  (case month
    ((1 3 5 7 8 10 12)
     31)
    ((4 6 9 11)
     30)
    (2
     (if (leap-year-p year) 29 28))))

(defun month-number (month)
  (cond
   ((or (symbolp month) (stringp month))
    (cdr (assoc (string month)
                '(("JAN" . 1) ("JANUARY" . 1)
                  ("FEB" . 2) ("FEBRUARY" . 2)
                  ("MAR" . 3) ("MARCH" . 3)
                  ("APR" . 4) ("APRIL" . 4)
                  ("MAY" . 5)
                  ("JUN" . 6) ("JUNE" . 6)
                  ("JUL" . 7) ("JULY" . 7)
                  ("AUG" . 8) ("AUGUST" . 8)
                  ("SEP" . 9) ("SEPTEMBER" . 9)
                  ("OCT" . 10) ("OCTOBER" . 10)
                  ("NOV" . 11) ("NOVEMBER" . 11)
                  ("DEC" . 12) ("DECEMBER" . 12))
                :test #'string-equal)))
   ((and (integerp month) (<= 1 month 12))
    month)
   (t
    nil)))

(defun print-args (&rest args)
  (declare (dynamic-extent args))
  (print args)
  nil)

(defvar *outputting-comment* nil)

(definline comment* (output-stream)
  (princ "; " output-stream)
  (setf *outputting-comment* t)	;not stream specific bug
  nil)

(definline nocomment* (output-stream)
  (declare (ignore output-stream))
  (setf *outputting-comment* nil))

(defun comment (&optional (output-stream *standard-output*))
  (unless *outputting-comment*
    (comment* output-stream)))

(defun nocomment (&optional (output-stream *standard-output*))
  (declare (ignorable output-stream))
  (nocomment* output-stream))

(defun terpri (&optional (output-stream *standard-output*))
  (cl:terpri output-stream)
  (nocomment* output-stream))

(defun terpri-comment (&optional (output-stream *standard-output*))
  (cl:terpri output-stream)
  (comment* output-stream))

(defvar *terpri-indent* 0)
(declaim (type fixnum *terpri-indent*))

(defun terpri-comment-indent (&optional (output-stream *standard-output*))
  (cl:terpri output-stream)
  (comment* output-stream)
  (dotimes (dummy *terpri-indent*)
    (declare (ignorable dummy)) 
    (princ " " output-stream)))

(defun terpri-indent (&optional (output-stream *standard-output*))
  (cl:terpri output-stream)
  (nocomment* output-stream)
  (dotimes (dummy *terpri-indent*)
    (declare (ignorable dummy)) 
    (princ " " output-stream)))

(defun unimplemented (&optional (datum "Unimplemented functionality.") &rest args)
  (apply #'error datum args))

(defvar *hash-dollar-package* nil)
(defvar *hash-dollar-readtable* nil)

(defun hash-dollar-reader (stream subchar arg)
  ;; reads exp in #$exp into package (or *hash-dollar-package* *package*) with case preserved
  (declare (ignore subchar arg))
  (let ((*readtable* *hash-dollar-readtable*)
        (*package* (or *hash-dollar-package* *package*)))
    (read stream t nil t)))

(defun initialize-hash-dollar-reader ()
  (unless *hash-dollar-readtable*
    (setf *hash-dollar-readtable* (copy-readtable nil))
    (setf (readtable-case *hash-dollar-readtable*) :preserve)
    (set-dispatch-macro-character #\# #\$ #'hash-dollar-reader *hash-dollar-readtable*)
    (set-dispatch-macro-character #\# #\$ #'hash-dollar-reader)
    t))

(initialize-hash-dollar-reader)

(defstruct (hash-dollar
            (:constructor make-hash-dollar (symbol))
            (:print-function print-hash-dollar-symbol3)
            (:copier nil))
  (symbol nil :read-only t))

(defun print-hash-dollar-symbol3 (x stream depth)
  (declare (ignore depth))
  (let* ((symbol (hash-dollar-symbol x))
         (string (symbol-name (hash-dollar-symbol x)))
         (*readtable* *hash-dollar-readtable*)
         (*package* (or (symbol-package symbol) *package*)))
    (unless (and (<= 1 (length string)) (eql #\? (char string 0)))
      (princ "#$" stream))
    (prin1 symbol stream)))

(defun hash-dollar-symbolize (x)
  (cond
   ((consp x)
    (cons (hash-dollar-symbolize (car x)) (hash-dollar-symbolize (cdr x))))
   ((and (symbolp x) (not (null x)) #+ignore (not (keywordp x)))
    (make-hash-dollar x))
   (t
    x)))

(defun hash-dollar-prin1 (object &optional (output-stream *standard-output*))
  (prin1 (hash-dollar-symbolize object) output-stream)
  object)

(defun hash-dollar-print (object &optional (output-stream *standard-output*))
  (prog2
   (terpri output-stream)
   (hash-dollar-prin1 object output-stream)
   (princ " " output-stream)))

;;; in MCL, (hash-dollar-print '|a"b|) erroneously prints #$a"b instead of #$|a"b|
;;; it appears that readtable-case = :preserve suppresses all escape character printing,
;;; not just those for case

;;; useful.lisp EOF
