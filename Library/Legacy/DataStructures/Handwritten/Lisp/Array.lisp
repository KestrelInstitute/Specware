
;;;; Arrays

(defpackage :Array-Spec)
(in-package :Array-Spec)

(defun |!array| (n i)
    (make-array n :initial-element i))
(defun |!array-1| (x)
  (make-array (car x) :initial-element (cdr x)))

(defun sub (a i)
    (svref a i))
(defun sub-1 (x)
    (svref (car x) (cdr x)))

(defun update (a i)
    #'(lambda (v)
	(progn
	  (setf (svref a i) v)
	  ())))

(defun update-1 (x) (update (car x) (cdr x)))

(defun update-1-1 (x v)
  (setf (svref (car x) (cdr x)) v)
  ())

(defun |!length| (a) 
  (length a))

(defun fromList (elements)
  (make-array (length elements) :initial-contents elements))

(defun tabulate (n f)
    (let ((a (make-array n))
	  (i 0))
      (loop
	(if (>= i n) (return a)
	  (progn
	    (setf (svref a i) (funcall f i))
	    (setf i (+ i 1)))))))

(defun tabulate-1 (x)
  (tabulate (car x) (cdr x)))

