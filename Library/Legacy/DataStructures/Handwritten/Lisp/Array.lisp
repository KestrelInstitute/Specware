
;;;; Arrays

(defpackage :Array-Spec)
(in-package :Array-Spec)

(defun |!array| (n i)
    (make-array n :initial-element i))
(defun |!array-1| (x)
  (make-array (car x) :initial-element (cdr x)))

(defun sub-2 (a i)
    (svref a i))
(defun sub (x)
    (svref (car x) (cdr x)))

(defun update-2 (a i)
    #'(lambda (v)
	(progn
	  (setf (svref a i) v)
	  ())))

(defun update (x) (update-2 (car x) (cdr x)))

(defun update-1-1 (x v)
  (setf (svref (car x) (cdr x)) v)
  ())

(defun |!length| (a) 
  (length a))

(defun fromList (elements)
  (make-array (length elements) :initial-contents elements))

(defun tabulate-2 (n f)
    (let ((a (make-array n))
	  (i 0))
      (loop
	(if (>= i n) (return a)
	  (progn
	    (setf (svref a i) (funcall f i))
	    (setf i (+ i 1)))))))

(defun tabulate (x)
  (tabulate-2 (car x) (cdr x)))

