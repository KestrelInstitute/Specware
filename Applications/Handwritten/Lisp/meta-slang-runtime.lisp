;; This file defines general utilities that are necessary to 
;; connect EXTENDED-SLANG specs with lisp code.

(defpackage :SLANG-BUILT-IN)
(IN-PACKAGE :SLANG-BUILT-IN)

(defparameter quotient-tag
  (list :|Quotient|))

(defun quotient (r)
  #'(lambda(x)  (vector quotient-tag r x)))

(defun quotient? (x)
  (and (vectorp x)
       (eq (svref x 0) quotient-tag)))

(defun quotient-relation (x)
  (svref x 1))

(defun quotient-element (x)
  (if (quotient? x)
      (svref x 2)
    (error "Expected an equivalence class, but got (presumably) a representative: ~S" x)))

(defun choose (relation)
  (declare (ignore relation))
  #'(lambda (f) #'(lambda(x) (funcall f (quotient-element x)))))

(defun choose-1-1 (relation f x) 
  (declare (ignore relation))
  (funcall f (quotient-element x)))

#|
  
  slang-term-equals
  -----------------
     This function determines equality for lisp expressions that
     are generated from EXT-SLANG terms admitting equality.


     A translated ext-slang term admitting equality can be in one of the
     following forms:

  (vector t1 t2 ... tn)   - a product
  (cons t1 t2)            - a two tuple
  (cons t1 t2) , nil      - an element of a list sort
  (list 'Quotient 'fn t)  - an element of a quotient sort
  (cons 'Name t)          - an embedding
  atom                    - a string, char, or nat constant.

|#

;;;  (defun slang-term-equals (t1 t2)
;;;     (or 
;;;      (eq t1 t2)
;;;      (cond
;;;        ((null t1) (null t2))
;;;        ((stringp t1) (string= t1 t2))
;;;        ((symbolp t1) (eql t1 t2))
;;;        ((numberp t1) (eq t1 t2))
;;;        ((characterp t1) (eql t1 t2))
;;;  #| 
;;;     Determine equality by calling the quotient 
;;;     operator in the second position 
;;;     |#
;;;        ((and (quotient? t1)
;;;  	    (quotient? t2))
;;;         (funcall 
;;;  	(quotient-relation t1)
;;;  	(quotient-element t1) 
;;;  	(quotient-element t2)))
;;;       
;;;  #|
;;;     Cons cells are equal if their elements are equal too.
;;;  |#
;;;        ((consp t1) 	 
;;;             (and 
;;;  	    (consp t2) 
;;;  	    (slang-term-equals (car t1) (car t2))
;;;  	    (slang-term-equals (cdr t1) (cdr t2))))
;;;  #|
;;;     Two vectors (corresponding to tuple types)
;;;     are equal if all their elements are equal.
;;;  |#
;;;        ((vectorp t1)
;;;             (and 
;;;  	    (vectorp t2)
;;;  	    (let ((dim (array-dimension t1 0)))
;;;  	      (do ((i 0 (+ i 1))
;;;  		   (v-equal t (slang-term-equals (svref t1 i)  (svref t2 i))))
;;;  		  ((or (= i dim) (not v-equal)) v-equal)))))
;;;        (t (progn (format t "Ill formed terms~%") nil))
;;;        )
;;;      )
;;;     )

;;; This is twice as fast as the version above...
(defun slang-term-equals-2 (t1 t2)
  (or (eq t1 t2)
      (typecase t1
	(null      (null    t2))
	(string    (string= t1 t2))
	(symbol    (eq      t1 t2))
	(number    (eq      t1 t2))
	(character (eq      t1 t2))
	(cons      (and (consp t2) 
			;;   Cons cells are equal if their elements are equal too.
			(slang-term-equals-2 (car t1) (car t2))
			(slang-term-equals-2 (cdr t1) (cdr t2))))
        (vector    (cond ((and   
			   ;; (quotient? t1) 
			   ;; (quotient? t2)
			   (eq (svref t1 0) quotient-tag)
			   (vectorp t2)
			   (eq (svref t2 0) quotient-tag)
			   )
			  ;; Determine equality by calling the quotient 
			  ;; operator in the second position 
			  (funcall (svref t1 1) ; (quotient-relation t1)
				   (cons (svref t1 2) ; (quotient-element t1) 
				         (svref t2 2) ; (quotient-element t2)
				   )))
			 (t
			  (and
			   ;; Two vectors (corresponding to tuple types)
			   ;; are equal if all their elements are equal.
			   (vectorp t2)
			   (let ((dim (array-dimension t1 0)))
			     (do ((i 0 (+ i 1))
				  (v-equal t (slang-term-equals-2 (svref t1 i)  (svref t2 i))))
				 ((or (= i dim) (not v-equal)) v-equal)))))))
	(t (progn 
	     (format t "Ill formed terms~%") 
	     nil)))))

(defun slang-term-equals (x) (slang-term-equals-2 (car x) (cdr x)))


#|

 Tests:

 (slang-term-equals (cons (vector 1 2 3) (vector 1 2 3)))

 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "3")))
 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "4")))

 (slang-term-equals (cons 
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  3)
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  11)))

|#


