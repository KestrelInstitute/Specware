;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: permutations.lisp
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

;;; permutations are specified by lists of integers specifying how to permute arguments
;;; (e.g., (1 0) for commutativity; this is shorthand for {x0 -> x1, x1 -> x0}

(defun permutation-p (x &optional max-length)
  ;; x is a permutation if its length is at least two and does not exceed max-length
  ;; and it is a nontrivial permutation of the integers between 0 and its length minus 1
  (let ((length (list-p x)))
    (and length
	 (<= 2 length)
	 (implies max-length (<= length max-length))
	 (let ((previous nil)
	       (nontrivial nil))
	   (dotails (l x nontrivial)
	     (let ((l1 (first l)))
	       (unless (and (integerp l1)
			    (>= l1 0)
			    (< l1 length)
			    (not (member l1 (rest l))))
		 (return nil))
	       (unless nontrivial
		 (if (and previous (> previous l1))
		     (setf nontrivial t)
		     (setf previous l1)))))))))

(defun permute (l permutation)
  (labels
    ((permute* (l1 permutation)
       (lcons (nth (first permutation) l)	;inefficient to use nth for this
	      (if (null (rest permutation))
		  (rest l1)
		  (permute* (rest l1) (rest permutation)))
	      l1)))
    (permute* l permutation)))

(defun permute-randomly (l)
  (cond
    ((null l)
     nil)
    (t
     (let ((result nil)
	   (n (length l)))
       (loop
	 (cond
	   ((= n 1)
	    (return (cons (first l) result)))
	   (t
	    (let ((v (nthcdr (random n) l)))
	      (push (first v) result)
	      (setf l (nconc (ldiff l v) (rest v)))
	      (decf n)))))))))

(defun permutations (l permutations &key (test #'eql))
  (labels
    ((permutations* (l result)
       (unless (member l result :test (lambda (x y) (every test x y)))
	 (push l result)
	 (dolist (p permutations)
	   (setf result (permutations* (permute l p) result))))
       result))
    (permutations* l nil)))

(defun all-insertions (x l &key (test #'eql))
  (labels
    ((all-insertions* (l lrev)
       (cond
	 ((null l)
	  (list (revappend lrev (list x))))
	 ((funcall test x (first l))
	  (all-insertions* (rest l) (cons (first l) lrev)))
	 (t
	  (cons (revappend lrev (cons x l))
		(all-insertions* (rest l) (cons (first l) lrev)))))))
    (all-insertions* l nil)))

(defun all-permutations (l &key (test #'eql))
  (cond
    ((null l)
     (list nil))
    ((null (rest l))
     (list l))
    (t
     (let ((x (first l)))
       (reduce (lambda (x y) (nunion x y :test (lambda (x y) (every test x y))))
	       (mapcar (lambda (y) (all-insertions x y :test test))
		       (all-permutations (rest l))))))))

;;; permutations.lisp EOF
