;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: mes -*-
;;; File: collectors.lisp
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

(defun make-collector ()
  (cons nil nil))

(defun collector-value (collector)
  (car collector))

(defun collect-item (x collector)
  ;; as in Interlisp TCONC,
  ;; add single element x to the end of the list in (car collector)
  ;; and update (cdr collector) to point to the end of the list
  (setq x (cons x nil))
  (cond
    ((null collector)
     (cons x x))
    ((null (car collector))
     (rplacd collector (setf (car collector) x)))
    (t
     (rplacd collector (setf (cddr collector) x)))))

(defun collect-list (l collector)
  ;; as in Interlisp LCONC,
  ;; add list l to the end of the list in (car collector)
  ;; and update (cdr collector) to point to the end of the list
  (cond
    ((null l)
     collector)
    ((null collector)
     (cons l (last l)))
    ((null (car collector))
     (rplacd collector (last (setf (car collector) l))))
    (t
     (rplacd collector (last (setf (cddr collector) l))))))

(defmacro collect (item place)
  ;; like (setf place (nconc place (list item)))
  ;; except last cell of list is remembered in place-last
  ;; so that operation is O(1)
  ;; it can be used instead of (push item place) + (nreverse place) loop idiom
  ;; user must declare place-last variable or slot
  (let* ((args (if (atom place)
		   nil
		   (mapcar (lambda (arg) (list (gensym) arg)) (rest place))))
         (place (if (atom place)
		    place
		    (cons (first place) (mapcar #'first args))))
         (place-last (if (atom place)
                         (intern (concatenate
				  'string
				  (symbol-name place)
				  "-LAST"))
                         (cons (intern (concatenate
					'string
					(symbol-name (first place))
					"-LAST"))
                               (rest place))))
         (v (gensym))
         (l (gensym)))
    `(let* ((,v (cons ,item nil)) ,@args (,l ,place))
       (cond
        ((null ,l)
         (setf ,place (setf ,place-last ,v)))
        (t
         (rplacd ,place-last (setf ,place-last ,v))
         ,l)))))

(defmacro ncollect (list place)
  ;; like (setf place (nconc place list))
  ;; except last cell of list is remembered in place-last
  (let* ((args (if (atom place)
		   nil
		   (mapcar (lambda (arg) (list (gensym) arg)) (rest place))))
         (place (if (atom place)
		    place
		    (cons (first place) (mapcar #'first args))))
         (place-last (if (atom place)
                         (intern (concatenate
				  'string
				  (symbol-name place)
				  "-LAST"))
                         (cons (intern (concatenate
					'string
					(symbol-name (first place))
					"-LAST"))
                               (rest place))))
         (v (gensym))
         (l (gensym))
         (e (gensym)))
    `(let* ((,v ,list) ,@args (,l ,place))
       (if  (null ,v)
            ,l
            (let ((,e (rest ,v)))
              (setq ,e (if (null ,e) ,v (last ,e)))
              (cond
               ((null ,l)
                (setf ,place-last ,e)
                (setf ,place ,v))
               (t
                (rplacd ,place-last ,v)
                (setf ,place-last ,e)
                ,l)))))))

(defmacro pushnew-unless-nil (item place &key test test-not key)
  (let ((v (gensym)))
    `(let ((,v ,item))
       (unless (null ,v)
	 (pushnew ,v ,place
		  ,@(when test `(:test ,test))
		  ,@(when test-not `(:test-not ,test-not))
		  ,@(when key `(:key ,key)))))))

;;; collectors.lisp EOF
