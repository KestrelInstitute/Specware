;;;-------------------------------------------------------------------------
;;;               Copyright (C) 2002 by Kestrel Technology
;;;                          All Rights Reserved
;;;-------------------------------------------------------------------------
;;; Modified from Marcel's HArrayAsStringMap.lisp
;;; Further modified for near single-threaded use.
;;; Only keep forward links to allow for garbage collection of unused nodes and undolist

(defpackage :MapSTHashtable)
(in-package :MapSTHashtable)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3)(debug 3))))


(defun make-map-as-undo-harray (harray undo-list)
  (vector harray t undo-list))

(defmacro map-as-undo-harray--harray (x) `(svref ,x 0))
(defmacro map-as-undo-harray--undo-list (x) `(svref ,x 2))
(defmacro map-as-undo-harray-current? (x) `(svref ,x 1))

(defun make-undo-pair (domain-value old-range-value)
  (cons domain-value old-range-value))

(defparameter *map-as-undo-harray--initial-harray-size* 100)
(defparameter *map-as-undo-harray--rehash-size* 2.0)

(defun map-as-undo-harray--initial-harray ()
  (make-hash-table :test 'equal
		   :size *map-as-undo-harray--initial-harray-size*
		   :rehash-size *map-as-undo-harray--rehash-size*))

(defmacro map-as-undo-harray--set-undo-list (m undo-list)
   `(setf (svref ,m 2) ,undo-list))

(defmacro map-as-undo-harray--mark-non-current (m)
   `(setf (svref ,m 1) nil))

(defun make-hash-table-same-size (table)
  (make-hash-table :test 'equal
		   :size (hash-table-count table)
		   :rehash-size
		   *map-as-undo-harray--rehash-size*))

(defun copy-hash-table (table)
  (let ((result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val) (setf (gethash key result) val))
	     table)
    result))

(defparameter *map-as-undo-harray-undo-count* 0)
(defparameter *map-as-undo-harray-copy-count* 0)
(defparameter *map-as-undo-harray-ref-count* 0)
(defparameter *map-as-undo-harray-alist-ref-count* 0)
(defparameter *map-as-undo-harray-alist-elt-ref-count* 0)
(defparameter *map-as-undo-harray-set-count* 0)

(defvar *undefined* '(:|None|))
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defvar *break-on-non-single-threaded-updates?* nil)
;;; (setq MapSTHashtable::*break-on-non-single-threaded-updates?* t)

(defun map-as-undo-harray-assure-current (m)
  (if (map-as-undo-harray-current? m)
      m
    (let ((undo-list (nreverse (map-as-undo-harray--undo-list m)))
	  (table (map-as-undo-harray--harray m)))
      ;(incf *map-as-undo-harray-undo-count* (length undo-list))
      ;(incf *map-as-undo-harray-copy-count*)
      (when *break-on-non-single-threaded-updates?*
	(break "Non-single-threaded update!"))
      (let ((new-table (copy-hash-table table)))
	(loop for (dom . ran) in undo-list
	   do (if (eq ran *undefined*)
		  (remhash dom new-table)
		(setf (gethash dom new-table) ran)))
	;; Two nreverses leave things unchanged
	(nreverse undo-list)
	(make-map-as-undo-harray new-table nil)))))

(defparameter emptyMap (make-map-as-undo-harray (make-hash-table :test 'equal :size 0) nil))

(defun map-as-undo-harray--update (m x y)
  (if (eq m emptyMap)
      (if (eq y *undefined*)
	  m
	(let ((new-table (map-as-undo-harray--initial-harray)))
	  (setf (gethash x new-table) y)
	  (make-map-as-undo-harray new-table nil)))
    (let ((m (map-as-undo-harray-assure-current m)))
      ;(incf *map-as-undo-harray-set-count*)
      (let* ((last-undo-list (map-as-undo-harray--undo-list m))
	     (table (map-as-undo-harray--harray m))
	     (old-val (gethash x table *undefined*)))
	(if (eq y old-val)
	    m				; Optimize special case
	  (progn
	    (if (eq y *undefined*)
		(progn (remhash x table))
	      (progn (setf (gethash x table) y)))
	    (let ((new-undo-list (cons (make-undo-pair x old-val)
				       nil)))
	      (map-as-undo-harray--set-undo-list m new-undo-list)
	      (map-as-undo-harray--mark-non-current m)
	      (unless (null last-undo-list)
		(setf (cdr last-undo-list) new-undo-list))
	      (make-map-as-undo-harray table new-undo-list))))))))

(defun map-as-undo-harray--map-through-pairs (fn m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash fn (map-as-undo-harray--harray m))))


;;; The Hash Table interface functions

(defun numItems (m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (hash-table-count (map-as-undo-harray--harray m))))

(defun apply-2 (m x)
  ;(incf *map-as-undo-harray-ref-count*)
  (let ((val
	 (if (map-as-undo-harray-current? m)
	     (gethash x (map-as-undo-harray--harray m) *undefined*)
	   (let ((alist (map-as-undo-harray--undo-list m)))
	     ;;(incf *map-as-undo-harray-alist-ref-count*)
	     ;;(incf *map-as-undo-harray-alist-elt-ref-count* (length alist))
	     (loop for l on alist
		 until (not (consp l))
		 when (equal (caar l) x)
		 return (cdar l)
		 finally (return (gethash x (map-as-undo-harray--harray m)
					  *undefined*)))))))
    (if (eq val *undefined*) *undefined*
      (mkSome val))))

(defun |!apply| (pr)
  (apply-2 (car pr) (cdr pr)))

;;; Some y is stored in array, as it is usually accessed more often than set
(defun update-3 (m x y)
  (map-as-undo-harray--update m x y))

(defun remove-2 (m x)
  (map-as-undo-harray--update m x *undefined*))

(defun |!remove| (pr)
  (map-as-undo-harray--update (car pr) (cdr pr) *undefined*))

(defun mapi-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f (cons key val))))
	     table)
    (make-map-as-undo-harray result nil)))

(defun map-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f val)))
	     table)
    (make-map-as-undo-harray result nil)))

(defun mapiPartial-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (map-as-undo-harray--initial-harray)))
    (maphash #'(lambda (key val)
		 (let ((val (funcall f (cons key val))))
		   (unless (equal val *undefined*)
		     ;; (:|Some| . realval)
		     (setf (gethash key result) (cdr val)))))
	     table)
    (make-map-as-undo-harray result nil)))

(defun mapPartial-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (map-as-undo-harray--initial-harray)))
    (maphash #'(lambda (key val)
		 (let ((val (funcall f val)))
		   (unless (equal val *undefined*)
		     ;; (:|Some| . realval)
		     (setf (gethash key result) (cdr val)))))
	     table)
    (make-map-as-undo-harray result nil)))

(defun app-2 (f m)
  (declare (dynamic-extent f))
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash #'(lambda (key val)
		 (declare (ignore key))
		 (funcall f val))
	     (map-as-undo-harray--harray m)))
  nil)

(defun appi-2 (f m)
  (declare (dynamic-extent f))
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash #'(lambda (key val)
		 (let ((args (cons key val)))
		   (declare (dynamic-extent args))
		   (funcall f args)))
	     (map-as-undo-harray--harray m))
    nil))

(defvar *foldi-vector* (vector nil nil nil))

(defun foldi-vector (x y z)
  ;(vector x y z)
  (setf (svref *foldi-vector* 0) x)
  (setf (svref *foldi-vector* 1) y)
  (setf (svref *foldi-vector* 2) z)
  *foldi-vector*
  )

#+allegro
(progn (setf (get 'foldi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'app 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'appi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get '|!map| 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'mapi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil)))

(defun foldi-3 (fn result m)
  (map-as-undo-harray--map-through-pairs
     #'(lambda (key val)
	 (let ((args (foldi-vector key val result)))
	   (declare (dynamic-extent args))
	   (setq result (funcall fn args))))
     m)
  result)

(defun imageToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (declare (ignore key))
		   (push val items))
	       (map-as-undo-harray--harray m))
      items)))

(defun mapToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (push (cons key val) items))
	       (map-as-undo-harray--harray m))
    items)))

(defun domainToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		 (declare (ignore val))
		 (push key items))
	       (map-as-undo-harray--harray m))
    items)))



#|


|#
