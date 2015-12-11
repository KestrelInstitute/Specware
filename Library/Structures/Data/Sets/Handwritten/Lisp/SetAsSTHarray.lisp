;;; Modified from MapAsSTHarray which was based on Marcel's HArrayAsStringMap.lisp
;;; Designed for near single-threaded use.
;;; Only keep forward links to allow for garbage collection of unused nodes and undolist

(defpackage :SetSTHashtable)
(in-package :SetSTHashtable)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3)(debug 3))))


(defun make-set-as-undo-harray (harray undo-list)
  (vector harray t undo-list))

(defmacro set-as-undo-harray--harray (x) `(svref ,x 0))
(defmacro set-as-undo-harray--undo-list (x) `(svref ,x 2))
(defmacro set-as-undo-harray-current? (x) `(svref ,x 1))

(defun make-undo-pair (domain-value old-range-value)
  (cons domain-value old-range-value))

(defparameter *set-as-undo-harray--initial-harray-size* 50)
(defparameter *set-as-undo-harray--rehash-size* 2.0)

(defun set-as-undo-harray--initial-harray ()
  (Specware::make-sw-hash-table :size *set-as-undo-harray--initial-harray-size*
                                :rehash-size *set-as-undo-harray--rehash-size*))

(defmacro set-as-undo-harray--set-undo-list (m undo-list)
   `(setf (svref ,m 2) ,undo-list))

(defmacro set-as-undo-harray--mark-non-current (m)
   `(setf (svref ,m 1) nil))

(defun make-hash-table-same-size (table)
  (Specware::make-sw-hash-table :size (hash-table-count table)
                                :rehash-size
                                *set-as-undo-harray--rehash-size*))

(defun copy-hash-table (table)
  (let ((result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val) (setf (gethash key result) val))
	     table)
    result))

(defparameter *set-as-undo-harray-undo-count* 0)
(defparameter *set-as-undo-harray-copy-count* 0)
(defparameter *set-as-undo-harray-ref-count* 0)
(defparameter *set-as-undo-harray-alist-ref-count* 0)
(defparameter *set-as-undo-harray-alist-elt-ref-count* 0)
(defparameter *set-as-undo-harray-set-count* 0)

(defvar *undefined* nil)
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defvar *break-on-non-single-threaded-updates?* nil)
;;; (setq SetSTHashtable::*break-on-non-single-threaded-updates?* t)

(defun set-as-undo-harray-assure-current (m)
  (if (set-as-undo-harray-current? m)
      m
    (let ((undo-list (nreverse (set-as-undo-harray--undo-list m)))
	  (table (set-as-undo-harray--harray m)))
      ;(incf *set-as-undo-harray-undo-count* (length undo-list))
      ;(incf *set-as-undo-harray-copy-count*)
      (when *break-on-non-single-threaded-updates?*
	(break "Non-single-threaded update!"))
      (let ((new-table (copy-hash-table table)))
	(loop for (dom . ran) in undo-list
	   do (if (eq ran *undefined*)
		  (remhash dom new-table)
		(setf (gethash dom new-table) ran)))
	;; Two nreverses leave things unchanged
	(nreverse undo-list)
	(make-set-as-undo-harray new-table nil)))))

(defparameter emptySet (make-set-as-undo-harray (Specware::make-sw-hash-table :size 0) nil))

(defun set-as-undo-harray--update (m x y)
  (if (eq m emptySet)
      (if (eq y *undefined*)
	  m
	(let ((new-table (set-as-undo-harray--initial-harray)))
	  (setf (gethash x new-table) y)
	  (make-set-as-undo-harray new-table nil)))
    (let ((m (set-as-undo-harray-assure-current m)))
      ;(incf *set-as-undo-harray-set-count*)
      (let* ((last-undo-list (set-as-undo-harray--undo-list m))
	     (table (set-as-undo-harray--harray m))
	     (old-val (gethash x table *undefined*)))
	(if (eq y old-val)
	    m				; Optimize special case
	  (progn
	    (if (eq y *undefined*)
		(progn (remhash x table))
	      (progn (setf (gethash x table) y)))
	    (let ((new-undo-list (cons (make-undo-pair x old-val)
				       nil)))
	      (set-as-undo-harray--set-undo-list m new-undo-list)
	      (set-as-undo-harray--mark-non-current m)
	      (unless (null last-undo-list)
		(setf (cdr last-undo-list) new-undo-list))
	      (make-set-as-undo-harray table new-undo-list))))))))

(defun set-as-undo-harray--map-through-pairs (fn m)
  (let ((m (set-as-undo-harray-assure-current m)))
    (maphash fn (set-as-undo-harray--harray m))))


;;; The Hash Table interface functions
(defun emptySet? (s) (= (numItems s) 0))

(defun numItems (m)
  (let ((m (set-as-undo-harray-assure-current m)))
    (hash-table-count (set-as-undo-harray--harray m))))

(defun member?-2 (m x)
  ;(incf *set-as-undo-harray-ref-count*)
  (let ((val
	 (if (set-as-undo-harray-current? m)
	     (gethash x (set-as-undo-harray--harray m) *undefined*)
	   (let ((alist (set-as-undo-harray--undo-list m)))
	     ;;(incf *set-as-undo-harray-alist-ref-count*)
	     ;;(incf *set-as-undo-harray-alist-elt-ref-count* (length alist))
	     (loop for l on alist
		 until (not (consp l))
		 when (equal (caar l) x)
		 return (cdar l)
		 finally (return (gethash x (set-as-undo-harray--harray m)
					  *undefined*)))))))
    (if (eq val *undefined*) nil
      t)))

(defun member? (pr)
  (member?-2 (car pr) (cdr pr)))

(defun subset?-2 (s1 s2)
  (let* ((s1 (set-as-undo-harray-assure-current s1))
	 (s2 (set-as-undo-harray-assure-current s2))
	 (s2-ht (set-as-undo-harray--harray s2)))
    (and (<= (hash-table-count (set-as-undo-harray--harray s1))
	     (hash-table-count s2-ht))
	 (progn (maphash #'(lambda (key val)
			     (declare (ignore val))
			     (when (eq (gethash key s2-ht *undefined*) *undefined*)
			       (return-from subset?-2 nil)))
			 (set-as-undo-harray--harray s1))
		t))))

;;; Some y is stored in array, as it is usually accessed more often than set
(defun insert-2 (m x)
  (set-as-undo-harray--update m x t))

(defun insert (pr)
  (set-as-undo-harray--update (car pr) (cdr pr) t))

(defun delete-2 (m x)
  (set-as-undo-harray--update m x *undefined*))

(defun |!delete| (pr)
  (set-as-undo-harray--update (car pr) (cdr pr) *undefined*))

(defun map-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (set-as-undo-harray-assure-current m))
	 (table (set-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (declare (ignore val))
		 (setf (gethash (funcall f key) result) t))
	     table)
    (make-set-as-undo-harray result nil)))

(defun |!map| (pr) (map-2 (car pr) (cdr pr)))

#+allegro
(progn (setf (get 'fold-3 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'map-2 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil)))

(defun fold-3 (fn result m)
  (set-as-undo-harray--map-through-pairs
     #'(lambda (key val)
	 (declare (ignore val))
	 (setq result (funcall (funcall fn result) key)))
     m)
  result)

(defun find-2 (pred m)
  (set-as-undo-harray--map-through-pairs
     #'(lambda (key val)
	 (declare (ignore val))
	 (when (funcall pred key)
	   (return-from find-2 (mkSome key))))
     m)
  '(:|None|))

(defun to_List (m) 
  (let ((m (set-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val)
		   (declare (ignore val))
		   (push key items))
	       (set-as-undo-harray--harray m))
    items)))
