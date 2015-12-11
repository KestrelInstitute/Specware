;;; Modified from MapAsSTHarray.lisp which is modified from Marcel's HArrayAsStringMap.lisp
;;; Modified for backtracking usage, where only one version is used at any time,
;;; but once a version is backtracked from, it is is likely never to be referenced again.
;;; Only keep forward links to allow for garbage collection of unused nodes.
;;; Rather than have a list of undos, keep the undo/information in the node with a pointer
;;; to the next node. When you undo, the pointers are reversed.

(defpackage :MapBTHashtable)
(in-package :MapBTHashtable)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3)(debug 3))))


(defun make-map-as-undo-harray (harray next)
  (vector harray next nil nil
))

(defmacro map-as-undo-harray--harray (x) `(svref ,x 0))
(defmacro map-as-undo-harray--next (x) `(svref ,x 1))
(defmacro map-as-undo-harray-current? (x) `(null (svref ,x 1)))
(defmacro map-as-undo-harray--dom-elt (x) `(svref ,x 2))
(defmacro map-as-undo-harray--saved-val (x) `(svref ,x 3))

(defmacro map-as-undo-harray--set-next (m next)
   `(setf (svref ,m 1) ,next))

(defun set-undo-info (v domain-value old-range-value)
  (setf (svref v 2) domain-value)
  (setf (svref v 3) old-range-value))

(defparameter *map-as-undo-harray--initial-harray-size* 100)
(defparameter *map-as-undo-harray--rehash-size* 2.0)

(defun map-as-undo-harray--initial-harray ()
  (Specware::make-sw-hash-table :size *map-as-undo-harray--initial-harray-size*
                                :rehash-size *map-as-undo-harray--rehash-size*))

(defun make-hash-table-same-size (table)
  (Specware::make-sw-hash-table :size (hash-table-count table)
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

(defun map-as-undo-harray-assure-current (m)
  (if (map-as-undo-harray-current? m)
      m
      (let* ((table (map-as-undo-harray--harray m))
	     ;; Follow links to curr reversing as you go
	     (live (do ((curr m next)
			(next (prog1 (map-as-undo-harray--next m)
				(map-as-undo-harray--set-next m nil))
			      (prog1 (map-as-undo-harray--next next)
				(map-as-undo-harray--set-next next curr))))
		       ((null next) curr)
		     ())))   ; empty body because action in prog1
	;; Follow links back to m undoing as we go and storing redo info
	(do ((curr live next)
	     (next (map-as-undo-harray--next live)
		   (map-as-undo-harray--next next)))
	    ((null next) ())
	  (let ((dom-elt (map-as-undo-harray--dom-elt next)))
	    ;(format t "Current: ~a~%~a -> ~a~%" curr dom-elt (gethash dom-elt table))
	    (set-undo-info curr dom-elt (gethash dom-elt table *undefined*))
	    (let ((old-val (map-as-undo-harray--saved-val next)))
	      (if (eq old-val *undefined*)
		  (remhash dom-elt table)
		  (setf (gethash dom-elt table) old-val)))))
	m)))
	     

(defparameter BTH_empty_map (make-map-as-undo-harray (Specware::make-sw-hash-table :size 0)
                                                     nil))

(defun map-as-undo-harray--update (m x y)
  (if (eq m BTH_empty_map)
      (if (eq y *undefined*)
	  m
	(let ((new-table (map-as-undo-harray--initial-harray)))
	  (setf (gethash x new-table) y)
	  (make-map-as-undo-harray new-table nil)))
    (let ((m (map-as-undo-harray-assure-current m)))
      ;(incf *map-as-undo-harray-set-count*)
      (let* ((table (map-as-undo-harray--harray m))
	     (old-val (gethash x table *undefined*)))
	(if (eq y old-val)
	    m				; Optimize special case
	  (progn
	    (if (eq y *undefined*)
		(progn (remhash x table))
	      (progn (setf (gethash x table) y)))
	    (set-undo-info m x old-val)
	    (let ((new-m (make-map-as-undo-harray table nil)))
	      (map-as-undo-harray--set-next m new-m)
	      new-m)))))))

(defun map-as-undo-harray--map-through-pairs (fn m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash fn (map-as-undo-harray--harray m))))


;;; The Hash Table interface functions

(defun BTH_numItems (m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (hash-table-count (map-as-undo-harray--harray m))))

(defun BTH_apply-2 (m x)
  ;(incf *map-as-undo-harray-ref-count*)
  (map-as-undo-harray-assure-current m)
  (let ((val (gethash x (map-as-undo-harray--harray m) *undefined*)))
    (if (eq val *undefined*) *undefined*
      (mkSome val))))

(defun BTH_apply (pr)
  (BTH_apply-2 (car pr) (cdr pr)))

(defun BTH_eval-2 (m x)
  ;(incf *map-as-undo-harray-ref-count*)
  (map-as-undo-harray-assure-current m)
  (let ((val (gethash x (map-as-undo-harray--harray m) *undefined*)))
    (if (eq val *undefined*)
	(error "BTH_eval: out-of-domain reference: ~a" x)
      val)))

(defun BTH_eval (pr)
  (BTH_eval-2 (car pr) (cdr pr)))


;;; Some y is stored in array, as it is usually accessed more often than set
(defun BTH_update-3 (m x y)
  (map-as-undo-harray--update m x y))

(defun BTH_remove-2 (m x)
  (map-as-undo-harray--update m x *undefined*))

(defun BTH_remove (pr)
  (map-as-undo-harray--update (car pr) (cdr pr) *undefined*))

(defun BTH_mapi-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f (cons key val))))
	     table)
    (make-map-as-undo-harray result nil)))

(defun BTH_map-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f val)))
	     table)
    (make-map-as-undo-harray result nil)))

(defun BTH_mapiPartial-2 (f m)
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

(defun BTH_mapPartial-2 (f m)
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

(defun BTH_app-2 (f m)
  (declare (dynamic-extent f))
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash #'(lambda (key val)
		 (declare (ignore key))
		 (funcall f val))
	     (map-as-undo-harray--harray m)))
  nil)

(defun BTH_appi-2 (f m)
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
(progn (setf (get 'foldi-3 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'app-2 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'appi-2 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'map-2 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'mapi-2 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil)))

(defun BTH_foldi-3 (fn result m)
  (map-as-undo-harray--map-through-pairs
     #'(lambda (key val)
	 (let ((args (foldi-vector key val result)))
	   (declare (dynamic-extent args))
	   (setq result (funcall fn args))))
     m)
  result)

(defun BTH_imageToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (declare (ignore key))
		   (push val items))
	       (map-as-undo-harray--harray m))
      items)))

(defun BTH_mapToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (push (cons key val) items))
	       (map-as-undo-harray--harray m))
    items)))

(defun BTH_domainToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		 (declare (ignore val))
		 (push key items))
	       (map-as-undo-harray--harray m))
    items)))

