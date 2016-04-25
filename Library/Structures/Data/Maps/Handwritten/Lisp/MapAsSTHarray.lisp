;;; Modified from Marcel's HArrayAsStringMap.lisp
;;; Further modified for near single-threaded use.
;;; Only keep forward links to allow for garbage collection of unused nodes and undolist
;;; Whenever changes are undone, make a copy, so that leaf versions can live together
;;; Each node is a vector containing the harray, whether the harray is current, and the undo
;;; list. I can't remember why an undo list of nil doesn't mean the harray is current.
;;; An undo element is a pair of the domain value and its previous range value.
;;; Because of the copy-on-undo strategy, there is never any need to switch the element to a redo.
;;; A lookup on a non-current version does not cause an update.Instead, the undo list is treated as
;;; an alist map shadowing the harray.


(defpackage :MapSTHashtable)
(in-package :MapSTHashtable)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3) (debug 1))))


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
  (Specware::make-sw-hash-table :size *map-as-undo-harray--initial-harray-size*
                                :rehash-size *map-as-undo-harray--rehash-size*))

(defmacro map-as-undo-harray--set-harray-list (m table)
   `(setf (svref ,m 0) ,table))

(defmacro map-as-undo-harray--set-undo-list (m undo-list)
   `(setf (svref ,m 2) ,undo-list))

(defmacro map-as-undo-harray--mark-current (m current)
   `(setf (svref ,m 1) ,current))

(defmacro map-as-undo-harray--mark-non-current (m)
   `(setf (svref ,m 1) nil))

(defmacro update-map-as-undo-harray (m harray current undo-list)
  `(let ((m ,m))
     (map-as-undo-harray--set-harray-list m ,harray)
     (map-as-undo-harray--mark-current m ,current)
     (map-as-undo-harray--set-undo-list m ,undo-list)
     m))

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

;;; (list MapSTHashtable::*map-as-undo-harray-undo-count* MapSTHashtable::*map-as-undo-harray-copy-count*)

(defvar *undefined* '(:|None|))
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defvar *maphash-htables* nil)
#+sb-thread
(defvar *maphash-htables-mutex* (sb-thread:make-mutex :name "*maphash-htables*"))

(defun set-*maphash-htables* (val-fn)
  #+sb-thread
  (sb-thread:with-mutex (*maphash-htables-mutex*)
    (setq *maphash-htables* (funcall val-fn *maphash-htables*)))
  #-sb-thread
  (setq *maphash-htables* (funcall val-fn *maphash-htables*)))

(defvar *break-on-non-single-threaded-updates?* nil)

;;; (setq MapSTHashtable::*break-on-non-single-threaded-updates?* t)

(defun map-as-undo-harray-assure-current (m)
  (if (map-as-undo-harray-current? m)
      m
    (let ((undo-list (nreverse (map-as-undo-harray--undo-list m)))
	  (table (map-as-undo-harray--harray m)))
      ; (incf *map-as-undo-harray-undo-count* (length undo-list))
      ; (incf *map-as-undo-harray-copy-count*)
      (when *break-on-non-single-threaded-updates?*
	(break "Non-single-threaded update!"))
      (let ((new-table (copy-hash-table table)))
	(unless (map-as-undo-harray-current? m)
          (loop for (dom . ran) in undo-list
                do (if (eq ran *undefined*)
                       (remhash dom new-table)
                       (setf (gethash dom new-table) ran)))
	;; Two nreverses leave things unchanged
          (nreverse undo-list))
        (update-map-as-undo-harray m new-table t nil)
        ))))

(defparameter STH_empty_map (make-map-as-undo-harray (Specware::make-sw-hash-table :size 0) nil))

(defun map-as-undo-harray--update (m x y)
  (if (eq m STH_empty_map)
      (if (eq y *undefined*)
	  m
	(let ((new-table (map-as-undo-harray--initial-harray)))
	  (setf (gethash x new-table) y)
	  (make-map-as-undo-harray new-table nil)))
    (let* ((m (map-as-undo-harray-assure-current m))
           (table (map-as-undo-harray--harray m)))
      ;(incf *map-as-undo-harray-set-count*)
      (let* ((last-undo-list (map-as-undo-harray--undo-list m))
	     (old-val (gethash x table *undefined*)))
	(if (Slang-Built-In::slang-term-equals-2 y old-val)
	    m				; Optimize special case
	  (progn
            (when (member table *maphash-htables* :test 'eq)
              (setq table (copy-hash-table table))
              (setq m (make-map-as-undo-harray table nil)))
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
  (let* ((m (map-as-undo-harray-assure-current m))
         (tbl (map-as-undo-harray--harray m)))
    (set-*maphash-htables* #'(lambda (mht) (cons tbl mht)))
    (maphash fn (map-as-undo-harray--harray m))
    (set-*maphash-htables* #'(lambda (mht) (remove tbl mht :count 1)))
    ))


;;; The Hash Table interface functions

(defun STH_numItems (m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (hash-table-count (map-as-undo-harray--harray m))))

(defvar *m1*)

(defun STH_apply-2 (m x)
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
;     (when (eq val *undefined*)
;       (setq *m1* m)
;       (format t "(STH_apply-2 '~a) = ~a~%" x val))
    (if (eq val *undefined*) *undefined*
      (mkSome val))))

(defun STH_apply (pr)
  (STH_apply-2 (car pr) (cdr pr)))

(defun STH_eval-2 (m x)
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
    (if (eq val *undefined*)
	(error "STH_eval: out-of-domain reference: ~a" x)
      val)))

(defun STH_eval (pr)
  (STH_eval-2 (car pr) (cdr pr)))


;;; Some y is stored in array, as it is usually accessed more often than set
(defun STH_update-3 (m x y)
  (map-as-undo-harray--update m x y))

(defun STH_remove-2 (m x)
  (map-as-undo-harray--update m x *undefined*))

(defun STH_remove (pr)
  (map-as-undo-harray--update (car pr) (cdr pr) *undefined*))

(defun STH_mapi-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f (cons key val))))
	     table)
    (make-map-as-undo-harray result nil)))

(defun STH_map-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-harray-assure-current m))
	 (table (map-as-undo-harray--harray curr-m))
	 (result (make-hash-table-same-size table)))
    (maphash #'(lambda (key val)
		 (setf (gethash key result) (funcall f val)))
	     table)
    (make-map-as-undo-harray result nil)))

(defun STH_mapiPartial-2 (f m)
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

(defun STH_mapPartial-2 (f m)
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

(defun STH_app-2 (f m)
  (declare (dynamic-extent f))
  (let ((m (map-as-undo-harray-assure-current m)))
    (maphash #'(lambda (key val)
		 (declare (ignore key))
		 (funcall f val))
	     (map-as-undo-harray--harray m)))
  nil)

(defun STH_appi-2 (f m)
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

(defun STH_foldi-3 (fn result m)
  (let ((*foldi-vector* (vector nil nil nil)))
    (map-as-undo-harray--map-through-pairs
     #'(lambda (key val)
	 (let ((args (foldi-vector key val result)))
	   (declare (dynamic-extent args))
	   (setq result (funcall fn args))))
     m))
  result)

(defun STH_imageToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (declare (ignore key))
		   (push val items))
	       (map-as-undo-harray--harray m))
      items)))

(defun STH_mapToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (push (cons key val) items))
	       (map-as-undo-harray--harray m))
    items)))

(defun STH_domainToList (m) 
  (let ((m (map-as-undo-harray-assure-current m)))
    (let ((items nil))
      (maphash #'(lambda (key val) 
		 (declare (ignore val))
		 (push key items))
	       (map-as-undo-harray--harray m))
    items)))

(defun STH_size (m)
  (let ((m (map-as-undo-harray-assure-current m)))
    (hash-table-count (map-as-undo-harray--harray m))))
