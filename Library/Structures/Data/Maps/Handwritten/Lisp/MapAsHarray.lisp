;;; Modified from Marcel's HArrayAsStringMap.lisp


(defpackage :MapHashtable)
(in-package :MapHashtable)


(eval-when (compile)
  (proclaim '(optimize (safety 0)(space 0) (speed 3)(debug 0))))


(defun make-ctxt-map-as-harray-obj (&key harray-history-pair history)
    (cons harray-history-pair history))

(defmacro ctxt-map-as-harray-obj-harray-history-pair (x) `(car ,x))
(defmacro ctxt-map-as-harray-obj-history (x) `(cdr ,x))

(defstruct (ctxt-map-as-harray-history-obj (:type vector))
  domain-value range-value old-range-value previous reversed)


(defun print-ctxt-map-as-harray-history-obj (obj strm k)
  (declare (ignore k))
  (print-unreadable-object (obj strm :type nil :identity nil)
			   (format strm "[ Key ~A Value ~A Old-Value ~A Rev ~A]"
				   (ctxt-map-as-harray-history-obj-domain-value obj)
				   (ctxt-map-as-harray-history-obj-range-value obj)
				   (ctxt-map-as-harray-history-obj-old-range-value obj)
				   (ctxt-map-as-harray-history-obj-reversed obj))))


(defparameter *ctxt-map-as-harray--initial-harray-size* 100)
(defparameter *ctxt-map-as-harray--rehash-size* 2.0)

(defun ctxt-map-as-harray--make-harray-history-pair (harr hist)
  (cons harr hist))

(defmacro ctxt-map-as-harray--harray-from-pair (pr)
   `(car ,pr))

(defmacro ctxt-map-as-harray--history-from-pair (pr)
   `(cdr ,pr))

(defun ctxt-map-as-harray--harray-map (table)
  (make-ctxt-map-as-harray-obj
     :harray-history-pair (ctxt-map-as-harray--make-harray-history-pair table nil)
     :history nil))

(defun ctxt-map-as-harray--initial-harray-history-pair (x)
  (declare (ignore x))
  (ctxt-map-as-harray--make-harray-history-pair
   (Specware::make-sw-hash-table :size *ctxt-map-as-harray--initial-harray-size*
                                 :rehash-size *ctxt-map-as-harray--rehash-size*)
   nil))

(defmacro ctxt-map-as-harray--set-history (pr hist)
   `(setf (cdr ,pr) ,hist))

(defun ctxt-map-as-harray--harray-history (m)
   (ctxt-map-as-harray--history-from-pair
     (ctxt-map-as-harray-obj-harray-history-pair m)))

(defun ctxt-map-as-harray--harray (m)
   (ctxt-map-as-harray--harray-from-pair
     (ctxt-map-as-harray-obj-harray-history-pair m)))

(defun ctxt-map-as-harray--extend-history (x y old-val old-hist)
   (make-ctxt-map-as-harray-history-obj
     :domain-value x 
     :range-value y 
     :old-range-value old-val
     :previous old-hist 
     :reversed nil))

(defparameter *ctxt-map-as-harray-undo-count* 0)
(defparameter *ctxt-map-as-harray-ref-count* 0)
(defparameter *ctxt-map-as-harray-set-count* 0)

(defvar *undefined* '(:|None|))
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defun ctxt-map-as-harray-assure-current (m)
  (let* ((pr (ctxt-map-as-harray-obj-harray-history-pair m))
	 (m-hist (ctxt-map-as-harray-obj-history m))
	 (a-hist (ctxt-map-as-harray--history-from-pair pr)))

    ;;(format t "~% CTXT ASSURE CURRENT ~% PR ~A ~% M-HIST ~A ~% A-HIST ~A" pr m-hist a-hist)
    (unless (eq m-hist a-hist)
      (let ((last-hist nil) 
	    (curr-hist m-hist))
	;; Follow reversed links to trunk reversing their pointers
	(loop while (and curr-hist (ctxt-map-as-harray-history-obj-reversed curr-hist))
	   do (let ((p-hist (ctxt-map-as-harray-history-obj-previous curr-hist)))
		(setf (ctxt-map-as-harray-history-obj-previous curr-hist) last-hist)
		(setf last-hist curr-hist)
		(setf curr-hist p-hist)))
	;; curr-hist is now the common ancestor link
	(let ((common-ancestor-link curr-hist)
	      (curr-hist a-hist)
	      (table (ctxt-map-as-harray--harray-from-pair pr)))
	  ;;(format t "~%~%  COMMON ANCESTOR ~A ~% CURR HIST ~A ~% TABLE ~A" common-ancestor-link curr-hist table)	  
	  ;; undo until ancestor link
	  (loop while (not (eq curr-hist common-ancestor-link)) do
	    ;;(incf *ctxt-map-as-harray-undo-count*)
	    (let ((x (ctxt-map-as-harray-history-obj-domain-value curr-hist))
		  (val (ctxt-map-as-harray-history-obj-old-range-value curr-hist)))
	      (if (defined? val)
		  (setf (gethash x table) val)
		 (remhash x table)))
	    (setf (ctxt-map-as-harray-history-obj-reversed curr-hist) t)
	    (setf curr-hist (ctxt-map-as-harray-history-obj-previous curr-hist)))
	  (let ((curr-hist last-hist) (last-hist common-ancestor-link))
	    ;; redo reversed links and reverse (restore) their pointers
	    (loop while (not (null curr-hist)) do
	      (let ((x (ctxt-map-as-harray-history-obj-domain-value curr-hist))
		    (val (ctxt-map-as-harray-history-obj-range-value curr-hist)))
		(if (defined? val)
		    (setf (gethash x table) val)
		   (remhash x table)))
	      (setf (ctxt-map-as-harray-history-obj-reversed curr-hist) nil)
	      (let ((p-hist (ctxt-map-as-harray-history-obj-previous curr-hist)))
	        (setf (ctxt-map-as-harray-history-obj-previous curr-hist)
		      last-hist)
		(setf last-hist curr-hist)
		(setf curr-hist p-hist)))
	    (ctxt-map-as-harray--set-history pr last-hist)))))))

(defvar emptyMap (ctxt-map-as-harray--harray-map (Specware::make-sw-hash-table :size 0)))

(defun ctxt-map-as-harray--update (m x y)
  (ctxt-map-as-harray-assure-current m)
  ;;(incf *ctxt-map-as-harray-set-count*)
  (let* ((hist-tab-pair
	  (if (and (eq m emptyMap) (defined? y))
	    (ctxt-map-as-harray--initial-harray-history-pair x)
	    (ctxt-map-as-harray-obj-harray-history-pair m)))
	 (table (ctxt-map-as-harray--harray-from-pair hist-tab-pair))
	 (old-val (gethash x table *undefined*)))
    (if (eq y old-val)
      m					; Optimize special case
      (progn
	(if (eq y *undefined*)
	  (progn (remhash x table))
	  (progn (setf (gethash x table) y)))
	(let ((hist-val (ctxt-map-as-harray--extend-history
			 x y old-val (ctxt-map-as-harray-obj-history m))))
	  (ctxt-map-as-harray--set-history hist-tab-pair hist-val)
	  (make-ctxt-map-as-harray-obj :harray-history-pair hist-tab-pair
				       :history hist-val))))))

(defun ctxt-map-as-harray--map-through-pairs (fn m)
  (when (> (the fixnum (numItems m)) 0)
    (ctxt-map-as-harray-assure-current m)
    (maphash fn (ctxt-map-as-harray--harray m))))


;;; The Hash Table interface functions

(defun numItems (m)
  (ctxt-map-as-harray-assure-current m)
  (hash-table-count (ctxt-map-as-harray--harray m)))

(defun apply-2 (m x)
  ;; (incf *ctxt-map-as-harray-ref-count*)
  (if (eq (numItems m) 0)
      *undefined*
    (progn (ctxt-map-as-harray-assure-current m)
	   (gethash x (ctxt-map-as-harray--harray m)
		    *undefined*))))
(defun |!apply| (pr)
  (apply-2 (car pr) (cdr pr)))


;;; Some y is stored in array, as it is usually accessed more often than set
(defun update-3 (m x y)
  (ctxt-map-as-harray--update m x (mkSome y)))

(defun remove-2 (m x)
  (ctxt-map-as-harray--update m x *undefined*))

(defun |!remove| (pr)
  (ctxt-map-as-harray--update (car pr) (cdr pr) *undefined*))

(defun mapi-2 (f table)
  (declare (dynamic-extent f))
  (let ((sz (numItems table)))
    (declare (fixnum sz))
    (if (= sz 0)
      emptyMap
      (progn (ctxt-map-as-harray-assure-current table)
	     (let ((result (Specware::make-sw-hash-table :size sz
                                                         :rehash-size
                                                         *ctxt-map-as-harray--rehash-size*)))
	       (maphash #'(lambda (key val)
			    (setf (gethash key result)
			      (mkSome (funcall f (cons key (cdr val))))))
			(ctxt-map-as-harray--harray table))
	       (ctxt-map-as-harray--harray-map result))))))

(defun map-2 (f table)
  (declare (dynamic-extent f))
  (let ((sz (numItems table)))
    (declare (fixnum sz))
    (if (= sz 0)
      emptyMap
      (progn (ctxt-map-as-harray-assure-current table)
	     (let ((result (Specware::make-sw-hash-table :size sz
                                                         :rehash-size
                                                         *ctxt-map-as-harray--rehash-size*)))
	       (maphash #'(lambda (key val)
			    (setf (gethash key result)
			      (mkSome (funcall f (cdr val)))))
			(ctxt-map-as-harray--harray table))
	       (ctxt-map-as-harray--harray-map result))))))

(defun mapiPartial-2 (f table)
  (declare (dynamic-extent f))
  (let ((sz (numItems table)))
    (declare (fixnum sz))
    (if (= sz 0)
      emptyMap
      (progn
	(ctxt-map-as-harray-assure-current table)
	(let ((result (Specware::make-sw-hash-table :size *ctxt-map-as-harray--initial-harray-size*
                                                    :rehash-size
                                                    *ctxt-map-as-harray--rehash-size*)))
	  (maphash #'(lambda (key val)
		       (let ((val (funcall f (cdr val))))
			 (unless (equal val *undefined*)
			   (setf (gethash key result) val))))
		   (ctxt-map-as-harray--harray table))
	  (ctxt-map-as-harray--harray-map result))))))

(defun mapPartial-2 (f table)
  (declare (dynamic-extent f))
  (let ((sz (numItems table)))
    (declare (fixnum sz))
    (if (= sz 0)
      emptyMap
      (progn
	(ctxt-map-as-harray-assure-current table)
	(let ((result (Specware::make-sw-hash-table :size *ctxt-map-as-harray--initial-harray-size*
                                                    :rehash-size
                                                    *ctxt-map-as-harray--rehash-size*)))
	  (maphash #'(lambda (key val)
		       (let ((val (funcall f (cdr val))))
			 (unless (equal val *undefined*)
			   (setf (gethash key result) val))))
		   (ctxt-map-as-harray--harray table))
	  (ctxt-map-as-harray--harray-map result))))))

(defun app-2 (f table)
  (declare (dynamic-extent f))
  (when (> (the fixnum (numItems table)) 0)
    (ctxt-map-as-harray-assure-current table)
    (maphash #'(lambda (key val)
		 (declare (ignore key))
		 (funcall f (cdr val)))
	     (ctxt-map-as-harray--harray table)))
  nil)

(defun appi-2 (f table)
  (declare (dynamic-extent f))
  (when (> (the fixnum (numItems table)) 0)
    (ctxt-map-as-harray-assure-current table)
    (maphash #'(lambda (key val)
		 (let ((args (cons key (cdr val))))
		   (declare (dynamic-extent args))
		   (funcall f args)))
	     (ctxt-map-as-harray--harray table)))
  nil)

;;;(defvar *foldi-vector* (vector nil nil nil))
;;;
;;;(defun foldi-vector (x y z)
;;;  (setf (svref *foldi-vector* 0) x)
;;;  (setf (svref *foldi-vector* 1) y)
;;;  (setf (svref *foldi-vector* 2) z)
;;;  *foldi-vector*)

#+allegro
(progn (setf (get 'foldi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil nil))
       (setf (get 'app 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'appi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get '|!map| 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil))
       (setf (get 'mapi 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE) '(t nil)))


#+allegro
(setf (get 'ctxt-map-as-harray--map-through-pairs 'EXCL::DYNAMIC-EXTENT-ARG-TEMPLATE)
  (list t nil))

(defun foldi-3 (fn result table)
  (declare (dynamic-extent fn) (optimize (speed 3) (safety 0) (debug 0)))
  (ctxt-map-as-harray--map-through-pairs
     #'(lambda (key val)
	 (let ((args (vector key (cdr val) result)))
	   (declare (dynamic-extent args))
	   (setq result (funcall fn args))))
     table)
  result)

(defun imageToList (table) 
  (when (> (the fixnum (numItems table)) 0)
    (ctxt-map-as-harray-assure-current table)
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (declare (ignore key))
		   (push (cdr val) items))
	       (ctxt-map-as-harray--harray table))
      items)))

(defun mapToList (table) 
  (when (> (the fixnum (numItems table)) 0)
    (ctxt-map-as-harray-assure-current table)
    (let ((items nil))
      (maphash #'(lambda (key val) 
		   (push (cons key (cdr val)) items))
	       (ctxt-map-as-harray--harray table))
    items)))

(defun domainToList (table) 
  (when (> (the fixnum (numItems table)) 0)
    (ctxt-map-as-harray-assure-current table)
    (let ((items nil))
      (maphash #'(lambda (key val) 
		 (declare (ignore val))
		 (push key items))
	       (ctxt-map-as-harray--harray table))
    items)))




;;;(defparameter emptyHashTable SW-USER::emptyHashTable )
;;;
;;;(defun numItemsInHashTable (table)
;;;  (SW-USER::numItemsInHashTable table))
;;;
;;;(defun insertInHashTable (table index object)
;;;  (format t "~% INSERT IN HASH TABLE INDEX ~A ~% OBJECT ~A" index object)
;;;  (SW-USER::insertInHashTable table index object))
;;;
;;;(defun removeFromHashTable (table index) 
;;;  (sw-user::removeFromHashTable table index))
;;;
;;;(defun listItemsInHashTable (table) 
;;;  (sw-user::listItemsInHashTable table))
;;;
;;;(defun listDomainInHashTable (table) 
;;;  (sw-user::listDomainInHashTable table))
;;;
;;;(defun findInHashTable (table index)
;;;  (let ((result (sw-user::findInHashTable table index)))
;;;    (format t "~% FIND IN HASH TABLE INDEX ~A ~% RESULT ~A" index result)
;;;    result))
