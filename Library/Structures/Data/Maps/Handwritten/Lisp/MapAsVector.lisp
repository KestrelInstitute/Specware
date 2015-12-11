;;; Implements a Map with domain Nat as a vector.
;;; Only works if access is single-threaded!

(defpackage :MapsAsVectors)
(defpackage :MapVec)
(in-package :MapVec)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3) (debug 3) (safety 0))))

;;(declaim (inline map-as-vector--update V_update-3 V_eval-2 defined? MapsAsVectors::update-1-1-1 MapsAsVectors::tmApply-2))

(defvar *undefined* '(:|None|))
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defparameter *map-as-vector--initial-vector-size* 50)
(defparameter *map-as-vector--max-vector-size* 1000000)
(defparameter *map-as-vector-resize-factor* 2.0)

(defmacro map-as-vector--initial-vector ()
  `(make-array *map-as-vector--initial-vector-size*
	      :initial-element *undefined*))

(defun make-vector-same-size (table)
  (make-array (length table)
	      :initial-element *undefined*))

(defun grow-map-vector (vec large-i)
  (when (> large-i *map-as-vector--max-vector-size*)
    (error "Trying to grow V vector too large ~a." large-i))
  (let ((new-vec (make-array (min *map-as-vector--max-vector-size*
				  (floor (* large-i *map-as-vector-resize-factor*)))
			     :initial-element *undefined*)))
    (loop for i from 0 to (- (length vec) 1)
	  do (setf (svref new-vec i) (svref vec i)))
    new-vec))
    

(defparameter *map-as-vector-miss-count* 0)
(defparameter *map-as-vector-count* 0)
(defparameter *map-as-vector-copy-count* 0)
(defparameter *map-as-vector-ref-count* 0)
(defparameter *map-as-vector-alist-ref-count* 0)
(defparameter *map-as-vector-alist-elt-ref-count* 0)
(defparameter *map-as-vector-set-count* 0)

(defparameter V_empty_map (map-as-vector--initial-vector))

(defun map-as-vector--update (m x y)
  (declare (fixnum x) (simple-vector m))
  (when (eq m V_empty_map)
    (setq m (map-as-vector--initial-vector)))
  (when (>= x (length m))
    (setq m (grow-map-vector m x)))
  (setf (svref m x) y)
  m)

(defun print-map (m)
  (let ((line-items 0))
    (declare (fixnum line-items) (simple-vector m))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (when (> (incf line-items) 10)
		   (terpri)
		   (setq line-items 0))
		 (format t "~3D:~4D " x val))))))

;;; The Vector interface functions

(defun V_numItems (m)
  (declare (simple-vector m))
  (loop for y across m
     count (not (eq y *undefined*))))

(defun V_apply-2 (m x)
  (declare (fixnum x) (simple-vector m))
  ;(incf *map-as-vector-ref-count*)
  (if (>= x (length m))
      *undefined*
      (let ((val (svref m x)))
        (if (eq val *undefined*) *undefined*
            (mkSome val)))))

(defun V_apply (pr)
  (V_apply-2 (car pr) (cdr pr)))

(defun V_map_eval-3 (m x default)
  (declare (fixnum x) (simple-vector m))
  ;(incf *map-as-vector-ref-count*)
  (if (>= x (length m))
      *undefined*
      (let ((val (svref m x)))
        (if (eq val *undefined*) default
            val))))

(defun V_map_eval (triple)
  (V_map_eval-3 (svref triple 0) (svref triple 1) (svref triple 2)))

(defun eval-error (m x)
  ;(print-map m)
  (error "V_eval: out-of-domain reference: ~a length: ~a" x (length m)))

(defun V_eval-2 (m x)
  (declare (fixnum x) (simple-vector m))
  ;(incf *map-as-vector-ref-count*)
  (if (>= x (length m))
      (eval-error m x)
      (let ((val (svref m x)))
        (if (eq val *undefined*)
            (eval-error m x)
            val))))

(defsetf V_eval-2 (v i) (val)
  `(setf (,v ,i) ,val))

(defun V_eval (pr)
  (V_eval-2 (car pr) (cdr pr)))

(defun V_update-3 (m x y)
  (map-as-vector--update m x y))

(defun V_remove-2 (m x)
  (map-as-vector--update m x *undefined*))

(defun V_remove (pr)
  (map-as-vector--update (car pr) (cdr pr) *undefined*))

(defun V_mapi-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (let ((result (make-vector-same-size m)))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (setf (svref result x) (funcall f (cons x val))))))
    result))

(defun V_map-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (let ((result (make-vector-same-size m)))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (setf (svref result x) (funcall f val)))))
    result))

(defun V_mapiPartial-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (let ((result (make-vector-same-size m)))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (let ((val (funcall f (cons x val))))
		   (unless (equal val *undefined*) ; Note equal not eq
		     ;; (:|Some| . realval)
		     (setf (svref result x) (cdr val)))))))
    result))

(defun V_mapPartial-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (let ((result (map-as-vector--initial-vector)))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (let ((val (funcall f val)))
		   (unless (equal val *undefined*) ; Note equal not eq
		     ;; (:|Some| . realval)
		     (setf (svref result x) (cdr val)))))))
    result))

(defun V_app-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (loop for x from 0 to (- (length m) 1)
     do (let ((val (svref m x)))
          (when (defined? val)
            (funcall f val))))
  nil)

(defun V_appi-2 (f m)
  (declare (dynamic-extent f) (simple-vector m))
  (loop for x from 0 to (- (length m) 1)
     do (let ((val (svref m x)))
          (when (defined? val)
            (funcall f (cons x val))))))

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

(defun V_foldi-3 (fn result m)
  (declare (simple-vector m))
  (let ((*foldi-vector* (vector nil nil nil)))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (let ((args (foldi-vector x val result)))
		   (declare (dynamic-extent args))
		   (setq result (funcall fn args))))))
    result))

(defun V_imageToList (m)
  (declare (simple-vector m))
  (let ((items nil))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (push val items))))
    items))

; TODO Same as V_imageToList?  Deprecate one?
(defun V_rangeToList (m)
  (declare (simple-vector m))
  (let ((items nil))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (push val items))))
    items))

(defun V_mapToList (m)
  (declare (simple-vector m))
  (let ((items nil))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (push (cons x val) items))))
    items))

(defun V_domainToList (m)
  (declare (simple-vector m))
  (let ((items nil))
    (loop for x from 0 to (- (length m) 1)
	  do (let ((val (svref m x)))
	       (when (defined? val)
		 (push x items))))
    items))

