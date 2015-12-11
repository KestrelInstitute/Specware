;;; Modified from MapAsSTHarray.lisp which is modified from Marcel's HArrayAsStringMap.lisp
;;; Modified for backtracking usage, where only one version is used at any time,
;;; but once a version is backtracked from, it is is likely never to be referenced again.
;;; Only keep forward links to allow for garbage collection of unused nodes.
;;; Rather than have a list of undos, keep the undo/information in the node with a pointer
;;; to the next node. When you undo, the pointers are reversed.
;;; Domain must be an initial segment of Nat.

(defpackage :MapBTV)
(in-package :MapBTV)

(eval-when (compile)
  (proclaim '(optimize (space 1) (speed 3)(debug 3))))


(defmacro make-map-as-undo-vector (vec next)
  `(vector ,vec ,next nil nil))

(defmacro map-as-undo-vector--vector (x) `(svref ,x 0))
(defmacro map-as-undo-vector--next (x) `(svref ,x 1))
(defmacro map-as-undo-vector-current? (x) `(null (svref ,x 1)))
(defmacro map-as-undo-vector--dom-elt (x) `(svref ,x 2))
(defmacro map-as-undo-vector--saved-val (x) `(svref ,x 3))

(defmacro map-as-undo-vector--set-next (m next)
   `(setf (svref ,m 1) ,next))

(defmacro set-undo-info (v domain-value old-range-value)
  `(progn (setf (svref ,v 2) ,domain-value)
          (setf (svref ,v 3) ,old-range-value)))

(defvar *undefined* '(:|None|))
(defun defined? (val) 
  (not (eq val *undefined*)))

(defun mkSome (val)
  (cons ':|Some| val))

(defparameter *map-as-undo-vector--initial-vector-size* 250)
(defparameter *map-as-undo-vector--max-vector-size* 100000)
(defparameter *map-as-undo-vector-resize-factor* 2.0)

(defmacro map-as-undo-vector--initial-vector ()
  `(make-array *map-as-undo-vector--initial-vector-size*
	      :initial-element *undefined*))

(defun make-vector-same-size (table)
  (make-array (length table)
	      :initial-element *undefined*))

(defun grow-map-vector (vec large-i)
  (when (> large-i *map-as-undo-vector--max-vector-size*)
    (error "Trying to grow BTV vector too large ~a." large-i))
  (let ((new-vec (make-array (min *map-as-undo-vector--max-vector-size*
				  (floor (* large-i *map-as-undo-vector-resize-factor*)))
			     :initial-element *undefined*)))
    (loop for i from 0 to (- (length vec) 1)
	  do (setf (svref new-vec i) (svref vec i)))
    (make-map-as-undo-vector new-vec nil)))
    

(defparameter *map-as-undo-vector-miss-count* 0)
(defparameter *map-as-undo-vector-undo-count* 0)
(defparameter *map-as-undo-vector-copy-count* 0)
(defparameter *map-as-undo-vector-ref-count* 0)
(defparameter *map-as-undo-vector-alist-ref-count* 0)
(defparameter *map-as-undo-vector-alist-elt-ref-count* 0)
(defparameter *map-as-undo-vector-set-count* 0)

(defparameter BTV_empty_map (make-map-as-undo-vector (map-as-undo-vector--initial-vector) nil))

(defmacro map-as-undo-vector-assure-current (m)
  `(if (map-as-undo-vector-current? ,m)
      ,m
      (map-as-undo-vector-make-current ,m)))
	     
(defun map-as-undo-vector-make-current (m)
  (let* ((vec (map-as-undo-vector--vector m))
	     ;; Follow links to curr reversing as you go
	     (live (do ((curr m next)
			(next (prog1 (map-as-undo-vector--next m)
				(map-as-undo-vector--set-next m nil))
			      (prog1 (map-as-undo-vector--next next)
				(map-as-undo-vector--set-next next curr))))
		       ((null next) curr)
		     ())))   ; empty body because action in prog1
        ;(break "Nnot current: ~a" m)
        ;(incf *map-as-undo-vector-miss-count*)
	;; Follow links back to m undoing as we go and storing redo info
	(do ((curr live next)
	     (next (map-as-undo-vector--next live)
		   (map-as-undo-vector--next next)))
	    ((null next) ())
	  (let ((dom-elt (map-as-undo-vector--dom-elt next)))
            ;(incf *map-as-undo-vector-undo-count*)
	    ;(format t "Current: ~a~%~a -> ~a~%" curr dom-elt (svref vec dom-elt)
	    (set-undo-info curr dom-elt (svref vec dom-elt))
	    (let ((old-val (map-as-undo-vector--saved-val next)))
	      (setf (svref vec dom-elt) old-val))))
	m))

(defun map-as-undo-vector--update (m x y)
  (declare (fixnum x))
  (when (eq m BTV_empty_map)
    (setq m (make-map-as-undo-vector (map-as-undo-vector--initial-vector) nil)))
  (let ((m (map-as-undo-vector-assure-current m)))
    ; (incf *map-as-undo-vector-set-count*)
    (let ((vec (map-as-undo-vector--vector m)))
      (if  (>= x (length vec))
	   (let* ((new-m (grow-map-vector vec x))
		  (vec (map-as-undo-vector--vector new-m)))
	     (setf (svref vec x) y)
	     new-m)
	   (let ((old-val (svref vec x)))
	     (if (eq y old-val)
		 m			; Optimize special case
		 (progn
		   (setf (svref vec x) y)
		   (set-undo-info m x old-val)
		   (let ((new-m (make-map-as-undo-vector vec nil)))
		     (map-as-undo-vector--set-next m new-m)
		     new-m))))))))

(defun print-map (m)
  (setq m (map-as-undo-vector-assure-current m))
  (let ((vec (map-as-undo-vector--vector m))
	(line-items 0))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (when (> (incf line-items) 10)
		   (terpri)
		   (setq line-items 0))
		 (format t "~3D:~4D " x val))))))

;;; The Vector interface functions

(defun BTV_numItems (m)
  (let ((m (map-as-undo-vector-assure-current m)))
    (loop for y across (map-as-undo-vector--vector m)
	  count (not (eq y *undefined*)))))

(defun BTV_apply-2 (m x)
  (declare (fixnum x))
  ;(incf *map-as-undo-vector-ref-count*)
  (setq m (map-as-undo-vector-assure-current m))
  (let ((vec (map-as-undo-vector--vector m)))
    (if (>= x (length vec))
	*undefined*
	(let ((val (svref vec x)))
	  (if (eq val *undefined*) *undefined*
	      (mkSome val))))))

(defun BTV_apply (pr)
  (BTV_apply-2 (car pr) (cdr pr)))

(defun eval-error (m x)
  (print-map m)
  (error "BTV_eval: out-of-domain reference: ~a" x))

(defun BTV_eval-2 (m x)
  (declare (fixnum x))
  ;(incf *map-as-undo-vector-ref-count*)
  (setq m (map-as-undo-vector-assure-current m))
  (let ((vec (map-as-undo-vector--vector m)))
    (if (>= x (length vec))
	(eval-error m x)
	(let ((val (svref vec x)))
	  (if (eq val *undefined*)
	      (eval-error m x)
	      val)))))

(defun BTV_eval (pr)
  (BTV_eval-2 (car pr) (cdr pr)))


;;; Some y is stored in array, as it is usually accessed more often than set
(defun BTV_update-3 (m x y)
  (map-as-undo-vector--update m x y))

(defun BTV_remove-2 (m x)
  (map-as-undo-vector--update m x *undefined*))

(defun BTV_remove (pr)
  (map-as-undo-vector--update (car pr) (cdr pr) *undefined*))

(defun BTV_mapi-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector curr-m))
	 (result (make-vector-same-size vec)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (setf (svref result x) (funcall f (cons x val))))))
    (make-map-as-undo-vector result nil)))

(defun BTV_map-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector curr-m))
	 (result (make-vector-same-size vec)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (setf (svref result x) (funcall f val)))))
    (make-map-as-undo-vector result nil)))

(defun BTV_mapiPartial-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-vector-assure-current m))
         (vec (map-as-undo-vector--vector curr-m))
         (result (make-vector-same-size vec)))
    (loop for x from 0 to (- (length vec) 1)
       do (let ((val (svref vec x)))
            (when (defined? val)
              (let ((val (funcall f (cons x val))))
                (unless (equal val *undefined*) ; Note equal not eq
                  ;; (:|Some| . realval)
                  (setf (svref result x) (cdr val)))))))
    (make-map-as-undo-vector result nil)))

(defun BTV_mapPartial-2 (f m)
  (declare (dynamic-extent f))
  (let* ((curr-m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector curr-m))
	 (result (map-as-undo-vector--initial-vector)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (let ((val (funcall f val)))
		   (unless (equal val *undefined*) ; Note equal not eq
		     ;; (:|Some| . realval)
		     (setf (svref result x) (cdr val)))))))
    (make-map-as-undo-vector result nil)))

(defun BTV_app-2 (f m)
  (declare (dynamic-extent f))
  (let* ((m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (funcall f val)))))
  nil)

(defun BTV_appi-2 (f m)
  (declare (dynamic-extent f))
  (let* ((m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (funcall f (cons x val)))))))

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

(defun BTV_foldi-3 (fn result m)
  (let* ((m (map-as-undo-vector-assure-current m))
	 (vec (map-as-undo-vector--vector m))
	 (*foldi-vector* (vector nil nil nil)))
    (loop for x from 0 to (- (length vec) 1)
	  do (setq m (map-as-undo-vector-assure-current m)) ; In case fn is modifying m
	     (let ((val (svref vec x)))
	       (when (defined? val)
		 (let ((args (foldi-vector x val result)))
		   (declare (dynamic-extent args))
		   (setq result (funcall fn args))))))
    result))

(defun BTV_imageToList (m) 
  (let ((m (map-as-undo-vector-assure-current m))
	(items nil)
	(vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (push val items))))
    items))

(defun BTV_rangeToList (m) 
  (let ((m (map-as-undo-vector-assure-current m))
	(items nil)
	(vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (push val items))))
    items))

(defun BTV_mapToList (m)
  (let ((m (map-as-undo-vector-assure-current m))
	(items nil)
	(vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (push (cons x val) items))))
    items))

(defun BTV_domainToList (m)
  (let ((m (map-as-undo-vector-assure-current m))
	(items nil)
	(vec (map-as-undo-vector--vector m)))
    (loop for x from 0 to (- (length vec) 1)
	  do (let ((val (svref vec x)))
	       (when (defined? val)
		 (push x items))))
    items))

