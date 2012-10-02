;;; Specware interface to opticl

(defpackage :Matrix (:use :cl))

(in-package :Matrix)

;;; type Matrix a

;;; type Index  = Nat
;;; type Indices = List Index
;;; 
;;; op [a] dimensions : Matrix a -> Indices

(defun dimensions (matrix)
  (array-dimensions matrix))

;;; op [a] newMatrix (dimensions : Indices) (initial_value : a) : Matrix a

(defun uniformMatrix-1-1 (dimensions initial_value)
  (make-array dimensions :initial-value initial_value))

;;; op [a] getregion (matrix: Matrix a) (lows : Indices) (highs : Indices) : Matrix a
;;; op [a] putregion (matrix: Matrix a) (lows : Indices) (highs : Indices) (region: Matrix a) : Matrix a

(defun getregion-1-1-1 (matrix lows highs)
  ;; grossly inefficient, and ugly to boot, but it works...
  ;; alternatively, could do our own indexing into displaced vectors 
  (let* ((new-dimensions (mapcar #'(lambda (low high) (- high low)) lows highs))
         (new-matrix (make-array new-dimensions)))
    ;; scan (rather inefficiently) indexes through the cartesian product of indices
    (labels ((scan (indices pending-dimensions)
               (cond ((null pending-dimensions)
                      ;; Ugly...
                      ;; Because aref takes dimensions as multiple arguments 
                      ;; rather than a list of values, we need to use apply.
                      (setf (apply #'aref new-matrix indices)
                            (apply #'aref matrix 
                                   (mapcar #'(lambda (low offset) (+ low offset)) 
                                           lows 
                                           indices))))
                     (t
                      (let ((still-pending-dimensions (cdr pending-dimensions)))
                        (dotimes (i (car pending-dimensions))
                          (scan (cons i indices) still-pending-dimensions)))))))
      (scan '() (reverse new-dimensions)))
    new-matrix))

;;; op [a] get : Matrix a -> Indices -> a
;;; op [a] put : Matrix a -> Indices -> a -> ()

(defun get-1-1 (matrix indices)
  (apply #'aref matrix indices))

(defun put-1-1-1 (matrix indices value)
  (setf (apply #'aref matrix indices) value))

;;; op [a,b] map (f : a -> b) (matrix: Matrix a) : Matrix b

(defun map-1-1 (f old-matrix)
  ;; note: this processes the elements in an arbitrary order
  (let* ((dimensions (array-dimensions   old-matrix))
         (etype      (array-element-type old-matrix))
         (new-matrix (make-array dimensions :element-type etype)))
    ;; To simplify scan, view matrices as 1-dimensional vectors.
    (let* ((size (apply #'* dimensions))
           (old-vector (make-array size :displaced-to old-matrix :element-type etype))
           (new-vector (make-array size :displaced-to new-matrix :element-type etype)))
      (dotimes (i size)
        (setf (aref new-vector i) (funcall f (aref old-vector i)))))
    new-matrix))

;;; op [a,b] foldl (f : b * a -> b) (base: b) (matrix: Matrix a) : b
;;; op [a,b] foldr (f : a * b -> b) (base: b) (matrix: Matrix a) : b

;;; Note: To avoid consing lists of indices, we access the elements
;;;       of the matrix as if it is a simple vector in lexicographic 
;;;       order.
;;;
;;;  0       0       ... 0
;;;  0       0       ... 1
;;;  ...
;;;  0       Max[1]  ... Max[n]
;;;  1       0       ... 0
;;;  ....
;;;  Max[0]  Max[1]  ... Max[n]
;;;

(defun foldl-1-1-1 (f value matrix)
  (let* ((dimensions (array-dimensions matrix))
         (size (apply #'* dimensions))
         (vector (make-array size :displaced-to matrix)))
    (dotimes (i size)
      (setq value (funcall f value (aref vector i)))))
  value)

(defun foldr-1-1-1 (f value matrix)
  (let* ((dimensions (array-dimensions matrix))
         (size (apply #'* dimensions))
         (vector (make-array size :displaced-to matrix)))
    (dotimes (i size)
      (setq value (funcall f (aref vector i) value))))
  value)

;;; op [a,b] foldli (f : Indices * b * a * -> b) (base: b) (matrix: Matrix a) : b
;;; op [a,b] foldri (f : Indices * a * b * -> b) (base: b) (matrix: Matrix a) : b

;;; These are general, but incredibly inefficient
;;; Optimize with special cases for 1-D, 2-D (3-D ?)

(defun foldli-1-1-1 (f value matrix)
  (let* ((dimensions (array-dimensions matrix)))
    (labels ((scan (indices pending-dimensions)
               (cond ((null pending-dimensions)
                      (let* ((indices (reverse indices))
                             (element (apply #'aref matrix indices)))
                        (setq value (funcall f indices value element))))
                     (t
                      (let ((still-pending (cdr pending-dimensions)))
                        (dotimes (i (car pending-dimensions))
                          (scan (cons i indices) still-pending)))))))
      (scan '() dimensions)))
  value)

(defun foldri-1-1-1 (f value matrix)
  (let* ((dimensions (array-dimensions matrix)))
    (labels ((scan (indices pending-dimensions)
               (cond ((null pending-dimensions)
                      (let* ((indices (reverse indices))
                             (element (apply #'aref matrix indices)))
                        (setq value (funcall f indices element value))))
                     (t
                      (let ((still-pending (cdr pending-dimensions)))
                        (dotimes (i (car pending-dimensions))
                          (scan (cons i indices) still-pending)))))))
      (scan '() dimensions)))
  value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
