;;; Specware interface to opticl

(defpackage :OptiCL (:use :Common-Lisp))
(in-package :OptiCL)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; type Image
;;; type Row         = Nat
;;; type Column      = Nat
;;; type Coordinates = Row * Column

(defmacro coordinates-y (coordinates)
  `(car ,coordinates))

(defmacro coordinates-x (coordinates)
  `(cdr ,coordinates))

(defmacro coordinates (row column)
  `(cons ,row ,column))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op height : BitMap -> Row
;;; op width  : BitMap -> Column
;;; op size   : BitMap -> Coordinates

(defun width (image) 
  (with-image-bounds (height width) image
    (declare (ignore height))
    width))

(defun height (image)
  (with-image-bounds (height width) image
    (declare (ignore width))
    height))

(defun size (image)
  (with-image-bounds (height width) image
    (coordinates height width)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op get    : BitMap -> Coordinates -> Pixel
;;; op put    : BitMap -> Coordinates -> Pixel -> ()

(defun get-2 (image coordinates)
  (let ((y (coordinates-y coordinates))
        (x (coordinates-x coordinates)))
    (pixel image y x)))

(defun put-3 (image coordinates pixel)
  (let ((y (coordinates-y coordinates))
        (x (coordinates-x coordinates)))
    (setf (pixel image y x) pixel)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; op getregion (image: Image) (bottom : Row) (left : Column) (top: Row) (right: Column) : Image
;;; op putregion (image: Image) (bottom : Row) (left : Column) (region: Image) : Image

(defun getregion-5 (image bottom left top right) 
  (declare (ignore bottom left top right))
  image)

(defun putregion-4 (image bottom left region)
  (let ((top   (+ bottom (height region)))
        (right (+ left   (width region))))
    (set-region-pixels (y x bottom left top right) image
       (pixel region y x))))
  
(defmacro do-region-pixels ((i-var j-var y1 x1 y2 x2) image &body body)
  (declare (ignorable image))
  `(loop for ,i-var fixnum from ,y1 below ,y2
         do (loop for ,j-var fixnum from ,x1 below ,x2
                  do ,@body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op map (f : Pixel -> Pixel) (image: Image) : Image

(defun copy-image (image)
  image)

(defun map-2 (f old)
  (let ((new (copy-image old)))
    (set-pixels (y x) new
      (funcall f (pixel old y x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op [a] foldl : (f : a * Pixel -> a) (base: a) (image: Image) : a
;;; op [a] foldr : (f : Pixel * a -> a) (base: a) (image: Image) : a

(defun foldl-3 (f value image)
  (do-pixels (y x) image
    (setf value (funcall f value (pixel image y x))))
  value)

(defun foldr-3 (f value image)
  (do-pixels (y x) image
    (setf value (funcall f (pixel image y x) value)))
  value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op [a] foldli : (f : a * Pixel * Coordinates -> a) (base: a) (image: Image) : a
;;; op [a] foldri : (f : Pixel * a * Coordinates -> a) (base: a) (image: Image) : a

(defun foldli-3 (f value image)
  (do-pixels (y x) image
    (setf value (funcall f value (pixel image y x) y x)))
  value)

;;; op [a] foldri : (f : Pixel * a * Coordinates -> a) (base: a) (bitMap: BitMap) : a
(defun foldri-3 (f value image)
  (do-pixels (y x) image
    (setf value (funcall f (pixel image y x) value y x)))
  value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op readImageFile (filename : FileName) : Image
;;; op writeImageFile (filename : FileName) (image : Image) : ()

(defun readImageFile (filename)
  (read-image-file filename))

(defun writeImageFile-2 (filename image)
  (write-image-file filename image)
  ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
