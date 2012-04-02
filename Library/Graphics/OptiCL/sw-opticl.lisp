;;; Specware interface to opticl

(require :OptiCL)

(defpackage :RGB    (:use :Common-Lisp :OptiCL))
(defpackage :RGBA   (:use :Common-Lisp :OptiCL))
(defpackage :Image  (:use :Common-Lisp :OptiCL))
(in-package :Image)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; type RGB  a 
;;; type RGBA a 
;;; 
;;; op [a] RGB.red    (pixel : RGB  a) : a
;;; op [a] RGB.green  (pixel : RGB  a) : a
;;; op [a] RGB.blue   (pixel : RGB  a) : a
;;; 
;;; op [a] RGBA.red   (pixel : RGBA a) : a
;;; op [a] RGBA.green (pixel : RGBA a) : a
;;; op [a] RGBA.blue  (pixel : RGBA a) : a
;;; op [a] RGBA.alpha (pixel : RGBA a) : a

;;; probably could be macros...

(defun RGB::red    (pixel) (first  pixel)) 
(defun RGB::green  (pixel) (second pixel))
(defun RGB::blue   (pixel) (third  pixel))
(defun RGB::mkRGB-3 (red green blue) (list red green blue))

(defun RGBA::red   (pixel) (first  pixel))
(defun RGBA::green (pixel) (second pixel))
(defun RGBA::blue  (pixel) (third  pixel))
(defun RGBA::alpha (pixel) (fourth pixel))
(defun RGBA::mkRGBA-4 (red green blue alpha) (list red green blue alpha))

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
    width))

(defun height (image)
  (with-image-bounds (height width) image
    height))

(defun size (image)
  (with-image-bounds (height width) image
    (coordinates height width)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op get    : BitMap -> Coordinates -> Pixel
;;; op put    : BitMap -> Coordinates -> Pixel -> ()

(defun get-1-1 (image coordinates)
  (let ((y (coordinates-y coordinates))
        (x (coordinates-x coordinates)))
    ;; pixel  returns multiple values
    ;; pixel* returns a single list of those values
    (if (singleValued? image)
        (pixel image y x)
        (pixel* image y x))))

(defun put-1-1-1 (image coordinates pixel)
  (let ((y (coordinates-y coordinates))
        (x (coordinates-x coordinates)))
    ;; setf pixel  expects multiple arguments
    ;; setf pixel* expects one arguments that is a list of values
    (if (singlevalued? image)
        (setf (pixel image y x) pixel)
        (setf (pixel* image y x) pixel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; op getregion (image: Image) (bottom : Row) (left : Column) (top: Row) (right: Column) : Image
;;; op putregion (image: Image) (bottom : Row) (left : Column) (region: Image) : Image

(defun getregion-1-1-1-1-1 (image bottom left top right) 
  (declare (ignore bottom left top right))
  image)

(defun putregion-1-1-1-1 (image bottom left region)
  (let ((top   (+ bottom (height region)))
        (right (+ left   (width region))))
    (set-region-pixels (y x bottom left top right) image
      ;; pixel returns multiple values
      ;; set-region-pixels expects multiple values for each pixel
      (pixel region y x))))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op map (f : Pixel -> Pixel) (image: Image) : Image

(defun copy-image (image)
  image)

(defun map-1-1 (f image)
  (let ((new (copy-image image)))
    (if (singleValued? image)

        (set-pixels (y x) new
          (let ((old-pixel (pixel image y x)))
            ;; pixel returns the pixel as a single value
            (let ((new-pixel (funcall f old-pixel)))
              ;; set-pixels expects multiple values, but we have just one here
              new-pixel)))

        (set-pixels (y x) new
          (let ((old-pixel (pixel* image y x)))
            ;; pixel* returns the pixel as a list of values
            (let ((new-pixel (funcall f old-pixel)))
              ;; set-pixels expects multiple values, not a list of values
              (values-list new-pixel)))))
    new))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op [a] foldl : (f : a * Pixel -> a) (base: a) (image: Image) : a
;;; op [a] foldr : (f : Pixel * a -> a) (base: a) (image: Image) : a

(defun foldl-1-1-1 (f value image)
  (do-pixels (y x) image
    ;; pixel  returns multiple values
    ;; pixel* returns a single list of those values
    (setf value (funcall f value (pixel* image y x))))
  value)

(defun foldr-1-1-1 (f value image)
  (do-pixels (y x) image
    ;; pixel  returns multiple values
    ;; pixel* returns a single list of those values
    (setf value (funcall f (pixel* image y x) value)))
  value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op [a] foldli : (f : a * Pixel * Coordinates -> a) (base: a) (image: Image) : a
;;; op [a] foldri : (f : Pixel * a * Coordinates -> a) (base: a) (image: Image) : a

(defun foldli-1-1-1 (f value image)
  (do-pixels (y x) image
    ;; pixel  returns multiple values
    ;; pixel* returns a single list of those values
    (setf value (funcall f value (pixel* image y x) y x)))
  value)

;;; op [a] foldri : (f : Pixel * a * Coordinates -> a) (base: a) (bitMap: BitMap) : a
(defun foldri-1-1-1 (f value image)
  (do-pixels (y x) image
    ;; pixel  returns multiple values
    ;; pixel* returns a single list of those values
    (setf value (funcall f (pixel* image y x) value y x)))
  value)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun singleValued? (image)
  (let ((x (pixelType image)))
    (ecase (car x)

      (:|Bit1|   t)
      (:|Bit2|   t)
      (:|Bit4|   t)
      (:|Bit8|   t)
      (:|Bit16|  t)
      (:|Bit32|  t)

      (:|SingleFloat| t)
      (:|DoubleFloat| t)
      (:|GraySingle|  t)
      (:|GrayDouble|  t)

      (:|RGB4|      nil)
      (:|RGB8|      nil)
      (:|RGB16|     nil)
      (:|RGBSingle| nil)
      (:|RGBDouble| nil)

      (:|RGBA4|      nil)
      (:|RGBA8|      nil)
      (:|RGBA16|     nil)
      (:|RGBASingle| nil)
      (:|RGBADouble| nil)

      )))

(defun pixelType (image)
  (let ((image-type (type-of image)))
    (if (consp image-type)
        (case (first image-type)
          (simple-array 
           (let* ((elt-type   (second image-type))
                  (dimensions (third  image-type)))
             (if (and (consp elt-type)
                      (equal (first elt-type) 'unsigned-byte))
                 (let ((elt-size (second elt-type)))
                   (cond ((and (consp dimensions) 
                               (>= (length dimensions) 3))
                          (case (third dimensions)
                            (1 (case elt-size
                                 (1  '(:|Bit1|))
                                 (2  '(:|Bit2|))
                                 (4  '(:|Bit4|))
                                 (8  '(:|Bit8|))
                                 (16 '(:|Bit16|))
                                 (32 '(:|Bit32|))))
                            (3 (case elt-size
                                 (4  '(:|RGB4|))
                                 (8  '(:|RGB8|))
                                 (16 '(:|RGB16|))))
                            (4 (case elt-size
                                 (4  '(:|RGBA4|))
                                 (8  '(:|RGBA8|))
                                 (16 '(:|RGBA16|))))))
                         (t 
                          (case elt-size
                            (1  '(:|Bit1|))
                            (2  '(:|Bit2|))
                            (4  '(:|Bit4|))
                            (8  '(:|Bit8|))
                            (16 '(:|Bit16|))
                            (32 '(:|Bit32|))))))
                 nil)))
          (t nil))
        nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; op [p] readImageFile  (pixeltype : PixelKind) (filename : FileName) : Image p               
;;; op [p] writeImageFile (pixeltype : PixelKind) (filename : FileName) (image : Image p) : ()  

(defun readImageFile-1-1 (pixeltype filename)
  (let ((image (read-image-file filename)))
    (let ((pti (pixelType image)))
      (unless (equal pixeltype pti)
        (warn "~&Read an image of pixel type ~S with a routine expecting pixel type ~S~%"
              pti pixeltype)))
    image))

(defun writeImageFile-1-1-1 (pixeltype filename image)
  (let ((pti (pixelType image)))
    (unless (equal pixeltype pti)
      (warn "~&Trying to write an image of pixel type ~S with a routine for pixel type ~S~%"
            pti pixeltype)))
  (write-image-file filename image)
  ())
                 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
