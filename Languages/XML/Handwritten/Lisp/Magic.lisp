(defpackage "MAGIC")
(in-package "MAGIC")

;;;   %% This creates a heterogenous list from the fields of a product
;;;   %% Such a beast is not even well formed for metaslang, so it must
;;;   %% be handled carefully!
;;;
;;;   op Magic.magicElements      : fa (X,Y) X -> List Y
;;;
;;;   %% This extracts the name of the constructor from the runtime datum
;;;   %% The value (Y) is actually a reasonable metaslang construction,
;;;   %% but we don't know it's type.
;;;
;;;   op Magic.magicConstructorNameAndValue : fa (X,Y) X -> String * Y
;;;
;;;   %% These are just identities that type cast their args, so that the result
;;;   %% is pleasing to Specware for further processing.
;;;
;;;   op Magic.magicCastToString        : fa (X) X -> String
;;;
;;;   op Magic.magicCastToInteger       : fa (X) X -> Integer
;;;
;;;   op Magic.magicCastToList          : fa (X,Y) X -> List Y
;;;
;;;   op Magic.magicCastToChar          : fa (X) X -> Char
;;;
;;;   op Magic.magicCastToBoolean       : fa (X) X -> Boolean

;;; Product

(defun magicElements (size-and-data)
  (let ((product-size (car size-and-data))
	(product-data (cdr size-and-data)))
    (case product-size
      (0  nil)
      (1  (list product-data))
      (2  (list (car product-data) (cdr product-data)))
      (t  (coerce product-data 'list)))))

(defun magicElements-2 (product-size product-data)
  (case product-size
    (0  nil)
    (1  (list product-data))
    (2  (list (car product-data) (cdr product-data)))
    (t  (coerce product-data 'list))))

(defun magicMakeProduct (x)
  (cond ((null x)
	 (coerce nil 'vector))
	((null (cdr x))
	 (car x))
	((null (cddr x))
	 (cons (car x) (cadr x)))
	(t
	 (coerce x 'vector))))

;;; CoProduct

(defun magicConstructorNameAndValue (coproduct)
  (cons ; we give metaslang two values by consing them
   (symbol-name (car coproduct))  ; string
   (cdr coproduct)))              ; Y

(defun magicMakeConstructor-2 (name value)
  (cons (intern name "KEYWORD") value))

;;; Misc Casts

(defun magicCastToBoolean (x) x)
(defun magicCastToInteger (x) x)
(defun magicCastToString  (x) x)
(defun magicCastToChar    (x) x)
(defun magicCastToList    (x) x)
(defun magicCastToOption  (x) x)

(defun magicCastFromBoolean (x) x)
(defun magicCastFromInteger (x) x)
(defun magicCastFromString  (x) x)
(defun magicCastFromChar    (x) x)
(defun magicCastFromList    (x) x)
(defun magicCastFromOption  (x) x)
(defun magicCastFromAE-2    (x y) (cons x y))

