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

(defun magicElements (product)
  (etypecase product
    (null   nil)
    (cons   (list (car product) (cdr product)))
    (vector (coerce product 'list))))

(defun magicMakeProduct (x)
  (if (equal (length x) 2)
      (cons (car x) (cdr x))
    (coerce x 'vector)))

;;; CoProduct

(defun magicConstructorNameAndValue (coproduct)
  (cons ; we give metaslang two values by consing them
   (symbol-name (car coproduct))  ; string
   (cdr coproduct)))              ; Y

(defun magicMakeConstructor-2 (name value)
  (cons (intern name "KEYWORD") value))

;;; Misc Casts

(defun magicCastToString  (x) x)
(defun magicCastToInteger (x) x)
(defun magicCastToList    (x) x)
(defun magicCastToChar    (x) x)
(defun magicCastToBoolean (x) x)

(defun magicCastFromString  (x) x)
(defun magicCastFromInteger (x) x)
(defun magicCastFromList    (x) x)
(defun magicCastFromChar    (x) x)
(defun magicCastFromBoolean (x) x)

