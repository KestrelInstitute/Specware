(defpackage "MONADICSTATEINTERNAL")
(in-package "MONADICSTATEINTERNAL")

(defpackage "Specware-Global-Variables")

;; (defun findSymbol (name)
;;    (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
;;      (if ok
;;         (cons :|Some| symb)
;;         (cons :|None| nil)))
;; )

(defun newGlobalVar-2 (name value)
   (multiple-value-bind (symb found) (intern name "Specware-Global-Variables")
     (if (not found)
       (progn (setf (symbol-value symb) value) t)
       nil))
)
    
(defun readGlobalVar (name)
   (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
     (if ok
       (cons :|Some| (symbol-value symb))
       (cons :|None| nil)))
)

(defun writeGlobalVar-2 (name value)
   (multiple-value-bind (symb ok) (find-symbol name "Specware-Global-Variables")
     (if ok
       (progn (setf (symbol-value symb) value) t)
       nil))
)

(defun newVar (value)
   (cons :|VarRef| value)
)

; readVar written in MetaSlang.

; The test below should not be necessary because of MetaSlang typechecking.
(defun writeVar-2 (variable value)
   (if (eq (car variable) :|VarRef|)
     (progn (rplacd variable value) t)
     (error "writeVar: argument not a variable"))
)
