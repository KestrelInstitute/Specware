(defpackage :MonadicStateInternal)
(in-package :MonadicStateInternal)

(defpackage :Specware-Global-Variables)

;; (defun findSymbol (name)
;;    (multiple-value-bind (symb ok) (find-symbol name :Specware-Global-Variables)
;;      (if ok
;;         (cons :|Some| symb)
;;         (cons :|None| nil)))
;; )

(defun newGlobalVar-2 (name value)
   (multiple-value-bind (symb found) (intern name :Specware-Global-Variables)
     (if (not found)
       (progn (setf (symbol-value symb) value) t)
       nil))
)
    
(defun readGlobalVar (name)
   (multiple-value-bind (symb ok) (find-symbol name :Specware-Global-Variables)
     (if ok
       (cons :|Some| (symbol-value symb))
       (cons :|None| nil)))
)

(defun writeGlobalVar-2 (name value)
   (multiple-value-bind (symb ok) (find-symbol name :Specware-Global-Variables)
     (if ok
       (progn (setf (symbol-value symb) value) t)
       nil))
)

(defun newVar (value) ; why does metaslang codegen think it should mangle this name?
   (cons :|VarRef| value)
)

; readVar written in MetaSlang.

; The test below should not be necessary because of MetaSlang typechecking.
(defun writeVar-2 (variable value)
   (if (eq (car variable) :|VarRef|)
     (progn (rplacd variable value) t)
     (error "writeVar: argument not a variable"))
)

(defpackage :SpecCalc)

;;; This doesn't belong here but don't want to create its own file yet
(define-compiler-macro SpecCalc::when-1-1-1 (p command yyy-2)
  ;; Make strict!
 `(let ((yyy-2 ,yyy-2))
    (if ,p (funcall ,command yyy-2) (SpecCalc::return-1-1 nil yyy-2))))