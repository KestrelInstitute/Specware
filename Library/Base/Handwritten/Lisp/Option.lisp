
;;; Lisp spec

(defpackage "OPTION")
(in-package "OPTION")

;;; Definitions

;;; (defun compare-1-1 (comp x) 
;;;   (let ((pV4 (cons (car x) (cdr x)))) 
;;;     (block 
;;;      nil 
;;;      (let ((pV6 (cdr pV4))
;;;            (pV5 (car pV4))) 
;;;        (if (eq (car pV5) :|None|) 
;;;            (if (eq (car pV6) :|Some|) (return '(:|Less|))) 
;;;            (if (eq (car pV5) :|Some|) 
;;;                (if (eq (car pV6) :|Some|) 
;;;                    (return (funcall comp (cons (cdr pV5) (cdr pV6)))) 
;;;                    (if (eq (car pV6) :|None|) (return '(:|Greater|))))))) 
;;;      (return '(:|equal|)))))
;;;                             
;;; (defun compare (x1) #'(lambda (x2) (compare-1-1 x1 x2)))
                                                        
(defun left (a) (cons :|Left| a))
                                 
;;; (defun mapOption-1-1 (f opt) 
;;;   (block 
;;;    nil 
;;;    (if (eq (car opt) :|None|) 
;;;        (return '(:|None|)) 
;;;        (if (eq (car opt) :|Some|) (return (cons :|Some| (funcall f (cdr opt)))))) 
;;;    (error "Nonexhaustive match failure in Option.mapOption")))
                                                               
;;; (defun mapOption (x1) #'(lambda (x2) (mapOption-1-1 x1 x2)))
                                                            
(defparameter mkNone '(:|None|))
                                
(defun mkSome (a) (cons :|Some| a))
                                   
;;; (defun some? (a?) 
;;;   (block 
;;;    nil 
;;;    (if (eq (car a?) :|None|) (return nil) (if (eq (car a?) :|Some|) (return t))) 
;;;    (error "Nonexhaustive match failure in Option.some?")))
                                                           
;;; (defun none? (a?) (if (some? a?) nil t))
                                        
(defun right (b) (cons :|Right| b))
                                   
