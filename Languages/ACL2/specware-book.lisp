(in-package "ACL2")

(defmacro implies-macro (x y)
  (list 'if x (list 'if y 't 'nil) 't))

(mutual-recursion

 (defun implies-to-implies-macro (term)
   (if (atom term) 
       term
       (let ((fn-name (if (equal (car term) 'implies) 
                          'implies-macro 
                          (car term))))
         (cons fn-name (map-implies-to-implies-macro (cdr term))))))

 (defun map-implies-to-implies-macro (terms)
   (if (atom terms)
       nil
       (cons (implies-to-implies-macro (car terms))
             (map-implies-to-implies-macro (cdr terms))))))

(defmacro defthm-guarded (name term)
  (list 'progn
        (list 'defthm name (implies-to-implies-macro term)
              ':rule-classes 
              (list (list ':rewrite
                          ':corollary
                          term
                          ':hints
                          (list (list '"Goal" 
                                      ':in-theory 
                                      (list 'theory '(quote minimal-theory))))
                          )))
        (list 'verify-guards name)))
