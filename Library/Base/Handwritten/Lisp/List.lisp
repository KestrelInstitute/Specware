
;;; Lisp spec

(defpackage "LIST-SPEC")
(in-package "LIST-SPEC")

;;; Definitions

(defun concat (s1 s2) 
  (block 
   nil 
   (if (null s1) 
       (return s2) 
       (if (consp s1) (return (cons (car s1) (concat (cdr s1) s2))))) 
   (error "Nonexhaustive match failure in List.concat")))
                                                         
(defun |!++| (s1 s2) (concat s1 s2))
                                    
(defun |!++|-1 (x) (|!++| (car x) (cdr x)))
                                           
(defun @ (s1 s2) (concat s1 s2))
                                
(defun @-1 (x) (@ (car x) (cdr x)))
                                   
(defun all-1-1 (p s) 
  (block 
   nil 
   (if (null s) 
       (return t) 
       (if (consp s) (return (if (funcall p (car s)) (all-1-1 p (cdr s)) nil)))) 
   (error "Nonexhaustive match failure in List.all")))
                                                      
(defun all (x1) #'(lambda (x2) (all-1-1 x1 x2)))
                                                
(defun app-1-1 (f s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) (return (progn (funcall f (car s)) (app-1-1 f (cdr s)))))) 
   (error "Nonexhaustive match failure in List.app")))
                                                      
(defun app (x1) #'(lambda (x2) (app-1-1 x1 x2)))
                                                
(defun compare-1-1 (comp x) 
  (let ((l2 (cdr x))
        (l1 (car x))) 
    (block 
     nil 
     (if (null l1) 
         (if (null l2) (return '(:|Equal|)) (if (consp l2) (return '(:|Less|)))) 
         (if (consp l1) 
             (if (consp l2) 
                 (return 
                  (let ((pV9 (funcall comp (cons (car l1) (car l2))))) 
                    (block 
                     nil 
                     (if (eq (car pV9) :|Equal|) 
                         (return (compare-1-1 comp (cons (cdr l1) (cdr l2))))) 
                     (return pV9)))) 
                 (if (null l2) (return '(:|Greater|)))))) 
     (error "Nonexhaustive match failure in List.compare"))))
                                                             
(defun compare (x1) #'(lambda (x2) (compare-1-1 x1 x2)))
                                                        
(defun concat-1 (x) (concat (car x) (cdr x)))
                                             
(defun |!cons| (a l) (cons a l))
                                
(defun |!cons|-1 (x) x)
                                               
(defun |!member| (a l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (return 
            (if (slang-built-in::slang-term-equals a (car l)) 
                t 
                (|!member| a (cdr l)))))) 
   (error "Nonexhaustive match failure in List.member")))
                                                         
(defun diff (s1 s2) 
  (block 
   nil 
   (if (null s1) 
       (return nil) 
       (if (consp s1) 
           (let ((pV32 (cdr s1))
                 (pV31 (car s1))) 
             (return 
              (if (|!member| pV31 s2) (diff pV32 s2) (cons pV31 (diff pV32 s2))))))) 
   (error "Nonexhaustive match failure in List.diff")))
                                                       
(defun diff-1 (x) (diff (car x) (cdr x)))
                                         
(defun |!exists|-1-1 (p s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) 
           (return (if (funcall p (car s)) t (|!exists|-1-1 p (cdr s)))))) 
   (error "Nonexhaustive match failure in List.exists")))
                                                         
(defun |!exists| (x1) #'(lambda (x2) (|!exists|-1-1 x1 x2)))
                                                            
(defun filter-1-1 (f l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (let ((pV40 (cdr l))
                 (pV39 (car l))) 
             (return 
              (if (funcall f pV39) 
                  (cons pV39 (filter-1-1 f pV40)) 
                  (filter-1-1 f pV40)))))) 
   (error "Nonexhaustive match failure in List.filter")))
                                                         
(defun filter (x1) #'(lambda (x2) (filter-1-1 x1 x2)))
                                                      
(defun |!find|-1-1 (p l) 
  (block 
   nil 
   (if (null l) 
       (return '(:|None|)) 
       (if (consp l) 
           (let ((pV43 (car l))) 
             (return 
              (if (funcall p pV43) (cons :|Some| pV43) (|!find|-1-1 p (cdr l))))))) 
   (error "Nonexhaustive match failure in List.find")))
                                                       
(defun |!find| (x1) #'(lambda (x2) (|!find|-1-1 x1 x2)))
                                                        
(defun flatten (l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) (return (concat (car l) (flatten (cdr l)))))) 
   (error "Nonexhaustive match failure in List.flatten")))
                                                          
(defun foldl-1-1-1 (f base s) 
  (block 
   nil 
   (if (null s) 
       (return base) 
       (if (consp s) 
           (return (foldl-1-1-1 f (funcall f (cons (car s) base)) (cdr s))))) 
   (error "Nonexhaustive match failure in List.foldl")))
                                                        
(defun foldl (x1) #'(lambda (x2) #'(lambda (x3) (foldl-1-1-1 x1 x2 x3))))
                                                                         
(defun foldr-1-1-1 (f base s) 
  (block 
   nil 
   (if (null s) 
       (return base) 
       (if (consp s) 
           (return (funcall f (cons (car s) (foldr-1-1-1 f base (cdr s))))))) 
   (error "Nonexhaustive match failure in List.foldr")))
                                                        
(defun foldr (x1) #'(lambda (x2) #'(lambda (x3) (foldr-1-1-1 x1 x2 x3))))
                                                                         
(defun hd (l) 
  (block 
   nil 
   (if (consp l) (return (car l))) 
   (error "Nonexhaustive match failure in List.hd")))
                                                     
(defun insert (hd tl) (cons hd tl))
                                   
(defun insert-1 (x) (insert (car x) (cdr x)))
                                             
(defun |!length| (s) 
  (block 
   nil 
   (if (null s) 
       (return 0) 
       (if (consp s) (return (NAT-SPEC::|!+| 1 (|!length| (cdr s)))))) 
   (error "Nonexhaustive match failure in List.length")))
                                                         
(defun |!map|-1-1 (f s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) (return (cons (funcall f (car s)) (|!map|-1-1 f (cdr s)))))) 
   (error "Nonexhaustive match failure in List.map")))
                                                      
(defun |!map| (x1) #'(lambda (x2) (|!map|-1-1 x1 x2)))
                                                      
(defun mapPartial-1-1 (f l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (let ((pV76 (cdr l))) 
             (return 
              (let ((pV71 (funcall f (car l)))) 
                (block 
                 nil 
                 (if (eq (car pV71) :|Some|) 
                     (return (cons (cdr pV71) (mapPartial-1-1 f pV76))) 
                     (if (eq (car pV71) :|None|) 
                         (return (mapPartial-1-1 f pV76)))) 
                 (error "Nonexhaustive match failure in List.mapPartial"))))))) 
   (error "Nonexhaustive match failure in List.mapPartial")))
                                                             
(defun mapPartial (x1) #'(lambda (x2) (mapPartial-1-1 x1 x2)))
                                                              
(defun |!member|-1 (x) (|!member| (car x) (cdr x)))
                                                   
(defparameter |!nil| nil)
                         
(defun |!nth| (ls i) 
  (block 
   nil 
   (if (consp ls) 
       (return (if ( =  i 0) (car ls) (|!nth| (cdr ls) (NAT-SPEC::|!-| i 1))))) 
   (error "Nonexhaustive match failure in List.nth")))
                                                      
(defun |!nth|-1 (x) (|!nth| (car x) (cdr x)))
                                             
(defun nthTail (ls i) 
  (block 
   nil 
   (if (null ls) 
       (return nil) 
       (if (consp ls) 
           (let ((pV88 (cdr ls))) 
             (return (if ( =  i 0) pV88 (nthTail pV88 (NAT-SPEC::|!-| i 1))))))) 
   (error "Nonexhaustive match failure in List.nthTail")))
                                                          
(defun nthTail-1 (x) (nthTail (car x) (cdr x)))
                                               
(defun |!null| (l) (block nil (if (null l) (return t)) (return nil)))
                                                                     
(defun rev2 (l r) 
  (block 
   nil 
   (if (null l) 
       (return r) 
       (if (consp l) (return (rev2 (cdr l) (cons (car l) r))))) 
   (error "Nonexhaustive match failure in List.rev2")))
                                                       
(defun rev (s) (rev2 s nil))
                            
(defun rev2-1 (x) (rev2 (car x) (cdr x)))
                                         
(defun tabulate (n f) 
  (labels 
    ((tabulateRec (m tl) 
      (if (NAT-SPEC::|!<| m 0) 
          tl 
          (tabulateRec (NAT-SPEC::|!-| m 1) (|!cons| (funcall f m) tl))))) 
    (tabulateRec (NAT-SPEC::|!-| n 1) nil)))
                                            
(defun tabulate-1 (x) (tabulate (car x) (cdr x)))
                                                 
(defun tl (l) 
  (block 
   nil 
   (if (consp l) (return (cdr l))) 
   (error "Nonexhaustive match failure in List.tl")))
                                                     
