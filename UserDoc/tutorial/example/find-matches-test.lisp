
;;; Lisp spec

(defpackage "BOOLEAN-SPEC")
(defpackage "CHAR-SPEC")
(defpackage "COMPARE")
(defpackage "FUNCTIONS")
(defpackage "INTEGER-SPEC")
(defpackage "LIST-SPEC")
(defpackage "NAT-SPEC")
(defpackage "OPTION")
(defpackage "STRING-SPEC")
(defpackage "SYSTEM-SPEC")
(defpackage "SW-USER")
(in-package "SW-USER")

;;; Definitions

(defun LIST-SPEC::foldl-1-1-1 (f base s) 
  (block 
   nil 
   (if (null s) 
       (return base) 
       (if (consp s) 
           (return 
            (LIST-SPEC::foldl-1-1-1 f (funcall f (cons (car s) base)) (cdr s))))) 
   (error "Nonexhaustive match failure in foldl")))
                                                   
(defun INTEGER-SPEC::|!>| (x y) (INTEGER-SPEC::|!<| y x))
                                                         
(defun LIST-SPEC::|!length| (s) 
  (block 
   nil 
   (if (null s) 
       (return 0) 
       (if (consp s) 
           (return (INTEGER-SPEC::|!+| 1 (LIST-SPEC::|!length| (cdr s)))))) 
   (error "Nonexhaustive match failure in length")))
                                                    
(defun LIST-SPEC::nthTail (ls i) 
  (block 
   nil 
   (if (null ls) 
       (return nil) 
       (if (consp ls) 
           (let ((pV103 (cdr ls))) 
             (return 
              (if ( =  i 0) 
                  pV103 
                  (LIST-SPEC::nthTail pV103 (INTEGER-SPEC::|!-| i 1))))))) 
   (error "Nonexhaustive match failure in nthTail")))
                                                     
(defun symb_matches? (s os) 
  (block 
   nil 
   (if (eq (car os) :|Some|) 
       (return (eq s (cdr os))) 
       (if (eq (car os) :|None|) (return t))) 
   (error "Nonexhaustive match failure in symb_matches?")))
                                                           
(defun word_matches_aux? (wrd msg) 
  (block 
   nil 
   (if (null wrd) 
       (return t) 
       (if (consp wrd) 
           (return 
            (block 
             nil 
             (if (consp msg) 
                 (return 
                  (if (symb_matches? (car wrd) (car msg)) 
                      (word_matches_aux? (cdr wrd) (cdr msg)) 
                      nil))) 
             (error "Nonexhaustive match failure in word_matches_aux?"))))) 
   (error "Nonexhaustive match failure in word_matches_aux?")))
                                                               
(defun word_matches_at? (wrd msg pos) 
  (if (INTEGER-SPEC::|!>| 
       (INTEGER-SPEC::|!+| pos (LIST-SPEC::|!length| wrd)) 
       (LIST-SPEC::|!length| msg)) 
      nil 
      (word_matches_aux? 
       wrd 
       (if ( =  pos 0) msg (LIST-SPEC::nthTail msg (INTEGER-SPEC::|!-| pos 1))))))


(defun find_matches_aux (msg wrd pos) 
  (if (INTEGER-SPEC::|!>| 
       (INTEGER-SPEC::|!+| pos (LIST-SPEC::|!length| wrd)) 
       (LIST-SPEC::|!length| msg)) 
      '(:|None|) 
      (if (word_matches_at? wrd msg pos) 
          (cons :|Some| pos) 
          (find_matches_aux msg wrd (INTEGER-SPEC::|!+| pos 1)))))
                                                                  
(defun find_matches (msg wrds) 
  (LIST-SPEC::foldl-1-1-1 
   #'(lambda (x) 
      (let ((mtchs (cdr x))
            (wrd (car x))) 
        (let ((pV1 (find_matches_aux msg wrd 0))) 
          (block 
           nil 
           (if (eq (car pV1) :|Some|) 
               (return (cons (cons (cdr pV1) wrd) mtchs)) 
               (if (eq (car pV1) :|None|) (return mtchs))) 
           (error "Nonexhaustive match failure in find_matches"))))) 
   nil 
   wrds))
         
(defun find_matches-1 (x) (find_matches (car x) (cdr x)))
                                                         
(defun find_matches_aux-1 (x) 
  (find_matches_aux (svref x 0) (svref x 1) (svref x 2)))
                                                         
(defun word2string (wrd) (STRING-SPEC::implode wrd))
                                                    
(defun match2string-1 (mtch) (cons (car mtch) (word2string (cdr mtch))))
                                                                        
(defun match2string (x0 x1) (match2string-1 (cons x0 x1)))
                                                          
(defun LIST-SPEC::|!map|-1-1 (f s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) 
           (return (cons (funcall f (car s)) (LIST-SPEC::|!map|-1-1 f (cdr s)))))) 
   (error "Nonexhaustive match failure in map")))
                                                 
(defun message2string (msg) 
  (STRING-SPEC::implode 
   (LIST-SPEC::|!map|-1-1 
    #'(lambda (msym) 
       (block 
        nil 
        (if (eq (car msym) :|Some|) 
            (return (cdr msym)) 
            (if (eq (car msym) :|None|) (return #\*))) 
        (error "Nonexhaustive match failure in message2string"))) 
    msg)))
          
(defun msg_char? (ch) (lisp::or (CHAR-SPEC::isUpperCase ch) (eq ch #\*)))
                                                                         
(defun string2message (mstr) 
  (LIST-SPEC::|!map|-1-1 
   #'(lambda (ch) (if (eq ch #\*) '(:|None|) (cons :|Some| ch))) 
   (STRING-SPEC::explode mstr)))
                                
(defun string2word (wstr) (STRING-SPEC::explode wstr))
                                                      
(defun symb_matches?-1 (x) (symb_matches? (car x) (cdr x)))
                                                           
(defun test_find_matches (mstr wstrs) 
  (LIST-SPEC::|!map|-1-1 
   #'match2string-1 
   (find_matches 
    (string2message mstr) 
    (LIST-SPEC::|!map|-1-1 #'string2word wstrs))))
                                                  
(defun test_find_matches-1 (x) (test_find_matches (car x) (cdr x)))
                                                                   
(defun word_char? (ch) (CHAR-SPEC::isUpperCase ch))
                                                   
(defun word_matches_at?-1 (x) 
  (word_matches_at? (svref x 0) (svref x 1) (svref x 2)))
                                                         
(defun word_matches_aux?-1 (x) (word_matches_aux? (car x) (cdr x)))
                                                                   
(defun BOOLEAN-SPEC::& (x y) (if x y nil))
                                          
(defun BOOLEAN-SPEC::&-1 (x) (BOOLEAN-SPEC::& (car x) (cdr x)))
                                                               
(defun BOOLEAN-SPEC::~ (x) (if x nil t))
                                        
(defun BOOLEAN-SPEC::<=> (x y) (if x y (BOOLEAN-SPEC::~ y)))
                                                            
(defun BOOLEAN-SPEC::<=>-1 (x) (BOOLEAN-SPEC::<=> (car x) (cdr x)))
                                                                   
(defun BOOLEAN-SPEC::=> (x y) (if x y t))
                                         
(defun BOOLEAN-SPEC::=>-1 (x) (BOOLEAN-SPEC::=> (car x) (cdr x)))
                                                                 
(defun BOOLEAN-SPEC::|!or| (x y) (if x t y))
                                            
(defun BOOLEAN-SPEC::|!or|-1 (x) (BOOLEAN-SPEC::|!or| (car x) (cdr x)))
                                                                       
(defun BOOLEAN-SPEC::show (b) (BOOLEAN-SPEC::toString b))
                                                         
(defun CHAR-SPEC::show (c) (CHAR-SPEC::toString c))
                                                   
(defun COMPARE::show (cmp) 
  (block 
   nil 
   (if (eq (car cmp) :|Greater|) 
       (return "Greater") 
       (if (eq (car cmp) :|Equal|) 
           (return "Equal") 
           (if (eq (car cmp) :|Less|) (return "Less")))) 
   (error "Nonexhaustive match failure in show")))
                                                  
(defun INTEGER-SPEC::|!>|-1 (x) (INTEGER-SPEC::|!>| (car x) (cdr x)))
                                                                     
(defun INTEGER-SPEC::|!>=| (x y) (INTEGER-SPEC::|!<=| y x))
                                                           
(defun INTEGER-SPEC::|!>=|-1 (x) (INTEGER-SPEC::|!>=| (car x) (cdr x)))
                                                                       
(defun INTEGER-SPEC::compare (n m) 
  (if (INTEGER-SPEC::|!<| n m) 
      '(:|Less|) 
      (if ( =  n m) '(:|Equal|) '(:|Greater|))))
                                                
(defun INTEGER-SPEC::compare-1 (x) (INTEGER-SPEC::compare (car x) (cdr x)))
                                                                           
(defun INTEGER-SPEC::|!max| (x y) (if (INTEGER-SPEC::|!<=| x y) y x))
                                                                     
(defun INTEGER-SPEC::|!max|-1 (x) (INTEGER-SPEC::|!max| (car x) (cdr x)))
                                                                         
(defun INTEGER-SPEC::|!min| (x y) (if (INTEGER-SPEC::|!<=| x y) x y))
                                                                     
(defun INTEGER-SPEC::|!min|-1 (x) (INTEGER-SPEC::|!min| (car x) (cdr x)))
                                                                         
(defun INTEGER-SPEC::show (n) (INTEGER-SPEC::toString n))
                                                         
(defun LIST-SPEC::concat (s1 s2) 
  (block 
   nil 
   (if (null s1) 
       (return s2) 
       (if (consp s1) (return (cons (car s1) (LIST-SPEC::concat (cdr s1) s2))))) 
   (error "Nonexhaustive match failure in concat")))
                                                    
(defun LIST-SPEC::|!++| (s1 s2) (LIST-SPEC::concat s1 s2))
                                                          
(defun LIST-SPEC::|!++|-1 (x) (LIST-SPEC::|!++| (car x) (cdr x)))
                                                                 
(defun LIST-SPEC::@ (s1 s2) (LIST-SPEC::concat s1 s2))
                                                      
(defun LIST-SPEC::@-1 (x) (LIST-SPEC::@ (car x) (cdr x)))
                                                         
(defun LIST-SPEC::all-1-1 (p s) 
  (block 
   nil 
   (if (null s) 
       (return t) 
       (if (consp s) 
           (return (if (funcall p (car s)) (LIST-SPEC::all-1-1 p (cdr s)) nil)))) 
   (error "Nonexhaustive match failure in all")))
                                                 
(defun LIST-SPEC::all (x1) #'(lambda (x2) (LIST-SPEC::all-1-1 x1 x2)))
                                                                      
(defun LIST-SPEC::app-1-1 (f s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) 
           (return (progn (funcall f (car s)) (LIST-SPEC::app-1-1 f (cdr s)))))) 
   (error "Nonexhaustive match failure in app")))
                                                 
(defun LIST-SPEC::app (x1) #'(lambda (x2) (LIST-SPEC::app-1-1 x1 x2)))
                                                                      
(defun LIST-SPEC::compare-1-1 (comp x) 
  (let ((l2 (cdr x))
        (l1 (car x))) 
    (block 
     nil 
     (if (null l1) 
         (if (null l2) (return '(:|Equal|)) (if (consp l2) (return '(:|Less|)))) 
         (if (consp l1) 
             (if (consp l2) 
                 (return 
                  (let ((pV24 (funcall comp (cons (car l1) (car l2))))) 
                    (block 
                     nil 
                     (if (eq (car pV24) :|Equal|) 
                         (return 
                          (LIST-SPEC::compare-1-1 comp (cons (cdr l1) (cdr l2))))) 
                     (return pV24)))) 
                 (if (null l2) (return '(:|Greater|)))))) 
     (error "Nonexhaustive match failure in compare"))))
                                                        
(defun LIST-SPEC::compare (x1) 
  #'(lambda (x2) (LIST-SPEC::compare-1-1 x1 x2)))
                                                 
(defun LIST-SPEC::concat-1 (x) (LIST-SPEC::concat (car x) (cdr x)))
                                                                   
(defun LIST-SPEC::|!cons| (a l) (cons a l))
                                           
(defun LIST-SPEC::|!cons|-1 (x) (LIST-SPEC::|!cons| (car x) (cdr x)))
                                                                     
(defun LIST-SPEC::|!member| (a l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (return 
            (if (slang-built-in::slang-term-equals a (car l)) 
                t 
                (LIST-SPEC::|!member| a (cdr l)))))) 
   (error "Nonexhaustive match failure in member")))
                                                    
(defun LIST-SPEC::diff (s1 s2) 
  (block 
   nil 
   (if (null s1) 
       (return nil) 
       (if (consp s1) 
           (let ((pV47 (cdr s1))
                 (pV46 (car s1))) 
             (return 
              (if (LIST-SPEC::|!member| pV46 s2) 
                  (LIST-SPEC::diff pV47 s2) 
                  (cons pV46 (LIST-SPEC::diff pV47 s2))))))) 
   (error "Nonexhaustive match failure in diff")))
                                                  
(defun LIST-SPEC::diff-1 (x) (LIST-SPEC::diff (car x) (cdr x)))
                                                               
(defun LIST-SPEC::|!exists|-1-1 (p s) 
  (block 
   nil 
   (if (null s) 
       (return nil) 
       (if (consp s) 
           (return 
            (if (funcall p (car s)) t (LIST-SPEC::|!exists|-1-1 p (cdr s)))))) 
   (error "Nonexhaustive match failure in exists")))
                                                    
(defun LIST-SPEC::|!exists| (x1) 
  #'(lambda (x2) (LIST-SPEC::|!exists|-1-1 x1 x2)))
                                                   
(defun LIST-SPEC::filter-1-1 (f l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (let ((pV55 (cdr l))
                 (pV54 (car l))) 
             (return 
              (if (funcall f pV54) 
                  (cons pV54 (LIST-SPEC::filter-1-1 f pV55)) 
                  (LIST-SPEC::filter-1-1 f pV55)))))) 
   (error "Nonexhaustive match failure in filter")))
                                                    
(defun LIST-SPEC::filter (x1) #'(lambda (x2) (LIST-SPEC::filter-1-1 x1 x2)))
                                                                            
(defun LIST-SPEC::|!find|-1-1 (p l) 
  (block 
   nil 
   (if (null l) 
       (return '(:|None|)) 
       (if (consp l) 
           (let ((pV58 (car l))) 
             (return 
              (if (funcall p pV58) 
                  (cons :|Some| pV58) 
                  (LIST-SPEC::|!find|-1-1 p (cdr l))))))) 
   (error "Nonexhaustive match failure in find")))
                                                  
(defun LIST-SPEC::|!find| (x1) 
  #'(lambda (x2) (LIST-SPEC::|!find|-1-1 x1 x2)))
                                                 
(defun LIST-SPEC::flatten (l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (return (LIST-SPEC::concat (car l) (LIST-SPEC::flatten (cdr l)))))) 
   (error "Nonexhaustive match failure in flatten")))
                                                     
(defun LIST-SPEC::foldl (x1) 
  #'(lambda (x2) #'(lambda (x3) (LIST-SPEC::foldl-1-1-1 x1 x2 x3))))
                                                                    
(defun LIST-SPEC::foldr-1-1-1 (f base s) 
  (block 
   nil 
   (if (null s) 
       (return base) 
       (if (consp s) 
           (return 
            (funcall f (cons (car s) (LIST-SPEC::foldr-1-1-1 f base (cdr s))))))) 
   (error "Nonexhaustive match failure in foldr")))
                                                   
(defun LIST-SPEC::foldr (x1) 
  #'(lambda (x2) #'(lambda (x3) (LIST-SPEC::foldr-1-1-1 x1 x2 x3))))
                                                                    
(defun LIST-SPEC::hd (l) 
  (block 
   nil 
   (if (consp l) (return (car l))) 
   (error "Nonexhaustive match failure in hd")))
                                                
(defun LIST-SPEC::insert (hd tl) (cons hd tl))
                                              
(defun LIST-SPEC::insert-1 (x) (LIST-SPEC::insert (car x) (cdr x)))
                                                                   
(defun LIST-SPEC::|!map| (x1) #'(lambda (x2) (LIST-SPEC::|!map|-1-1 x1 x2)))
                                                                            
(defun LIST-SPEC::mapPartial-1-1 (f l) 
  (block 
   nil 
   (if (null l) 
       (return nil) 
       (if (consp l) 
           (let ((pV91 (cdr l))) 
             (return 
              (let ((pV86 (funcall f (car l)))) 
                (block 
                 nil 
                 (if (eq (car pV86) :|Some|) 
                     (return 
                      (cons (cdr pV86) (LIST-SPEC::mapPartial-1-1 f pV91))) 
                     (if (eq (car pV86) :|None|) 
                         (return (LIST-SPEC::mapPartial-1-1 f pV91)))) 
                 (error "Nonexhaustive match failure in mapPartial"))))))) 
   (error "Nonexhaustive match failure in mapPartial")))
                                                        
(defun LIST-SPEC::mapPartial (x1) 
  #'(lambda (x2) (LIST-SPEC::mapPartial-1-1 x1 x2)))
                                                    
(defun LIST-SPEC::|!member|-1 (x) (LIST-SPEC::|!member| (car x) (cdr x)))
                                                                         
(defparameter LIST-SPEC::|!nil| nil)
                                    
(defun LIST-SPEC::|!nth| (ls i) 
  (block 
   nil 
   (if (consp ls) 
       (return 
        (if ( =  i 0) 
            (car ls) 
            (LIST-SPEC::|!nth| (cdr ls) (INTEGER-SPEC::|!-| i 1))))) 
   (error "Nonexhaustive match failure in nth")))
                                                 
(defun LIST-SPEC::|!nth|-1 (x) (LIST-SPEC::|!nth| (car x) (cdr x)))
                                                                   
(defun LIST-SPEC::nthTail-1 (x) (LIST-SPEC::nthTail (car x) (cdr x)))
                                                                     
(defun LIST-SPEC::|!null| (l) (block nil (if (null l) (return t)) (return nil)))
                                                                                
(defun LIST-SPEC::rev2 (l r) 
  (block 
   nil 
   (if (null l) 
       (return r) 
       (if (consp l) (return (LIST-SPEC::rev2 (cdr l) (cons (car l) r))))) 
   (error "Nonexhaustive match failure in rev2")))
                                                  
(defun LIST-SPEC::rev (s) (LIST-SPEC::rev2 s nil))
                                                  
(defun LIST-SPEC::rev2-1 (x) (LIST-SPEC::rev2 (car x) (cdr x)))
                                                               
(defun LIST-SPEC::show-1-1-1 (sep showElem l) 
  (block 
   nil 
   (if (null l) 
       (return "") 
       (if (consp l) 
           (let ((pV113 (cdr l))
                 (pV112 (car l))) 
             (progn (if (null pV113) (return (funcall showElem pV112))) 
                    (return 
                     (STRING-SPEC::^ 
                      (STRING-SPEC::^ (funcall showElem pV112) sep) 
                      (LIST-SPEC::show-1-1-1 sep showElem pV113))))))) 
   (error "Nonexhaustive match failure in show")))
                                                  
(defun LIST-SPEC::show (x1) 
  #'(lambda (x2) #'(lambda (x3) (LIST-SPEC::show-1-1-1 x1 x2 x3))))
                                                                   
(defun LIST-SPEC::tabulate (n f) 
  (labels 
    ((tabulateRec (m tl) 
      (if (INTEGER-SPEC::|!<| m 0) 
          tl 
          (tabulateRec 
           (INTEGER-SPEC::|!-| m 1) 
           (LIST-SPEC::|!cons| (funcall f m) tl))))) 
    (tabulateRec (INTEGER-SPEC::|!-| n 1) nil)))
                                                
(defun LIST-SPEC::tabulate-1 (x) (LIST-SPEC::tabulate (car x) (cdr x)))
                                                                       
(defun LIST-SPEC::tl (l) 
  (block 
   nil 
   (if (consp l) (return (cdr l))) 
   (error "Nonexhaustive match failure in tl")))
                                                
(defun NAT-SPEC::div (n m) 
  (if (INTEGER-SPEC::|!<| n m) 
      0 
      (INTEGER-SPEC::|!+| 1 (NAT-SPEC::div (INTEGER-SPEC::|!-| n m) m))))
                                                                         
(defun NAT-SPEC::div-1 (x) (NAT-SPEC::div (car x) (cdr x)))
                                                           
(defparameter NAT-SPEC::one 1)
                              
(defun NAT-SPEC::posNat? (n) (INTEGER-SPEC::|!>| n 0))
                                                      
(defun NAT-SPEC::pred (n) (INTEGER-SPEC::|!-| n 1))
                                                   
(defun NAT-SPEC::show (n) (NAT-SPEC::natToString n))
                                                    
(defun NAT-SPEC::succ (n) (INTEGER-SPEC::|!+| n 1))
                                                   
(defparameter NAT-SPEC::two 2)
                              
(defparameter NAT-SPEC::zero 0)
                               
(defun OPTION::compare-1-1 (comp x) 
  (let ((pV122 (cons (car x) (cdr x)))) 
    (block 
     nil 
     (let ((pV124 (cdr pV122))
           (pV123 (car pV122))) 
       (if (eq (car pV123) :|None|) 
           (if (eq (car pV124) :|Some|) (return '(:|Less|))) 
           (if (eq (car pV123) :|Some|) 
               (if (eq (car pV124) :|Some|) 
                   (return (funcall comp (cons (cdr pV123) (cdr pV124)))) 
                   (if (eq (car pV124) :|None|) (return '(:|Greater|))))))) 
     (return '(:|Equal|)))))
                            
(defun OPTION::compare (x1) #'(lambda (x2) (OPTION::compare-1-1 x1 x2)))
                                                                        
(defun OPTION::mapOption-1-1 (f opt) 
  (block 
   nil 
   (if (eq (car opt) :|None|) 
       (return '(:|None|)) 
       (if (eq (car opt) :|Some|) (return (cons :|Some| (funcall f (cdr opt)))))) 
   (error "Nonexhaustive match failure in mapOption")))
                                                       
(defun OPTION::mapOption (x1) #'(lambda (x2) (OPTION::mapOption-1-1 x1 x2)))
                                                                            
(defun OPTION::some? (x) 
  (block 
   nil 
   (if (eq (car x) :|None|) (return nil) (if (eq (car x) :|Some|) (return t))) 
   (error "Nonexhaustive match failure in some?")))
                                                   
(defun OPTION::none? (x) (if (OPTION::some? x) nil t))
                                                      
(defun OPTION::show-1-1 (showX opt) 
  (block 
   nil 
   (if (eq (car opt) :|None|) 
       (return "None") 
       (if (eq (car opt) :|Some|) 
           (return 
            (STRING-SPEC::^ 
             (STRING-SPEC::^ "(Some " (funcall showX (cdr opt))) 
             ")")))) 
   (error "Nonexhaustive match failure in show")))
                                                  
(defun OPTION::show (x1) #'(lambda (x2) (OPTION::show-1-1 x1 x2)))
                                                                  
(defun STRING-SPEC::compare (n m) 
  (if (STRING-SPEC::lt n m) 
      '(:|Less|) 
      (if (string=  n m) '(:|Equal|) '(:|Greater|))))
                                                     
(defun STRING-SPEC::compare-1 (x) (STRING-SPEC::compare (car x) (cdr x)))
                                                                         