;; This file defines general utilities that are necessary to 
;; connect EXTENDED-SLANG specs with lisp code.
;; The functions here are referenced in code produced by 
;;  Specware4/Languages/MetaSlang/CodeGen/Lisp/SpecToLisp.sw

(defpackage :Specware)
(defpackage :SpecCalc)
(defpackage :List-Spec)
(defpackage :Slang-Built-In)
(defpackage :Assert-Spec)
(in-package :Slang-Built-In)

;; defvar specwareWizard? here (as opposed to def in Monad.sw) 
;; to avoid having CMUCL treat it as a constant, in which case
;; code under the false branch would be optimized away!
(defvar SpecCalc::specwareWizard? nil) ; see Specware4/Languages/SpecCalculus/Semantics/Monad.sw

(defparameter quotient-tag
  (list :|Quotient|))

(defun quotient (r)
  #'(lambda(x)  (vector quotient-tag r x)))

(defun quotient-1-1 (r x)
  (vector quotient-tag r x))

(defun quotient? (x)
  (and (vectorp x)
       (eq (svref x 0) quotient-tag)))

(defun quotient-relation (x)
  (svref x 1))

(defun quotient-element (x)
  (if (quotient? x)
      (svref x 2)
    (error "Expected an equivalence class, but got (presumably) a representative: ~S" x)))

(define-compiler-macro quotient-element (x)
  `(svref ,x 2))

(defun choose ()
  #'(lambda (f) #'(lambda(x) (funcall f (quotient-element x)))))

(defun choose-1 (f)
  #'(lambda(x) (funcall f (quotient-element x))))

(defun choose-1-1 (f x) 
  (funcall f (quotient-element x)))

(define-compiler-macro choose-1-1 (f x)
  `(funcall ,f (quotient-element ,x)))

#|
  
  slang-term-equals
  -----------------
     This function determines equality for lisp expressions that
     are generated from EXT-SLANG terms admitting equality.


     A translated ext-slang term admitting equality can be in one of the
     following forms:

  (vector t1 t2 ... tn)   - a product
  (cons t1 t2)            - a two tuple
  (cons t1 t2) , nil      - an element of a list sort
  (list 'Quotient 'fn t)  - an element of a quotient sort
  (cons 'Name t)          - an embedding
  atom                    - a string, char, or nat constant.

|#

;;;  (defun slang-term-equals (t1 t2)
;;;     (or 
;;;      (eq t1 t2)
;;;      (cond
;;;        ((null t1) (null t2))
;;;        ((stringp t1) (string= t1 t2))
;;;        ((symbolp t1) (eql t1 t2))
;;;        ((numberp t1) (eq t1 t2))
;;;        ((characterp t1) (eql t1 t2))
;;;  #| 
;;;     Determine equality by calling the quotient 
;;;     operator in the second position 
;;;     |#
;;;        ((and (quotient? t1)
;;;  	    (quotient? t2))
;;;         (funcall 
;;;  	(quotient-relation t1)
;;;  	(quotient-element t1) 
;;;  	(quotient-element t2)))
;;;       
;;;  #|
;;;     Cons cells are equal if their elements are equal too.
;;;  |#
;;;        ((consp t1) 	 
;;;             (and 
;;;  	    (consp t2) 
;;;  	    (slang-term-equals (car t1) (car t2))
;;;  	    (slang-term-equals (cdr t1) (cdr t2))))
;;;  #|
;;;     Two vectors (corresponding to tuple types)
;;;     are equal if all their elements are equal.
;;;  |#
;;;        ((vectorp t1)
;;;             (and 
;;;  	    (vectorp t2)
;;;  	    (let ((dim (array-dimension t1 0)))
;;;  	      (do ((i 0 (+ i 1))
;;;  		   (v-equal t (slang-term-equals (svref t1 i)  (svref t2 i))))
;;;  		  ((or (= i dim) (not v-equal)) v-equal)))))
;;;        (t (progn (format t "Ill formed terms~%") nil))
;;;        )
;;;      )
;;;     )

(defvar *warn-about-questionable-equality?* nil)

;;; This is twice as fast as the version above...
(defun slang-term-equals-2 (t1 t2)
  #+sbcl(declare (optimize speed))
  (or (eq t1 t2)
      (typecase t1
        (array (typecase t1
                 (string    (string= t1 t2))
                 (vector    (cond ((and   
                           ;; (quotient? t1) 
                           ;; (quotient? t2)
                           (eq (svref t1 0) quotient-tag)
                           (vectorp t2)
                           (eq (svref t2 0) quotient-tag)
                           )
                          ;; Determine equality by calling the quotient 
                          ;; operator in the second position 
                          (funcall (svref t1 1) ; (quotient-relation t1)
                                   (cons (svref t1 2) ; (quotient-element t1) 
                                         (svref t2 2) ; (quotient-element t2)
                                         )))
                         (t
                          (and
                           ;; Two vectors (corresponding to tuple types)
                           ;; are equal if all their elements are equal.
                           (vectorp t2)
                           (let ((dim1 (array-dimension t1 0))
                                 (dim2 (array-dimension t2 0)))
                             (and (eql dim1 dim2)
                                  (do ((i 0 (+ i 1))
                                       (v-equal t (slang-term-equals-2 (svref t1 i)  (svref t2 i))))
                                      ((or (= i dim1) (not v-equal)) v-equal)
                                    (declare (fixnum i)))))))))
                 (t (equalp t1 t2))
                 ))
        ;(null      (null    t2))
        ;(string    (string= t1 t2))
        (symbol    (eq      t1 t2))
        (cons      (and (consp t2) 
                        ;;   Cons cells are equal if their elements are equal too.
                        (slang-term-equals-2 (car t1) (car t2))
                        (slang-term-equals-2 (cdr t1) (cdr t2))))
        (number    (=       t1 t2))    ; catches complex numbers, etc.
        (character (eq      t1 t2))
        (hash-table
         ;; This can happen, for example, when comparing specs, which use maps from
         ;; /Library/Structures/Data/Maps/SimpleAsSTHarray.sw that are implemented
         ;; with hash tables in the associated Handwritten/Lisp/MapAsSTHarray.lisp
         ;; Expensive pair of sub-map tests, but should be used rarely:
         (and (eql (hash-table-count t1) (hash-table-count t2))
              (block comparison-of-entries
                ;; fail if t1 disagrees with t2 for something in the domain of t1
                (maphash #'(lambda (k v) 
                             (unless (slang-term-equals-2 v (gethash k t2))
                               (return-from comparison-of-entries nil)))
                         t1)
;; This is unnecessary if sizes are the same
;                ;; fail if t2 disagrees with t1 for something in the domain of t2
;                (maphash #'(lambda (k v) 
;                             (unless (slang-term-equals-2 v (gethash k t1))
;                               (return-from comparison-of-entries nil)))
;                         t2)
                ;; the maps are functionally equivalent
                t)))
        (pathname
         ;; As long as we might have hash-tables, maybe pathnames?
         (equal t1 t2))
        (t 
         ;; structures, etc. will end up here
         ;; print semi-informative error message, but avoid printing
         ;; what could be enormous structures...
         (progn 
           (when *warn-about-questionable-equality?*
             (warn "In slang-term-equals, ill formed terms of types ~S and ~S are ~A~%" 
                   (type-of t1)
                   (type-of t2)
                   (if (equal t1 t2) "LISP:EQUAL" "not LISP:EQUAL")))
           ;; would it be better to just fail?
           (equal t1 t2))))))

(defun slang-term-equals (x) (slang-term-equals-2 (car x) (cdr x)))

(defun sw-equal? (x y) (slang-term-equals-2 x y))

(defun slang-term-not-equals-2 (x y) 
  (not (slang-term-equals-2 x y)))

;;; swxhash: Hash function for slang-term-equals (based on sbcl psxhash for equalp)
(eval-when (compile load)
  (defconstant +max-hash-depthoid+ 5))
(declaim (inline mix Specware::swxhash))
(defun mix (x y)
  ;; FIXME: We wouldn't need the nasty (SAFETY 0) here if the compiler
  ;; were smarter about optimizing ASH. (Without the THE FIXNUM below,
  ;; and the (SAFETY 0) declaration here to get the compiler to trust
  ;; it, the sbcl-0.5.0m cross-compiler running under Debian
  ;; cmucl-2.4.17 turns the ASH into a full call, requiring the
  ;; UNSIGNED-BYTE 32 argument to be coerced to a bignum, requiring
  ;; consing, and thus generally obliterating performance.)
  #+sbcl(declare (optimize (speed 3) (safety 0)))
  (declare (type (and fixnum unsigned-byte) x y))
  ;; the ideas here:
  ;;   * Bits diffuse in both directions (shifted left by up to 2 places
  ;;     in the calculation of XY, and shifted right by up to 5 places
  ;;     by the ASH).
  ;;   * The #'+ and #'LOGXOR operations don't commute with each other,
  ;;     so different bit patterns are mixed together as they shift
  ;;     past each other.
  ;;   * The arbitrary constant in the #'LOGXOR expression is intended
  ;;     to help break up any weird anomalies we might otherwise get
  ;;     when hashing highly regular patterns.
  ;; (These are vaguely like the ideas used in many cryptographic
  ;; algorithms, but we're not pushing them hard enough here for them
  ;; to be cryptographically strong.)
  (let* ((xy (+ (* x 3) y)))
    (logand most-positive-fixnum
            (logxor 441516657
                    xy
                    (ash xy -5)))))

(defmacro mixf (v val) `(setq ,v (mix ,v ,val)))

(defun swxhash (key &optional (depthoid +max-hash-depthoid+))
  #+sbcl(declare (optimize speed))
  (declare (type (integer 0 #.+max-hash-depthoid+) depthoid))
  ;; Note: You might think it would be cleaner to use the ordering given in the
  ;; table from Figure 5-13 in the EQUALP section of the ANSI specification
  ;; here. So did I, but that is a snare for the unwary! Nothing in the ANSI
  ;; spec says that HASH-TABLE can't be a STRUCTURE-OBJECT, and in fact our
  ;; HASH-TABLEs *are* STRUCTURE-OBJECTs, so we need to pick off the special
  ;; HASH-TABLE behavior before we fall through to the generic STRUCTURE-OBJECT
  ;; comparison behavior.
  (typecase key
    (cons (list-swxhash key depthoid))
    (array (typecase key
             (simple-string (sxhash key))
             (t (array-swxhash key depthoid))))
    (hash-table (hash-table-swxhash key))
    (structure-object (structure-object-swxhash key depthoid))
    (number (number-swxhash key))
    (character (char-code key))
    (t (sxhash key))))

(defun Specware::swxhash (key) (swxhash key))

(defun array-swxhash (key depthoid)
  #+sbcl(declare (optimize speed))
  (declare (type array key))
  (declare (type (integer 0 #.+max-hash-depthoid+) depthoid))
  (typecase key
    ;; VECTORs have to be treated specially because ANSI specifies
    ;; that we must respect fill pointers.
    (vector
     (macrolet ((frob ()
                  '(let ((result 572539))
                     (declare (type fixnum result))
                     (mixf result (length key))
                    (when (plusp depthoid)
                      (decf depthoid)
                      (dotimes (i (length key))
                       (declare (type fixnum i))
                       (mixf result
                             (swxhash (aref key i) depthoid))))
                    result))
                (make-dispatch (types)
                  `(typecase key
                     ,@(loop for type in types
                             collect `(,type
                                       (frob))))))
       (make-dispatch (simple-base-string
                       (simple-array character (*))
                       simple-vector
                       (simple-array (unsigned-byte 8) (*))
                       (simple-array fixnum (*))
                       t))))
    ;; Any other array can be hashed by working with its underlying
    ;; one-dimensional physical representation.
    (t
     (let ((result 60828))
       (declare (type fixnum result))
       (dotimes (i (array-rank key))
         (mixf result (array-dimension key i)))
       (when (plusp depthoid)
         (decf depthoid)
         (dotimes (i (array-total-size key))
          (mixf result
                (swxhash (row-major-aref key i) depthoid))))
       result))))

(defun structure-object-swxhash (key depthoid)
  #+sbcl(declare (optimize speed))
  (declare (type structure-object key))
  (declare (type (integer 0 #.+max-hash-depthoid+) depthoid))
  #-sbcl (the fixnum 481929)            ; just some number
  #+sbcl
  (let* ((layout (%instance-layout key)) ; i.e. slot #0
         (length (layout-length layout))
         (classoid (layout-classoid layout))
         (name (classoid-name classoid))
         (result (mix (sxhash name) (the fixnum 79867))))
    (declare (type fixnum result))
    (dotimes (i (min depthoid (- length 1 (layout-n-untagged-slots layout))))
      (declare (type fixnum i))
      (let ((j (1+ i))) ; skipping slot #0, which is for LAYOUT
        (declare (type fixnum j))
        (mixf result
              (swxhash (%instance-ref key j)
                       (1- depthoid)))))
    ;; KLUDGE: Should hash untagged slots, too.  (Although +max-hash-depthoid+
    ;; is pretty low currently, so they might not make it into the hash
    ;; value anyway.)
    result))

(defun list-swxhash (key depthoid)
  #+sbcl(declare (optimize speed))
  (declare (type list key))
  (declare (type (integer 0 #.+max-hash-depthoid+) depthoid))
  (cond ((null key)
         (the fixnum 480929))
        ((zerop depthoid)
         (the fixnum 779578))
        (t
         (mix (swxhash (car key) (1- depthoid))
              (swxhash (cdr key) (1- depthoid))))))

(defun hash-table-swxhash (key)
  #+sbcl(declare (optimize speed))
  (declare (type hash-table key))
  (let ((result 103924836))
    (declare (type fixnum result))
    (mixf result (hash-table-count key))
    (mixf result (sxhash (hash-table-test key)))
    result))

(defun number-swxhash (key)
  #+sbcl(declare (optimize speed))
  (declare (type number key))
  (flet ((sxhash-double-float (val)
           (declare (type double-float val))
           ;; FIXME: Check to make sure that the DEFTRANSFORM kicks in and the
           ;; resulting code works without consing. (In Debian cmucl 2.4.17,
           ;; it didn't.)
           (sxhash val)))
    (etypecase key
      (integer (sxhash key))
      (float (macrolet ((frob (type)
                          (let ((lo (coerce most-negative-fixnum type))
                                (hi (coerce most-positive-fixnum type)))
                            `(cond (;; This clause allows FIXNUM-sized integer
                                    ;; values to be handled without consing.
                                    (<= ,lo key ,hi)
                                    (multiple-value-bind (q r)
                                        (floor (the (,type ,lo ,hi) key))
                                      (if (zerop (the ,type r))
                                          (sxhash q)
                                          (sxhash-double-float
                                           (coerce key 'double-float)))))
                                   (t
                                    (multiple-value-bind (q r) (floor key)
                                      (if (zerop (the ,type r))
                                          (sxhash q)
                                          (sxhash-double-float
                                           (coerce key 'double-float)))))))))
               (etypecase key
                 (single-float (frob single-float))
                 (double-float (frob double-float)))))
      (rational (if (and (<= most-negative-double-float
                             key
                             most-positive-double-float)
                         (= (coerce key 'double-float) key))
                    (sxhash-double-float (coerce key 'double-float))
                    (sxhash key)))
      (complex (if (zerop (imagpart key))
                   (number-swxhash (realpart key))
                   (let ((result 330231))
                     (declare (type fixnum result))
                     (mixf result (number-swxhash (realpart key)))
                     (mixf result (number-swxhash (imagpart key)))
                     result))))))

;;; slang-term-equal? hashtables  (for sbcl allegro & cmucl)
#+sbcl
(if (find-symbol "DEFINE-HASH-TABLE-TEST" "SB-INT")
    (eval `(,(find-symbol "DEFINE-HASH-TABLE-TEST" "SB-INT")
             'sw-equal? #'slang-term-equals-2 #'swxhash))
    (eval `(,(find-symbol "DEFINE-HASH-TABLE-TEST" "SB-EXT")
             sw-equal? swxhash)))
#+cmucl
(ext:define-hash-table-test 'sw-equal? #'slang-term-equals-2 #'swxhash)

;(defun Specware::make-sw-hash-table (&rest real-args)
;  #+allegro (apply #'make-hash-table :test #'slang-term-equals-2 :hash-function #'swxhash
;                   real-args)
;  #-allegro (apply #'make-hash-table :test 'sw-equal?
;                   real-args))

(defun Specware::make-sw-hash-table (&key (size 16) (rehash-size 1.5))
  #+allegro (make-hash-table :test 'slang-term-equals-2 :hash-function 'swxhash
                             :size size :rehash-size rehash-size)
  #-allegro (make-hash-table :test 'sw-equal?
                             :size size :rehash-size rehash-size))

;;; optimizations of not-equals for Booleans and Strings:

;; The boolean version of slang-term-equals-2 is just cl:eq, 
;; and we wouldn't need boolean-not-equals-2 if neq was also defined in ANSI Common Lisp.
;; We avoid calling this neq, to mimimize confusion in implementations that define neq.
(defun boolean-not-equals-2 (x y) 
  (not (eq x y)))

(defun string-not-equals-2 (x y)
  ;; Note: this     returns NIL or T  
  ;;       string/= returns NIL or integer, which could confuse subsequent boolean 
  ;;       comparisons implemented with cl::eq.
  (not (string= x y)))

;; CL 'and' and 'or' correspond to (non-strict) "&&" and "||"

;; Nothing in CL corresponds to boolean 'implies':
;; TODO: This probably isn't (or shouldn't be) possible, 
;;       since syntax ("&&", "||", "=>", etc.) can't (shouldn't) be passed as an arg
(defun implies-2 (x y) 
  (or (not x) y))

;; Optimization
(define-compiler-macro List-Spec::|!length| (l)
  `(length ,l))

(define-compiler-macro List-Spec::++-2 (l1 l2)
 `(append ,l1 ,l2))

;; assert is in Library/General/Assert
;; If optimization property speed is 3 and safety is less than 3 then this is compiled away.
;; Otherwise it tests condition and gives a run-time error if it is false
(defmacro Assert-Spec::|!assert| (condn)
          `(assert ,condn))

#|

 Tests:

 (slang-term-equals (cons (vector 1 2 3) (vector 1 2 3)))

 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "3")))
 (slang-term-equals (cons (vector 1 2 "3") (vector 1 2 "4")))

 (slang-term-equals (cons 
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  3)
            (list 'Quotient 
                  (lambda (x) (eq (< 10 (car x)) (< 10 (cdr x))))
                  11)))

|#


