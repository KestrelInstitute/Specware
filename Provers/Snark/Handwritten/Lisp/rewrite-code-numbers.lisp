;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: rewrite-code-numbers.lisp
;;; The contents of this file are subject to the Mozilla Public License
;;; Version 1.1 (the "License"); you may not use this file except in
;;; compliance with the License. You may obtain a copy of the License at
;;; http://www.mozilla.org/MPL/
;;;
;;; Software distributed under the License is distributed on an "AS IS"
;;; basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See the
;;; License for the specific language governing rights and limitations
;;; under the License.
;;;
;;; The Original Code is SNARK.
;;; The Initial Developer of the Original Code is SRI International.
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(declare-snark-option use-code-for-numbers nil nil)

(defmethod use-code-for-numbers :before (&optional (value t))
  (cond
   (value
    (use-lisp-types-as-sorts t)
    ;; KIF allows - and / with arity > 2, SNARK doesn't
    (mapc #'declare-function-rewrite-code
          '((*           :any times-term-rewriter :sort number)
            (+           :any plus-term-rewriter :sort number)
            (-           2 difference-term-rewriter :alias difference :sort number)
            (-           1 minus-term-rewriter :alias minus :sort number)
            (/           2 quotient-term-rewriter :alias quotient :sort number)
            (/           1 recip-term-rewriter :alias recip :sort number)
            (1+          1 add1-term-rewriter :sort number)
            (1-          1 sub1-term-rewriter :sort number)
            (abs         1 abs-term-rewriter :sort nonnegative)
            (expt        2 expt-term-rewriter :sort number)
            (gcd         :any gcd-term-rewriter :sort number)
            (lcm         :any lcm-term-rewriter :sort number)
            (log         2 log-term-rewriter :sort number)
            (sqrt        1 sqrt-term-rewriter :sort number)

            (max         :any max-term-rewriter :sort real)
            (min         :any min-term-rewriter :sort real)

            (mod         2 mod-term-rewriter :sort real)
            (rem         2 rem-term-rewriter :sort real)

            (numerator   1 numerator-term-rewriter :sort integer)
            (denominator 1 denominator-term-rewriter :sort positive-integer)

            (ceiling     1 ceiling-term-rewriter :sort integer)
            (floor       1 floor-term-rewriter :sort integer)
            (round       1 round-term-rewriter :sort integer)
            (truncate    1 truncate-term-rewriter :sort integer)

            (realpart    1 realpart-term-rewriter :sort real)
            (imagpart    1 imagpart-term-rewriter :sort real)
            ))
    (mapc #'declare-predicate-rewrite-code
          '((integer   1 integer-atom-rewriter)
            (real      1 real-atom-rewriter)
            (complex   1 complex-atom-rewriter)
            (number    1 number-atom-rewriter)
            (natural   1 natural-atom-rewriter)
            (rational  1 rational-atom-rewriter)
            (ratio     1 ratio-atom-rewriter)
            (float     1 float-atom-rewriter)
            (approx    3 approx-atom-rewriter)
            (==        2 ==-atom-rewriter)
            (=/=       2 =/=-atom-rewriter)
            (<         2 <-atom-rewriter)
            (>         2 >-atom-rewriter)
            (=<        2 =<-atom-rewriter)
            (>=        2 >=-atom-rewriter)
            (positive  1 positive-atom-rewriter)
            (negative  1 negative-atom-rewriter)
            (nonnegative 1 nonnegative-atom-rewriter)
            (zero      1 zero-atom-rewriter)
            (even      1 even-atom-rewriter)
            (odd       1 odd-atom-rewriter)
            )))))

(defmacro when-using-code-for-numbers (&body body)
  `(if (use-code-for-numbers?) (progn ,@body) none))

(defun naturalp (x &optional subst)
  (if (null subst)
      (and (integerp x) (not (minusp x)) x)
      (dereference x subst :if-constant (and (integerp x) (not (minusp x)) x))))

(defun nonnegativep (x &optional subst)
  (if (null subst)
      (and (numberp x) (not (minusp x)) x)
      (dereference x subst :if-constant (and (numberp x) (not (minusp x)) x))))

(defun positive-integer-p (x &optional subst)
  (if (null subst)
      (and (integerp x) (plusp x) x)
      (dereference x subst :if-constant (and (integerp x) (plusp x) x))))

(defun negative-integer-p (x &optional subst)
  (if (null subst)
      (and (integerp x) (minusp x) x)
      (dereference x subst :if-constant (and (integerp x) (minusp x) x))))

(defun even-integer-p (x &optional subst)
  (if (null subst)
      (and (integerp x) (evenp x) x)
      (dereference x subst :if-constant (and (integerp x) (evenp x) x))))

(defun odd-integer-p (x &optional subst)
  (if (null subst)
      (and (integerp x) (oddp x) x)
      (dereference x subst :if-constant (and (integerp x) (oddp x) x))))

(defun ratiop (x &optional subst)
  (if (null subst)
      (and (rationalp x) (not (integerp x)) x)
      (dereference x subst :if-constant (and (rationalp x) (not (integerp x)) x))))

(defmacro number-term-evaluation (result &optional (cond t))
  `(when-using-code-for-numbers
     (let ((x (arg1 term)))
       (if (and (dereference x subst :if-constant (numberp x))
                ,cond)
           (declare-constant-symbol ,result)
           none))))

(defmacro number*number-term-evaluation (result &optional (cond t))
  `(when-using-code-for-numbers
     (mvlet (((:list x y) (args term)))
       (if (and (dereference x subst :if-constant (numberp x))
                (dereference y subst :if-constant (numberp y))
                ,cond)
           (declare-constant-symbol ,result)
           none))))

(defmacro number-atom-evaluation (form)
  `(when-using-code-for-numbers
     (let ((x (arg1 atom)))
       (dereference
        x subst
        :if-constant (if (numberp x) (if ,form true false) (if-constant-constructor-then-false x))
        :if-compound (if (function-constructor (head x)) false none)
        :if-variable none))))

(defmacro number*number-atom-evaluation (form)
  `(when-using-code-for-numbers
     (mvlet (((:list x y) (args atom)))
       (if (and (dereference x subst :if-constant (numberp x))
                (dereference y subst :if-constant (numberp y)))
           (if ,form true false)
           none))))

(defmacro numbers-term-evaluation (fn)
  ;; doesn't flatten
  `(when-using-code-for-numbers
    (let ((args (args term)) (number nil) (reduced nil))
      (dolist (arg args)
        (when (dereference arg subst :if-constant (numberp arg))
          (if number
              (setq number (,fn number arg) reduced t)
              (setq number arg))))
      (if reduced
          (let ((nonnumbers nil) nonnumbers-last)
            (dolist (arg args)
              (unless (dereference arg subst :if-constant (numberp arg))
                (collect arg nonnumbers)))
            (cond
             ((null nonnumbers)
              (declare-constant-symbol number))
             (t
              (make-compound* (head term) (declare-constant-symbol number) nonnumbers))))
          none))))

(defun times-term-rewriter       (term subst) (numbers-term-evaluation *))
(defun plus-term-rewriter        (term subst) (numbers-term-evaluation +))
(defun gcd-term-rewriter         (term subst) (numbers-term-evaluation gcd))
(defun lcm-term-rewriter         (term subst) (numbers-term-evaluation lcm))
(defun max-term-rewriter         (term subst) (numbers-term-evaluation max))
(defun min-term-rewriter         (term subst) (numbers-term-evaluation min))

(defun minus-term-rewriter       (term subst) (number-term-evaluation (- x)))
(defun recip-term-rewriter       (term subst) (number-term-evaluation (/ x) (/= 0 x)))
(defun add1-term-rewriter        (term subst) (number-term-evaluation (1+ x)))
(defun sub1-term-rewriter        (term subst) (number-term-evaluation (1- x)))
(defun abs-term-rewriter         (term subst) (number-term-evaluation (abs x)))
(defun ceiling-term-rewriter     (term subst) (number-term-evaluation (ceiling x)))
(defun denominator-term-rewriter (term subst) (number-term-evaluation (denominator x)))
(defun floor-term-rewriter       (term subst) (number-term-evaluation (floor x)))
(defun imagpart-term-rewriter    (term subst) (number-term-evaluation (imagpart x)))
(defun log-term-rewriter         (term subst) (number-term-evaluation (log x) (/= 0 x)))
(defun numerator-term-rewriter   (term subst) (number-term-evaluation (numerator x)))
(defun realpart-term-rewriter    (term subst) (number-term-evaluation (realpart x)))
(defun round-term-rewriter       (term subst) (number-term-evaluation (round x)))
(defun sqrt-term-rewriter        (term subst) (number-term-evaluation (sqrt x)))
(defun truncate-term-rewriter    (term subst) (number-term-evaluation (truncate x)))

(defun difference-term-rewriter  (term subst) (number*number-term-evaluation (- x y)))
(defun quotient-term-rewriter    (term subst) (number*number-term-evaluation (/ x y) (/= 0 y)))
(defun expt-term-rewriter        (term subst) (number*number-term-evaluation (expt x y)))
(defun mod-term-rewriter         (term subst) (number*number-term-evaluation (mod x y) (/= 0 y)))
(defun rem-term-rewriter         (term subst) (number*number-term-evaluation (rem x y) (/= 0 y)))

(defun integer-atom-rewriter    (atom subst) (number-atom-evaluation (integerp x)))
(defun real-atom-rewriter       (atom subst) (number-atom-evaluation (realp x)))
(defun complex-atom-rewriter    (atom subst) (number-atom-evaluation (complexp x)))
(defun number-atom-rewriter     (atom subst) (number-atom-evaluation (numberp x)))
(defun natural-atom-rewriter    (atom subst) (number-atom-evaluation (naturalp x)))
(defun rational-atom-rewriter   (atom subst) (number-atom-evaluation (rationalp x)))
(defun ratio-atom-rewriter      (atom subst) (number-atom-evaluation (ratiop x)))
(defun float-atom-rewriter      (atom subst) (number-atom-evaluation (floatp x)))
(defun positive-atom-rewriter   (atom subst) (number-atom-evaluation (plusp x)))
(defun negative-atom-rewriter   (atom subst) (number-atom-evaluation (minusp x)))
(defun nonnegative-atom-rewriter(atom subst) (number-atom-evaluation (nonnegativep x)))
(defun zero-atom-rewriter       (atom subst) (number-atom-evaluation (zerop x)))
(defun even-atom-rewriter       (atom subst) (number-atom-evaluation (even-integer-p x)))
(defun odd-atom-rewriter        (atom subst) (number-atom-evaluation (odd-integer-p x)))

(defun ==-atom-rewriter         (atom subst) (number*number-atom-evaluation (= x y)))
(defun =/=-atom-rewriter        (atom subst) (number*number-atom-evaluation (/= x y)))
(defun <-atom-rewriter          (atom subst) (number*number-atom-evaluation (< x y)))
(defun >-atom-rewriter          (atom subst) (number*number-atom-evaluation (> x y)))
(defun =<-atom-rewriter         (atom subst) (number*number-atom-evaluation (<= x y)))
(defun >=-atom-rewriter         (atom subst) (number*number-atom-evaluation (>= x y)))

(defun approx-atom-rewriter (atom subst)
  (when-using-code-for-numbers
    (mvlet (((:list t1 t2 tol) (args atom)))
      (if (and (dereference t1 subst :if-constant (numberp t1))
               (dereference t2 subst :if-constant (numberp t2))
               (dereference tol subst :if-constant (numberp tol)))
          (if (<= (abs (- t1 t2)) tol) true false)
          none))))

;;; rewrite-code-numbers.lisp EOF
