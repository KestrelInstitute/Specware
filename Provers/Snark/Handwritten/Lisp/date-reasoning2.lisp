;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: date-reasoning2.lisp
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

;;; date-point and date-interval are external (solely for user convenience) function symbols
;;; for date points and intervals; they are replaced by utime-point and utime-interval when
;;; formulas are input
;;;
;;; utime-point and utime-interval are internal function symbols for dates
;;; they use Lisp universal time representation (which counts seconds since 1900-01-01T00:00:00)
;;;
;;; date-point and date-interval use 1 to 6 integer arguments
;;;   year, month, day, hour, minute, second
;;; to specify dates
;;;
;;; examples of SNARK dates and their translations:
;;; (date-point 2002 4 1 16 27 20)                       -> (utime-point 3226667240)
;;; (date-interval 2002 4 1 16 34)                       -> (utime-interval 3226667640 3226667700)
;;; (date-interval 2002 4 1 16 34 :until 2002 4 1 16 35) -> (utime-interval 3226667640 3226667700)
;;; (date-interval 2002 4 1 16 34 :until 2002 4 1 17)    -> (utime-interval 3226667640 3226669200))

(declare-snark-option2 date-point-function-name 'date-point)
(declare-snark-option2 date-interval-function-name 'date-interval)

(declare-snark-option2 utime-point-function-name 'utime-point)
(declare-snark-option2 utime-interval-function-name 'utime-interval)

(defun can-be-date-p (list &optional action)
  ;; a proper date is a list of 1 to 6 integers with appropriate values
  ;; interpreted as year, month, day, hour, minute, and second
  (or (let ((year (pop list)))
        (and (integerp year)
             (<= 1900 year)
             (implies
              list
              (let ((month (pop list)))
                (and (integerp month)
                     (<= 1 month 12)
                     (implies
                      list
                      (let ((day (pop list)))
                        (and (integerp day)
                             (<= 1 day (days-per-month month year))
                             (implies
                              list
                              (let ((hour (pop list)))
                                (and (integerp hour)
                                     (<= 0 hour 23)
                                     (implies
                                      list
                                      (let ((minute (pop list)))
                                        (and (integerp minute)
                                             (<= 0 minute 59)
                                             (implies
                                              list
                                              (let ((second (pop list)))
                                                (and (integerp second)
                                                     (<= 0 second 59)	;no leap seconds!
                                                     (null list))))))))))))))))))
      (and action (funcall action "~A cannot be a date." list))))

(defun encode-universal-time-point (year &optional month day hour minute second)
  (encode-universal-time
   (or second 0)
   (or minute 0)
   (or hour 0)
   (or day 1)
   (or month 1)
   year
   0))

(defun decode-universal-time-point (universal-time-point)
  (mvlet (((:values second minute hour day month year)
           (decode-universal-time universal-time-point 0)))
    (cond
     ((neql 0 second)
      (list year month day hour minute second))
     ((neql 0 minute)
      (list year month day hour minute))
     ((neql 0 hour)
      (list year month day hour))
     ((neql 1 day)
      (list year month day))
     ((neql 1 month)
      (list year month))
     (t
      (list year)))))

(defun encode-universal-time-interval (year &optional month day hour minute second)
  (let ((v (encode-universal-time-point year month day hour minute second)))
    (list v
          (+ v (or (and second 1)					;1 second long interval
                   (and minute 60)					;1 minute long interval
                   (and hour 3600)					;1 hour long interval
                   (and day 86400)					;1 day long interval
                   (and month (* (days-per-month month year) 86400))	;1 month long interval
                   (* (if (leap-year-p year) 366 365) 86400))))))	;1 year long interval

(defun decode-universal-time-interval (universal-time-interval)
  (mvlet (((:list start finish) universal-time-interval))
    (values (decode-universal-time-point start) (decode-universal-time-point finish))))

(defun pp-compare-universal-times (point1 point2)
  (cond
   ((< point1 point2)
    'p<p)
   ((> point1 point2)
    'p>p)
   (t
    'p=p)))

(defun ii-compare-universal-times (interval1 interval2)
  (mvlet (((:list start1 finish1) interval1)
          ((:list start2 finish2) interval2))
    (cond
     ((eql start1 start2)
      (if (< finish1 finish2) 's (if (> finish1 finish2) 'si '=)))
     ((eql finish1 finish2)
      (if (> start1 start2) 'f 'fi))
     ((<= finish1 start2)
      (if (eql finish1 start2) 'm '<))
     ((>= start1 finish2)
      (if (eql start1 finish2) 'mi '>))
     ((< start1 start2)
      (if (> finish1 finish2) 'di 'o))
     (t
      (if (< finish1 finish2) 'd 'oi)))))

(defun pi-compare-universal-times (point interval)
  (mvlet (((:list start finish) interval))
    (cond
     ((<= point start)
      (if (eql point start) 'p_s_i 'p<i))
     ((>= point finish)
      (if (eql point finish) 'p_f_i 'p>i))
     (t
      'p_d_i))))

(defun declare-date-functions (&key intervals points)
  (when points
    (declare-function-symbol
     (date-point-function-name?) :any
     :input-function 'input-date-point)
    (declare-function-symbol
     (utime-point-function-name?) 1
     :sort (list (time-point-sort-name?))
     :to-lisp-code 'utime-point-term-to-lisp))
  (when intervals
    (declare-function-symbol
     (date-interval-function-name?) :any
     :input-function 'input-date-interval)
    (declare-function-symbol
     (utime-interval-function-name?) 2
     :sort (list (time-interval-sort-name?))
     :to-lisp-code 'utime-interval-term-to-lisp))
  (let-options ((print-symbol-in-use-warnings nil))
    (when points
      (declare-predicate-symbol
       (time-pp-main-relation-name?) 3
       :rewrite-code 'time-pp-atom-rewriter-for-dates))
    (when intervals
      (declare-predicate-symbol
       (time-ii-main-relation-name?) 3
       :rewrite-code 'time-ii-atom-rewriter-for-dates))
    (when (and points intervals)
      (declare-predicate-symbol
       (time-pi-main-relation-name?) 3
       :rewrite-code 'time-pi-atom-rewriter-for-dates)))
  nil)
  
(defun input-date-point (head args polarity)
  (declare (ignore head polarity))
  (make-compound (input-function-symbol (utime-point-function-name?) 1)
                 (declare-number (apply 'encode-universal-time-point args))))

(defun input-date-interval (head args polarity)
  (declare (ignore head polarity))
  (let (v start finish)
    (cond
     ((setf v (member :until args))
      (setf start (apply 'encode-universal-time-point (ldiff args v)))
      (setf finish (apply 'encode-universal-time-point (rest v)))
      (cl:assert (< start finish)))
     (t
      (setf v (apply 'encode-universal-time-interval args))
      (setf start (first v))
      (setf finish (second v))))
    (declare-number start)
    (declare-number finish)
    (make-compound (input-function-symbol (utime-interval-function-name?) 2) start finish)))

(defun utime-point-term-to-lisp (head args subst)
  (declare (ignore head))
  (let ((arg1 (first args)))
    (and (dereference arg1 subst :if-constant (integerp arg1))
         (cons (date-point-function-name?)
               (decode-universal-time-point arg1)))))

(defun utime-interval-term-to-lisp (head args subst)
  (declare (ignore head))
  (let ((arg1 (first args))
        (arg2 (second args)))
    (and (dereference arg1 subst :if-constant (integerp arg1))
         (dereference arg2 subst :if-constant (integerp arg2))
         (cons (date-interval-function-name?)
               (append (decode-universal-time-point arg1)
                       (cons :until (decode-universal-time-point arg2)))))))

(defun utime-point-term-p (term subst)
  (dereference
   term subst
   :if-compound-appl (let ((head (heada term)))
                       (and (eq (utime-point-function-name?) (function-name head))
                            (eql 1 (function-arity head))
                            (let* ((args (argsa term))
                                   (arg1 (first args)))
                              (and (dereference arg1 subst :if-constant (integerp arg1))
                                   arg1))))))

(defun utime-interval-term-p (term subst)
  (dereference
   term subst
   :if-compound-appl (let ((head (heada term)))
                       (and (eq (utime-interval-function-name?) (function-name head))
                            (eql 2 (function-arity head))
                            (let* ((args (argsa term))
                                   (arg1 (first args))
                                   (arg2 (second args)))
                              (and (dereference arg1 subst :if-constant (integerp arg1))
                                   (dereference arg2 subst :if-constant (Integerp arg2))
                                   (if (and (eql arg1 (first args))
                                            (eql arg2 (second args)))
                                       args
                                       (list arg1 arg2))))))))

(defun time-ii-atom-rewriter-for-dates (term subst)
  (let ((args (args term)) m n)
    (cond
     ((and (setf m (utime-interval-term-p (first args) subst))
           (setf n (utime-interval-term-p (second args) subst)))
      (let ((v (third args)))
        (dereference v subst)
        (setf v (nth (jepd-relation-code (ii-compare-universal-times m n) $time-ii-relation-code) v))
        (if (dereference v subst :if-variable t) false true)))
     (t
      none))))

(defun time-pp-atom-rewriter-for-dates (term subst)
  (let ((args (args term)) m n)
    (cond
     ((and (setf m (utime-point-term-p (first args) subst))
           (setf n (utime-point-term-p (second args) subst)))
      (let ((v (third args)))
        (dereference v subst)
        (setf v (nth (jepd-relation-code (pp-compare-universal-times m n) $time-pp-relation-code) v))
        (if (dereference v subst :if-variable t) false true)))
     (t
      none))))

(defun time-pi-atom-rewriter-for-dates (term subst)
  (let ((args (args term)) m n)
    (cond
     ((and (setf m (utime-point-term-p (first args) subst))
           (setf n (utime-interval-term-p (second args) subst)))
      (let ((v (third args)))
        (dereference v subst)
        (setf v (nth (jepd-relation-code (pi-compare-universal-times m n) $time-pi-relation-code) v))
        (if (dereference v subst :if-variable t) false true)))
     (t
      none))))

;;; date-reasoning2.lisp EOF
