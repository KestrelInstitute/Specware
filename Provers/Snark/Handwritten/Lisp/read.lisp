;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark -*-
;;; File: read.lisp
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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2003.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(definline letter-char-p (char)
  (or (alpha-char-p char)
      (eql #\$ char)
      (eql #\_ char)
      (eql #\! char)
      (eql #\? char)))

(definline separator-char-p (char)
  (or (eql #\( char)
      (eql #\) char)
      (eql #\[ char)
      (eql #\] char)
      (eql #\, char)
      (eql #\. char)))

(definline whitespace-char-p (char)
  (or (eql #\space char)
      (eql #\tab char)
      (eql #\newline char)
      (eql #\return char)
      (eql #\linefeed char)
      (eql #\page char)))

(defun tokenize (string &optional (pos 0) (end (length string)))
  (let ((tokens nil) tokens-last)
    (labels
      ((tokenize-identifier ()
         (let ((start pos) ch)
           (incf pos)
           (loop
             (cond
              ((eql end pos)
               (return))
              ((or (digit-char-p (setf ch (char string pos)))
                   (letter-char-p ch)
                   (eql #\- ch))
               (incf pos))
              (t
               (return))))
           (subseq string start pos)))
       (tokenize-special ()
         (let ((start pos) ch)
           (incf pos)
           (loop
             (cond
              ((eql end pos)
               (return))
              ((not (or (digit-char-p (setf ch (char string pos)))
                        (letter-char-p ch)
                        (separator-char-p ch)
                        (whitespace-char-p ch)))
               (incf pos))
              (t
               (return))))
           (subseq string start pos)))
       (tokenize-number ()
         (let ((nopoint t) (num 0) (d 10) n ch cv)
           (loop
             (cond
              ((eql end pos)
               (return))
              ((setf cv (digit-char-p (setf ch (char string pos))))
               (if nopoint
                   (setf num (+ (* 10 num) cv))
                   (setf n (+ (* 10 n) cv) d (* 10 d)))
               (incf pos))
              ((and nopoint
                    (eql #\. ch)
                    (let ((pos (1+ pos)))
                      (and (not (eql end pos))
                           (setf n (digit-char-p (char string pos))))))
               (setf nopoint nil) 
               (incf pos 2))
              (t
               (return))))
           (if nopoint num (+ num (/ (float n) d))))))
      (loop
        (loop
          (cond
           ((<= end pos)
            (return))
           ((whitespace-char-p (char string pos))
            (incf pos))
           (t
            (return))))
        (let (ch)
          (cond
           ((<= end pos)
            (return))
           ((separator-char-p (setf ch (char string pos)))
            (incf pos)
            (collect ch tokens))
           ((letter-char-p ch)
            (collect (tokenize-identifier) tokens))
           ((digit-char-p ch)
            (collect (tokenize-number) tokens))
           (t
            (collect (tokenize-special) tokens))))))
    tokens))

;;; incomplete: doesn't read infix forms
;;; but will convert "p(a,b,c)" to (p a b c) and "[a,b,c]" to (LIST a b c)

(defun tokens-to-lisp (tokens &key (intern t) (period nil))
  (labels
    ((tokens-to-lisp1 (tokens)
       (let ((token1 (pop tokens)))
         (cond
          ((numberp token1)
           (values token1 tokens))
          ((equal "++" token1)					;for TPTP
           (tokens-to-lisp1 tokens))
          ((equal "--" token1)					;for TPTP
           (let (term)
             (multiple-value-setq (term tokens) (tokens-to-lisp1 tokens))
             (values (list (intern? "NOT") term) tokens)))
          ((stringp token1)
           (if (eql #\( (first tokens))
               (tokens-to-lisp2 (intern? token1) (rest tokens) #\))
               (values (intern? token1) tokens)))
          ((eql #\[ token1)
           (tokens-to-lisp2 (intern? "LIST") tokens #\]))
          (t
           (error "Syntax error.")))))
     (tokens-to-lisp2 (token1 tokens end)
       (cond
        ((eql end (first tokens))
         (values (cons token1 nil) (rest tokens)))
        (t
         (let ((args nil) arg)
           (loop
             (multiple-value-setq (arg tokens) (tokens-to-lisp1 tokens))
             (push arg args)
             (cond
              ((eql end (first tokens))
               (return (values (cons token1 (nreverse args)) (rest tokens))))
              ((eql #\, (first tokens))
               (setf tokens (rest tokens)))
              (t
               (error "Syntax error."))))))))
     (intern? (token)
       (if intern (intern token) token)))
    (let (term)
      (multiple-value-setq (term tokens) (tokens-to-lisp1 tokens))
      (when period
        (cl:assert (eql #\. (first tokens)))
        (setf tokens (rest tokens)))
      (values term tokens))))

(defun read-prolog-term (string &key (start 0) (end (length string)) (intern t) (period nil))
  (tokens-to-lisp (tokenize string start end) :intern intern :period period))

;;; read.lisp EOF
