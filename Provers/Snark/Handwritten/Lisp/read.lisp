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
;;; Portions created by the Initial Developer are Copyright (C) 1981-2002.
;;; All Rights Reserved.
;;;
;;; Contributor(s): Mark E. Stickel <stickel@ai.sri.com>.

(in-package :snark)

(defun letter-char-p (char)
  (or (alpha-char-p char)
      (eql char #\$)
      (eql char #\_)
      (eql char #\.)
      (eql char #\!)
      (eql char #\?)))

(defun separator-char-p (char)
  (or (eql char #\()
      (eql char #\))
      (eql char #\,)))

(defun white-space-char-p (char)
  (or (eql char #\space)
      (eql char #\tab)
      (eql char #\newline)
      (eql char #\return)
      (eql char #\linefeed)
      (eql char #\page)))

(defun tokenize (string &optional (start 0) (end (length string)))
  (let ((pos start))
    (loop
      (cond
	((and (< pos end) (white-space-char-p (elt string pos)))
	 (incf pos))
	(t
	 (return))))
    (cond
      ((>= pos end)
       nil)
      (t
       (let ((c (elt string pos)))
	 (cond
	   ((digit-char-p c)
	    (multiple-value-bind (x pos)
		(tokenize-starting-with-digit string pos end)
	      (cons x (tokenize string pos end))))
	   ((letter-char-p c)
	    (multiple-value-bind (id pos)
		(tokenize-identifier string pos end)
	      (cons id (tokenize string pos end))))
	   ((separator-char-p c)
	    (cons c (tokenize string (1+ pos) end)))
	   (t
	    (multiple-value-bind (op pos)
		(tokenize-special string pos end)
	      (cons op (tokenize string pos end))))))))))

(defun tokenize-starting-with-digit (string &optional (start 0) (end (length string)))
  (let ((pos start) (num 0) (decpt nil) (n 0) (d 1) c)
    (loop
      (cond
	((>= pos end)
	 (return (values (if (and decpt (> d 1)) (+ num (/ n (float d))) num) pos)))
	((eql (setq c (elt string pos)) #\.)
	 (if (not decpt)
	     (setq decpt t)
	     (return (tokenize-identifier string start end))))
	((letter-char-p c)
	 (return (tokenize-identifier string start end)))
	((setq c (digit-char-p c))
	 (if (not decpt)
	     (setq num (+ (* num 10) c))
	     (setq n (+ (* n 10) c)
		   d (* d 10))))
	(t
	 (return (values (if (and decpt (> d 1)) (+ num (/ n (float d))) num) pos))))
      (incf pos))))

(defun tokenize-identifier (string &optional (start 0) (end (length string)))
  (let ((pos start) (id nil) c)
    (loop
      (cond
	((and (< pos end)
	      (or (letter-char-p (setq c (elt string pos)))
		  (digit-char-p c)))
	 (setq id (cons (char-upcase c) id)))
	(t
	 (return (values (intern (coerce (nreverse id) 'string)) pos))))
      (incf pos))))

(defun tokenize-special (string &optional (start 0) (end (length string)))
  (let ((pos start) (op nil) c)
    (loop
      (cond
	((and (< pos end)
	      (not (or (letter-char-p (setq c (elt string pos)))
		       (digit-char-p c)
		       (white-space-char-p c)
		       (separator-char-p c))))
	 (setq op (cons c op)))
	(t
	 (return (values (intern (coerce (nreverse op) 'string)) pos))))
      (incf pos))))

;;; incomplete: doesn't read infix forms
;;; but will convert "p(a,b,c)" to (P A B C)

(defun tokens-to-lisp (tokens)
  (let ((token1 (pop tokens)))
    (cond
      ((eql token1 #\()
       (let (term)
	 (multiple-value-setq (term tokens) (tokens-to-lisp tokens))
	 (unless (eql (pop tokens) #\))
	   (error "Syntax error."))
	 (values term tokens)))
      ((numberp token1)
       (values token1 tokens))
      ((symbolp token1)
       (cond
	 ((null tokens)
	  (values token1 tokens))
	 (t
	  (let ((token2 (first tokens)))
	    (cond
	      ((or (eql token2 #\,)
		   (eql token2 #\)))
	       (values token1 tokens))
	      ((eql token2 #\()
	       (setq tokens (rest tokens))
	       (let ((args nil) arg)
		 (loop
		   (when (eql (first tokens) #\))
		     (return (values (cons token1 (nreverse args)) (rest tokens))))
		   (multiple-value-setq (arg tokens) (tokens-to-lisp tokens))
		   (cond
		     ((eql (first tokens) #\,)
		      (setq tokens (rest tokens)))
		     ((eql (first tokens) #\))
		      )
		     (t
		      (error "Syntax error.")))
		   (push arg args)))))))))
      (t
       (error "Syntax error.")))))

;;; read.lisp EOF
