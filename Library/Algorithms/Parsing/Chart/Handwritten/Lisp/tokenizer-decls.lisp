;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defconstant +word-symbol-start-code+         1)
(defconstant +word-symbol-continue-code+      2)
;(defconstant +word-symbol-escape-code+       3)

(defconstant +non-word-symbol-start-code+     4)
(defconstant +non-word-symbol-continue-code+  5)
;(defconstant +non-word-symbol-escape-code+   6)

(defconstant +number-start-code+              7)
(defconstant +number-continue-code+           8)

(defconstant +string-quote-code+              9)
(defconstant +string-escape-code+            10)

(defconstant +whitespace-code+               11)

(defconstant +separator-code+                12)

(defconstant +comment-to-eol-code+           13)
(defconstant +char-literal-start-code+       14)

(defconstant +syllable-separator-code+       15)  ; underbar in some contexts
(defconstant +wildcard-code+                 16)  ; underbar in other contexts

(defconstant +maybe-open-comment-or-pragma-code+ -1)
(defconstant +maybe-start-of-ad-hoc-token+       -2)

(defstruct tokenizer-parameters
  name
  whitespace-table
  word-symbol-table
  non-word-symbol-table
  number-table
  string-table
  digits-may-start-symbols?
  comment-table
  separator-tokens
  cp-descriptors
  ad-hoc-types-ht
  ad-hoc-table
  ad-hoc-strings)

(defstruct (cp-descriptor (:type vector)) ; comment-or-pragma-descriptor
  prefix
  postfix
  recursive?
  eof-ok?
  pragma?)

(defparameter +tokenizer-eof+ (cons nil nil))

(defstruct pseudo-stream
  unread-chars
  stream)

(defmacro ps-read-char (s)
  (let ((s-var (gensym)))
    `(let ((,s-var ,s))
       (or (pop (pseudo-stream-unread-chars ,s-var))
	   (loop
	     (let ((byte (read-byte (pseudo-stream-stream ,s-var) nil +tokenizer-eof+)))
	       (cond ((eq byte +tokenizer-eof+)  (return +tokenizer-eof+))
		     ((< byte #x7F)              (return (code-char byte)))
		     (t 
		      (warn "Ignoring non-ASCII character: \~2,0X" byte)))))))))

(defmacro ps-unread-char (char s)
  `(push ,char (pseudo-stream-unread-chars ,s)))

