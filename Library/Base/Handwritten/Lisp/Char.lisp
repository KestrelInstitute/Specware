;; Built in functions for characters. A large fraction of these correspond to those
;; supported in the SML basis library as well as in Common Lisp.

(DEFPACKAGE :CHAR-SPEC)
(IN-PACKAGE :CHAR-SPEC)


;;; The functions commented out acquire definitions from the compilation of Specware4.sw
;;;  before they are used.  [This wasn't true, so I restored several definitions here.]

(defun toString (x)
  (string x))

(defun isUpperCase (ch)
  (upper-case-p ch))

(defun isLowerCase (ch)
  (lower-case-p ch))

(defun isAlphaNum (ch)
  (alphanumericp ch))

(defun isAlpha (ch)
  (alpha-char-p ch))

(defun isAscii (ch)
  (standard-char-p ch))

(defun isNum (ch)
  (and (<= 48 (char-code ch)) (<= (char-code ch) 57)))

(defun toUpperCase (ch)
  (char-upcase ch))

(defun toLowerCase (ch)
  (char-downcase ch))

(defun ord (ch)
  (char-code ch))

(defun chr (n)
  (code-char n))

;;;  (defun compare (s1 s2) 
;;;    (nat-spec::compare (ord s1) (ord s2)))
;;;
;;;  (defun compare-1 (x) (compare (car x) (cdr x)))
