(DEFPACKAGE "CHAR-SPEC")
(IN-PACKAGE "CHAR-SPEC")


;;; While in Metaslang characters are exactly those occupying decimal
;;; positions 0 to 255 in the ISO-8859-1 code table, the Common Lisp
;;; standard does not commit to that. So, Specware-generated code and the
;;; hand-written code in this file may not work as expected in Common Lisp
;;; implementation whose characters do not coincide with, or at least
;;; include, the Metaslang characters.


(defun ord (ch)
  (char-code ch))

(defun chr (n)
  (code-char n))

(defun isUpperCase (ch)
  (upper-case-p ch))

(defun isLowerCase (ch)
  (lower-case-p ch))

(defun isAlpha (ch)
  (alpha-char-p ch))

(defun isNum (ch)
  (and (<= 48 (char-code ch)) (<= (char-code ch) 57)))

(defun isAlphaNum (ch)
  (alphanumericp ch))

(defun isAscii (ch)
  (standard-char-p ch))

(defun toUpperCase (ch)
  (char-upcase ch))

(defun toLowerCase (ch)
  (char-downcase ch))
