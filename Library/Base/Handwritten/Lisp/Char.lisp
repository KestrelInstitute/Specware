(DEFPACKAGE "SPECTOLISP")
(DEFPACKAGE "CHAR-SPEC")
(IN-PACKAGE "CHAR-SPEC")

(defvar SpecToLisp::SuppressGeneratedDefs nil) ;; note: defvar does not redefine if var already has a value

(setq SpecToLisp::SuppressGeneratedDefs
      (append '("CHAR-SPEC::ord" 
		"CHAR-SPEC::chr" 
		"CHAR-SPEC::isUpperCase"
		"CHAR-SPEC::isLowerCase"
		"CHAR-SPEC::isAlpha"
		"CHAR-SPEC::isNum"
		"CHAR-SPEC::isAlphaNum"
		"CHAR-SPEC::isAscii"
		"CHAR-SPEC::toUpperCase"
		"CHAR-SPEC::toLowerCase")
	      SpecToLisp::SuppressGeneratedDefs))

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

;;; lower-case-p, upper-case-p etc. only guaranteed for Standard ASCII (First 96 characters)
(defun isUpperCase (char)
  (declare (character char))
  (let ((ch-num (char-code char)))
    (or (< 64 ch-num 91)		; A-Z
	(< 191 ch-num 215)		; À-Ö
	(< 215 ch-num 224)		; Ø-ß
	)))

(defun isLowerCase (char)
  (declare (character char))
  (let ((ch-num (char-code char)))
    (or (< 96 ch-num 123)		; a-z
	(< 223 ch-num 247)		; à-à
	(< 247 ch-num 256)		; ø-ÿ
	)))

(defun isAlpha (ch)
  (or (isUpperCase ch)
      (isLowerCase ch)))

(defun isNum (ch)
  (and (<= 48 (char-code ch)) (<= (char-code ch) 57)))

(defun isAlphaNum (ch)
  (or (isAlpha ch)
      (isNum ch)))

(defun isAscii (char)
  (declare (character char))
  (< -1
     (char-code char)
     256))

;;; Relationship between ÿ and ß is anomalous
(defun toUpperCase (char)
  (declare (character char))
  (if (isLowerCase char)
      (code-char (- (char-code char) 32))
    char))

(defun toLowerCase (char)
  (declare (character char))
  (if (isUpperCase char)
      (code-char (+ (char-code char) 32))
    char))
