(defpackage "PARSER4")
(defpackage "UNICODE")
(defpackage "IO-SPEC")
(in-package "IO-SPEC")

;;;  sort Filename = String
;;;  sort Time     = Nat          % Not a fixnum
;;;  sort Byte     = {x : Nat | 0 <= x &  x < 256} 
;;;
;;;  op getCurrentDirectory   : () -> Filename
;;;  op fileExistsAndReadable : Filename -> Boolean
;;;  op fileWriteTime         : Filename -> Time
;;;
;;;  op fileWritable          : Filename -> Boolean
;;;  op readBytesFromFile     : Filename -> List Byte
;;;  op writeBytesToFile      : List Byte * Filename -> ()
;;;


;;; This returns true if, as the name suggests, the given file
;;; exists and is readable. Otherwise, it returns false.
(defun fileExistsAndReadable (x)
  (handler-case
      (progn (close (open x :direction :input)) t)
    (file-error (condition) 
      (declare (ignore condition))
      nil)
    #+gcl
    (error (condition) 
      (declare (ignore condition))
      nil)))

(defvar nullFileWriteTime 9999999999999)   ; eons from now: "Thu May 21 10:46:39 PST 318787"

(defun fileWriteTime (file)
  ;; bignum (i.e., not a lisp fixnum, not a C int)
  ;; Bigger than 536870911 = 2^29 - 1 = most-positive-fixnum
  ;; Bigger than 2147483648 = 2^31 = biggest 32-bit int 
  (or #+allegro(excl::filesys-write-date file)    ; faster?
      ;;
      ;; The allegro hack above returns nil for names such as "~/foo.sw"
      ;; The following should succeed where the above hack returns nil, 
      ;; but maybe this is all that the standard file-write-date does:
      ;;  (excl::filesys-write-date (namestring (truename  file))) 
      ;;
      ;; Call this when hack fails (or we're not running Allego CL) ...
      (file-write-date file)
      ;; If file doesn't exist then return a future time! 
      ;; 3288592472 = "Thu Mar 18 01:54:32 PST 2004"
      nullFileWriteTime))

(defun currentTime-0 ()
  ;; bignum (i.e., not a lisp fixnum, not a C int)
  ;; Bigger than 536870911 = 2^29 - 1 = most-positive-fixnum
  ;; Bigger than 2147483648 = 2^31 = biggest 32-bit int 
  (get-universal-time))

(defun getCurrentDirectory-0 ()
  (convert-windows-filename (namestring (specware::current-directory))))

(defun convert-windows-filename (filestr)
  (declare (simple-string filestr))
  (let ((strip-c-colon-nm
	 (if (string-equal "c:" (subseq filestr 0 2))  ; Ignore case of c in =
	     (subseq filestr 2 (length filestr))
	   filestr)))
    (substitute #\/ #\\ strip-c-colon-nm)))

;;;  (defun fileExists (x)
;;;    (probe-file x))
;;;  
;;;  (defun openFile (name mode)
;;;    (handler-case
;;;      (cons :|Ok| (open name))
;;;  ;;    (ecase mode
;;;  ;;      (:|Read| )
;;;  ;;      (:|Write| )
;;;  ;;      (:|Append| )
;;;  ;;      (:|ReadWrite| )
;;;  ;;    ) 
;;;    (file-error (condition)
;;;      (let* ((errno
;;;               (if (null (excl::file-error-errno condition))
;;;                  (list :|None|)
;;;                  (cons :|Some| (excl::file-error-errno condition)))))
;;;      (cons :|FileError|
;;;         (vector errno
;;;         (format nil "~A" (file-error-pathname condition))
;;;         (format nil "~A" condition)))))))

(defun readStringFromFile (filename)
  #+allegro(excl::file-contents filename)
  #-allegro nil)			; Fix!!!

(defun readBytesFromFile (filename)
  (let ((eof (cons nil nil))
	(chars nil))
    (if (probe-file filename)
	(with-open-file (s filename :element-type 'unsigned-byte)
	  (do ((char (read-byte s nil eof) 
		     (read-byte s nil eof)))
	      ((eq char eof)
	       (cons :|Some| (reverse chars)))
	    (push char chars)))
      '(:|None|))))

(defun writeBytesToFile-2 (bytes filename)
  (with-open-file (s filename :element-type 'unsigned-byte
		   :direction :output
		   :if-exists :supersede)
    (dolist (byte bytes)
      (write-byte byte s))))

;;; From UnicodeSig.sw :
;;;
;;;  sort Encoding = UChars -> Bytes   % UTF-8, UTF-16, JIS, etc.
;;;  sort Decoding = Bytes  -> UChars  % UTF-8, UTF-16, JIS, etc.
;;;
;;;  op read_unicode_chars_from_file : Filename * Encoding -> Option UChars
;;;  op write_unicode_chars_to_file  : UChars * Filename * Encoding -> ()

(defun unicode::read_unicode_chars_from_file-2 (filename decoding)
  (let ((bytes (readBytesFromFile filename)))
    (case (car bytes)
      (:|None| '(:|None|))
      (:|Some| (cons :|Some|
		     (let ((uchars (funcall decoding (cdr bytes))))
		       uchars))))))

(defun unicode::write_unicode_chars_to_file-3 (uchars filename encoding)
  (let ((bytes (funcall encoding uchars)))
    (writeBytesToFile-2 bytes filename)))

;; Used by prover interface:
;; Hopefully not Allegro specific.
(defun parser4::read_list_of_s_expressions_from_string (string)
  (let ((done? nil)
	(whitespaces '(#\space #\tab #\newline)))
    (let* ((trimmed-string (string-trim whitespaces string))
	   (index 0)
	   (result 
	    (catch 'problem
	      (prog1
		  (handler-bind ((error #'(lambda (signal) 
					    (throw 'problem (list signal index)))))
		    (let ((sexp nil)
			  (s-expressions ())
			  (n (length trimmed-string)))
		      (loop
			(multiple-value-setq (sexp index)
			  ;; bug in Allegro?  
			  ;; Setting eof-error-p to nil won't
			  ;; suppress eof error unless there is no 
			  ;; text at all to parse.
			  ;; At any rate, other kinds of errors are
			  ;; also possible.
			  (let ((*package* (find-package 'snark)))
			    (read-from-string trimmed-string nil nil 
					      :start               index 
					      :preserve-whitespace t)))
			(push sexp s-expressions)
			(when (>= index n)
			  (return (reverse s-expressions))))))
		;; if there were no problems, done? will become true,
		;; but we will return the value from the handler-bind 
		;; above from the prog1
		(setq done? t)))))
      (if done?
	  (cons :|OptionString| result)
	;; cause parser error?
	(let ((signal (first result))
	      (index  (second result)))
	  (let ((error-msg 
		 (format nil "~A at position ~D" 
			 (if (eq (type-of signal) 'common-lisp::end-of-file)
			     "Premature EOF for expression starting"
			   signal)
			 index)))
	    (cons :|Error| (cons error-msg string))))))))

;; translate invalid file name characters to valid ones
(defun convertToFileName(str)
  (let* ((chars (STRING-SPEC::explode str))
	 (translated-char-strings 
	  (mapcar #'(lambda (ch) 
		      (case ch
			(#\? "_p")
			((#\\ #\/ #\: #\* #\" #\< #\> #\|)
			 (format nil "_x~a" (char-code ch)))
			(t (string ch))))
		  chars)))
    (declare (type list translated-char-strings))
    (the cl:simple-base-string 
      (apply #'concatenate 'string translated-char-strings))))
