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
      nil)))

(defun fileWriteTime (file)
  (or #+allegro(excl::filesys-write-date file)    ; faster?
      ;;
      ;; The allegro hack above returns nil for names such as "~/foo.sw"
      ;; The following should succeed where the above hack returns nil, 
      ;; but maybe this is all that the standard file-write-date does:
      ;;  (excl::filesys-write-date (namestring (truename  file))) 
      ;;
      ;; Call this when hack fails...
      (file-write-date file)
      ;; If file doesn't exist then return a future time! (shouldn't normally happen)
      9999999999))

(defun getCurrentDirectory ()
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

(defun writeBytesToFile (bytes filename)
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
;;;  op read_unicode_chars_from_file : Filename * Encoding -> UChars
;;;  op write_unicode_chars_to_file  : UChars * Filename * Encoding -> ()

(defun unicode::read_unicode_chars_from_file (filename decoding)
  (let ((bytes (readBytesFromFile filename)))
    (let ((uchars (funcall decoding bytes)))
      uchar)))

(defun unicode::write_unicode_chars_to_file (uchars filename encoding)
  (let ((bytes (funcall encoding uchars)))
    (writeBytesToFile bytes filename)))
