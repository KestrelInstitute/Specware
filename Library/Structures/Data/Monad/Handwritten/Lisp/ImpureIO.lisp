(defpackage "IO-SPEC")
(defpackage "IMPUREIO")
(in-package "IMPUREIO")

;; We want to avoid writing code that depends 
;; on the Lisp representation of Specware terms
;; so we have 4 instances of open

;; May need state in the IO monad to record
;; what streams are open and to close them when one leaves the monad.

(defun openFileRead (name)
   (handler-case (mkOk (open name))
     (file-error (condition) (handle-open-error name condition)))
)

(defun openFileWrite (name)
   (handler-case (mkOk (open name :output :supersede :create))
     (file-error (condition) (handle-open-error name condition)))
)

(defun openFileReadWrite (name)
   (handler-case (mkOk (open name :io :overwrite :create))
     (file-error (condition) (handle-open-error name condition)))
)

(defun openFileAppend (name)
   (handler-case (mkOk (open name :output :append :create))
     (file-error (condition) (handle-open-error name condition)))
)

(defun handle-open-error (name condition)
   (mkFileError
      mkNone
      (format nil "~A" (file-error-pathname condition))
      (format nil "~A" condition))
)

(defun mkOk (x) (cons :|Ok| x))
(defun mkEOF (path) (cons :|EOF| path))
(defun mkFileError (optCond path |!cond|) 
  (cons :|FileError| (vector optCond path |!cond|)))

(defun mkStreamError (strm action code ident) 
  (cons :|StreamError| (vector strm action code ident)))

(defparameter IO-SPEC::stdin *standard-input*)
(defparameter IO-SPEC::stdout *standard-output*)

(defparameter mkNone '(:|None|))
(defun mkSome (x) (cons :|Some| x))

(defun closeFile (strm)
   (mkOk (close strm))
)

(defun readChar (strm)
  (handler-case (mkOk (read-char strm))
    (end-of-file (condition)
      (mkEOF (format nil "~A" (stream-error-stream condition))))
    (stream-error (condition)
      (mkStreamError
        (format nil "~A" (excl::stream-error-stream condition))
        (format nil "~A" (excl::stream-error-action condition))
        (excl::stream-error-code condition)
        (excl::stream-error-identifier condition))))
)

(defun readLine (strm)
   (handler-case (mkOk (read-line strm))
      (end-of-file (condition) (mkEOF (format nil "~A" (stream-error-stream condition)))))
)

(defun readString (strm)
   (handler-case
     (multiple-value-bind (line noNewline) (read-line strm)
       (if noNewline 
         (mkOk line)
         (mkOk (format nil "~A~%" line))))
     (end-of-file (condition) (mkEOF (format nil "~A" (stream-error-stream condition)))))
)


;; The Allegro documentation does not describe any errors associated
;; with writing. Should experiment to see what happens when one
;; writes to a closed stream.
;;
;; Correction. Maybe stream-error.
(defun writeChar-1-1 (strm char)
   (mkOk (write-char char strm))
)

(defun writeLine-1-1 (strm str)
   (mkOk (write-line str strm))
)

(defun writeString-1-1 (strm str)
   ;;(mkOk (write-string str strm))
   (mkOk (format strm "~A" str))
)

(defun flushStream (strm)
   (mkOk (force-output strm))
)

(defun atEOF? (strm)
   (if (eq (peek-char nil strm nil :EOF) :EOF) t nil)
)

