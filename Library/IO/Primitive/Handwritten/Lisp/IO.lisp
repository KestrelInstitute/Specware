(defpackage "IO-SPEC")
(in-package "IO-SPEC")

;; The Lisp getenv returns nil if the name is not in the environment. 
;; Otherwise it returns a string. We want to be able to distinguish
;; the outcomes in MetaSlang
(defun getEnv (name)
  (let ((val (system:getenv name)))
    (if (or (eq val nil) (equal val ""))    ; I think it returns "" if not set
	(cons :|None| nil)
      (cons :|Some| val))))

;; This returns true if, as the name suggests, the given file
;; exists and is readable. Otherwise, it return false.
(defun fileExistsAndReadable (x)
  (handler-case
      (close (open x :direction :input))
    (file-error (condition) 
      (declare (ignore condition))
      nil)))

(defun fileWriteTime (file)
  (or #+allegro(excl::filesys-write-date file)    ; faster
      #-allegro(file-write-date file)
      ;; If file doesn't exist then return a future time! (shouldn't normally happen)
      9999999999))

(defun getCurrentDirectory ()
  (convert-windows-filename (namestring (sys::current-directory))))

(defun convert-windows-filename (filestr)
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
