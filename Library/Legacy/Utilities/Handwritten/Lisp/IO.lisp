(defpackage :IO-SPEC) 
(in-package :IO-SPEC)

(defun withOpenFileForRead (name p)
  (with-open-file (s name :direction :input :if-does-not-exist :error)
    (funcall p s)))

(defun withOpenFileForWrite (name p)
  (with-open-file (s name :direction :output :if-exists :new-version)
    (funcall p s)))

(defun withOpenFileForAppend (name p)
  (with-open-file (s name :direction :output :if-exists :append)
    (funcall p s)))

(defun deleteFile (name)
  (delete-file name))

(defun fileExists? (name)
  (not (null (probe-file name))))

;; op readLines : [A] String * (String * A -> A) * A -> A

;; Works like foldL, not foldR.  That is, first we fold in lines from
;; the beginning of the file, not the end.

(defun readLines (name fn val)
    (withOpenFileForRead name
      #'(lambda (s)
          (loop
	    (let ((line (read-line s nil nil)))
	      (if (null line) (return val)
		(setq val (funcall fn (cons line val)))))))))

(defun writeLines (name fn) 
  (withOpenFileForWrite 
   name
   #'(lambda (s) 
       (loop
	(let ((line? (funcall fn ())))
	  (if (eq (car line?) :|None|)
	      (return ())
	    (let ((line (cdr line?)))
	      (write-line line s))))))))


;; op readLines : [A] String * (String * A -> A) * A -> A

;; Works like foldL, not foldR.  That is, first we fold in lines from
;; the beginning of the file, not the end.

(defparameter terminal  t)
(defparameter |!string| nil)

(defun format1 (s control data1)
  (format s control data1))

(defun format2 (s control data1 data2)
  (declare (ignore data2))
  (format s control data1))

(defun format3 (s control data1 data2 data3)
  (format s control data1 data2 data3))

(defun formatTerminal1 (control data1) 
  (format terminal control data1))

(defun formatTerminal2 (control data1 data2) 
  (format terminal control data1 data2))

(defun formatTerminal3 (control data1 data2 data3) 
  (format terminal control data1 data2 data3))

(defun formatString1 (control data1) 
  (format |!string| control data1))

(defun formatString2 (control data1 data2) 
  (format |!string| control data1 data2))

(defun formatString3 (control data1 data2 data3) 
  (format |!string| control data1 data2 data3))

(defun |!read| (s)
  (let ((eof-value 'eof))
    (let ((a (read s nil eof-value)))
      (if (eq a eof-value)
	  (cons :|None| nil)
	(cons :|Some| a)))))

(defun |!write| (s a)
  (prin1 a s))

(defun fileOlder? (f1 f2)
  ;#+allegro(excl::file-older-p f1 f2)
  (let ((d1 (or (file-write-date f1) 0))
	(d2 (or (file-write-date f2) 0)))
    (< d1 d2)))

(defun ensureDirectoriesExist (s)
  (ensure-directories-exist s :verbose t))

(defun writeNat (n)
  (format t "~A" n))

(defun writeChar (c)
  (format t "~A" c))

(defun writeString (s)
  (format t "~A" s))

(defun writeLineNat (n)
  (format t "~A~%" n))

(defun writeLineChar (c)
  (format t "~A~%" c))

(defun writeLineString (s)
  (format t "~A~%" s))

;; (defun FileNameInSpecwareHome (s)
  ;; (declare (special re::*specware-home-directory*))
  ;; (concatenate 'string re::*specware-home-directory* "/" s))

;;; Lisp functions to avoid creating grarbage for indentation strings when prettyprinting
(defpackage "PRETTYPRINT")

(defun make-blanks-array (n)
  (let ((a (make-array n)))
    (loop for i from 1 to n do (setf (svref a (- i 1))
				     (format nil "~v@t" i)))
    a))

(defvar *blanks-array-size* 60)

(defvar *blanks-array* (make-blanks-array *blanks-array-size*))

(defun prettyprint::blanks (n)
  (if (= n 0) ""
    (if (<= n *blanks-array-size*) (svref *blanks-array* (- n 1))
      (format nil "~vT" n))))

(defpackage "EMACS")
(defun gotoFilePosition (file line col)
  (emacs::goto-file-position file line col))

