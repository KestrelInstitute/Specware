;;; -*- Mode: LISP; Package: Parser; Base: 10; Syntax: Common-Lisp -*-

(in-package "PARSER4")

(defun COMMENT-BLANK-LINES (&optional (n 1))
  ;; No ";;;" prefix, just a blank line...
  (format t "~&~V%" n))

(defun COMMENT (format-string &rest format-args)
  (let* ((str (apply #'format nil format-string format-args))
	 (old-i 0)
	 (n (length str)))
    (dotimes (i n)
      (let ((char (schar str i)))
	(when (eq char #\newline)
	  (one-line-comment (subseq str old-i i))
	  (setq old-i (1+ i)))))
    (when (< old-i n)
      (one-line-comment (subseq str old-i n)))))

(defun ONE-LINE-COMMENT (str)
  ;;  main comment routine uses this for each line to be output
  (format t "~&;;; ~A~&" str)
  (force-output t))

(defun trim-whitespace (str)
  (string-trim '(#\space #\tab #\newline #\page) str))
