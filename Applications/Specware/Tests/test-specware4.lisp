(in-package :cl-user)

(defun test-specware4 (&optional (log-file-name
				  (multiple-value-bind (ss mm hh dd mo yy)
				      (decode-universal-time (get-universal-time))
				    (format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
					    yy mo dd hh mm ss))))
  (format t "~&Testing Specware4, results to ~A ...~%" log-file-name)
  (with-open-file (s log-file-name :direction :output) 
    (let ((*standard-output* s)
	  (*error-output* s)
	  (test-dir (format nil "~A/TestSuite/" (Specware::getenv "SPECWARE4"))))
      (specware-test::run-test-directories-rec-fn (list test-dir))))
  (format t "~&Done.~%")
  log-file-name)


(defun test-specware4-subdir (subdir
			      &optional (log-file-name
					 (multiple-value-bind (ss mm hh dd mo yy)
					     (decode-universal-time (get-universal-time))
					   (format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
						   yy mo dd hh mm ss))))
  (format t "~&Testing Specware4, results to ~A ...~%" log-file-name)
  (with-open-file (s log-file-name :direction :output) 
    (let ((*standard-output* s)
	  (*error-output* s)
	  (test-dir (format nil "~A/TestSuite/~A/" (Specware::getenv "SPECWARE4") subdir)))
      (specware-test::run-test-directories-rec-fn (list test-dir))))
  (format t "~&Done.~%")
  log-file-name)

(defun test-specware4-bugs (&optional (log-file-name
				       (multiple-value-bind (ss mm hh dd mo yy)
					   (decode-universal-time (get-universal-time))
					 (format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
						 yy mo dd hh mm ss))))
  (test-specware4-subdir "Bugs" log-file-name))


(defun test-specware4-bug (bug-number
			   &optional (log-file-name
				      (multiple-value-bind (ss mm hh dd mo yy)
					  (decode-universal-time (get-universal-time))
					(format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
						yy mo dd hh mm ss))))
  (let ((subdir (format nil "Bugs/Bug_~4,'0D" bug-number)))
    ;; CEM: Don't wire in HOME dir --- use SPECWARE4 environment variable
    (let ((dir-to-check (format nil "~A/TestSuite/~A/" (Specware::getenv "SPECWARE4") subdir)))
      (if (probe-file dir-to-check)
          (test-specware4-subdir subdir log-file-name)
          (with-open-file (s log-file-name :direction :output)
            (format s "No test number ~D in directory ~S~%" bug-number dir-to-check))))))
