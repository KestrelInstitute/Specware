(in-package "USER")

(defun test-specware4 (&optional (log-file-name
				  (multiple-value-bind (ss mm hh dd mm yy)
				      (decode-universal-time (get-universal-time))
				    (format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
					    yy mm dd hh mm ss))))
  (format t "~&Testing Specware4, results to ~A ...~%" log-file-name)
  (with-open-file (s log-file-name :direction :output) 
    (let ((*standard-output* s)
	  (*error-output* s)
	  (test-dir (format nil "~A/TestSuite/" (specware::getenv "SPECWARE4"))))
      (specware-test::run-test-directories-rec-fn (list test-dir))))
  (format t "~&Done.~%")
  log-file-name)


(defun test-specware4-bugs (&optional (log-file-name
				       (multiple-value-bind (ss mm hh dd mm yy)
					   (decode-universal-time (get-universal-time))
					 (format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
						 yy mm dd hh mm ss))))
  (format t "~&Testing Specware4, results to ~A ...~%" log-file-name)
  (with-open-file (s log-file-name :direction :output) 
    (let ((*standard-output* s)
	  (*error-output* s)
	  (test-dir (format nil "~A/TestSuite/Bugs/" (specware::getenv "SPECWARE4"))))
      (specware-test::run-test-directories-rec-fn (list test-dir))))
  (format t "~&Done.~%")
  log-file-name)


(defun test-specware4-bug (bug-number
			   &optional (log-file-name
				      (multiple-value-bind (ss mm hh dd mm yy)
					  (decode-universal-time (get-universal-time))
					(format nil "/tmp/test-specware4-~D-~D-~D-~D-~D-~D"
						yy mm dd hh mm ss))))
  (format t "~&Testing Specware4, results to ~A ...~%" log-file-name)
  (with-open-file (s log-file-name :direction :output) 
    (let ((*standard-output* s)
	  (*error-output* s)
	  (test-dir (format nil "~A/TestSuite/Bugs/Bug_~4,'0D" 
			    (specware::getenv "SPECWARE4") 
			    bug-number)))
      (specware-test::run-test-directories-rec-fn (list test-dir))))
  (format t "~&Done.~%")
  log-file-name)


