(in-package "USER")

(defun show-dirs (file &optional (max-level 4) (prefix ""))
  (let ((trim (length (namestring file)))
	(lines  '()))
    (format t "~&~A~A~%" prefix file)
    (format t "~&~A~A~%" prefix (make-string trim :initial-element #\-))
    (labels ((blank-common-chars (file old)
	       (let* ((old (coerce (namestring old) 'list))
		      (original-chars (coerce (namestring file) 'list))
		      (suffix original-chars))
		 (do ((chars original-chars (cdr chars)))
		     ((not (eq (first chars) (pop old)))
		      (format nil "~,V@T~A" 
			      (1+ (- (length original-chars) (length suffix)))
			      (coerce suffix 'string)))
		   (when (member (car chars) '(#\/ #\\))
		     (setq suffix (cdr chars))))))
	     (list-files (file level)
	       (if (file-directory-p file)
		   (let* ((foo (namestring file))
			  (sub-files (directory 
				      (if (member (schar foo (1- (length foo))) '(#\/ #\\))
					  file
					(format nil "~A/" foo)))))
		     (if (< level max-level)
			 (let ((level (1+ level)))
			   (dolist (file sub-files) 
			     (list-files file level)))
		       (push (list (subseq (format nil "~A/" file) trim)
				   (length sub-files))
			     lines)))
		 (push (list (subseq (namestring file) trim))
		       lines))))
      (list-files file 0)
      (let ((right-tab 0)
	    (previous-file ""))
	(dolist (pair (reverse lines))
	  (unless (null (second pair))
	    (setq right-tab (max right-tab (length (first pair))))))
	(setq right-tab (+ right-tab 3 (length prefix)))
	(dolist (pair (reverse lines))
	  (let* ((file  (first  pair))
		 (revised-name (blank-common-chars file previous-file))
		 (count (second pair)))
	    (cond ((null count)
		   (format t "~&~A~A~%" prefix revised-name))
		  (t
		   (format t "~&~A~A ~,V@T [~2D files]~%" 
			   prefix revised-name right-tab count)))
	    (setq previous-file file)))))))
