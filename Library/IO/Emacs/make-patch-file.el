(require 'compare-w)

(defvar *copy-new-defs-without-asking* t)

(defun sw:make-patch-file (file)
  (interactive "FPatch file name: ")
  (save-excursion
    (let ((dont-ask (null current-prefix-arg))
	  (new-buffer (current-buffer))
	  (new-window (selected-window))
	  (old-window (next-window (selected-window))))
      (with-current-buffer new-buffer
	(when (eq old-window (selected-window))
	  (error "No other window"))
	(let ((old-buffer (window-buffer old-window))
	      (patch-file-buffer (find-file-noselect file)))
	  (goto-char (point-min) new-buffer)
	  (goto-char (point-max patch-file-buffer) patch-file-buffer)
	  ;; Add in-package form to buffer. May not be correct of more than one in file.
	  (save-excursion
	    (if (search-forward "(in-package " nil t nil new-buffer)
		(with-current-buffer patch-file-buffer
		  (goto-char (match-beginning 0) new-buffer)
		  (insert-buffer-substring new-buffer (point new-buffer)
					   (with-current-buffer new-buffer
					     (beginning-of-defun -1) (point new-buffer))))
	      (with-current-buffer patch-file-buffer
		(insert "(in-package \"SW-USER\")\n\n"))))
	  (with-current-buffer old-buffer
	    (goto-char (point-min) old-buffer))
	  (while (not (eq (point new-buffer) (point-max new-buffer)))
	    (sw:compare-buffers-1 new-buffer old-buffer)
	    (unless (eq (point new-buffer) (point-max new-buffer))
	      (with-current-buffer new-buffer
		(forward-char)
		(beginning-of-defun)
		(forward-char -1))
	      (with-current-buffer old-buffer
		(beginning-of-defun)
		(forward-char -1))
	      (if (equal 0 (compare-buffer-substrings new-buffer (point new-buffer)
						      (sw:forward-def-header)
						      old-buffer (point old-buffer)
						      (with-current-buffer old-buffer
							(sw:forward-def-header))))
		  ;; Definition changed. Copy new one and continue after definition
		  (progn (with-current-buffer new-buffer
			   (forward-char))
			 (sw:copy-to-patch-buffer new-buffer patch-file-buffer
						  (point new-buffer) (progn (beginning-of-defun -1) (point))
						  new-window old-window (point old-buffer) dont-ask)
			 (with-current-buffer old-buffer
			   (beginning-of-defun -1)))
		(progn
		  (with-current-buffer new-buffer
		    (forward-char))
		  (with-current-buffer old-buffer
		    (while (and (not (eq (point new-buffer) (point-max new-buffer)))
				(looking-at "(" new-buffer)
				(not (save-excursion
				       (goto-char (point-min) old-buffer)
				       (and (search-forward (sw:get-definition-ident-str new-buffer) nil t)))))
		      (with-current-buffer new-buffer
			(sw:copy-to-patch-buffer new-buffer patch-file-buffer
						 (point) (progn (beginning-of-defun -1) (point))
						 new-window old-window (point old-buffer)
						 (or *copy-new-defs-without-asking* dont-ask))))
		    ;; Start again at matching definition in old buffer
		    (unless (eq (point new-buffer) (point-max new-buffer))
		      (goto-char (point-min) old-buffer)
		      (search-forward (sw:get-definition-ident-str new-buffer) nil t)
		      (beginning-of-defun)))))))
	  (switch-to-buffer patch-file-buffer))))))

(defun sw:forward-def-header ()
  (save-excursion (forward-char 2)
		  (forward-sexp 2)
		  (forward-char)
		  (point)))

(defun sw:copy-to-patch-buffer (source-buffer target-buffer beg end w1 w2 pos2 dont-ask)
  (save-excursion
    (set-window-point w1 beg)
    (set-window-point w2 pos2)
    (when (or dont-ask (y-or-n-p "Add def to patch? "))
      (with-current-buffer target-buffer
	(insert-buffer-substring source-buffer beg end)))))

(defun sw:get-definition-ident-str (buffer)
  (with-current-buffer buffer
    (save-excursion
      (forward-char -1)
      (when (not (looking-at "\n("))
	(error "Looking at" (point)))
      (buffer-substring (point)
			(sw:forward-def-header)))))

  
;;; Adapted from compare-w
(defun sw:compare-buffers-1 (b1 b2)
  (let* ((p1 (point b1)) (p2 (point b2))
	 (opoint1 p1)    (opoint2 p2)
	 maxp1 maxp2 success)
    (setq maxp1 (point-max b1))
    (push-mark p2 t nil b2)
    (setq maxp2 (point-max b2))
    (push-mark p1 nil nil b1)

    (setq success t)
    (while success
      (setq success nil)
      ;; if interrupted, show how far we've gotten
      (goto-char p1)
      (goto-char p2 b2)

      ;; If both buffers have whitespace next to point,
      ;; skip over it.

      (save-excursion
	(let (p1a p2a)
	  (setq result1 (compare-windows-skip-whitespace opoint1))
	  (setq p1a (point))
	  (goto-char p2 b2)
	  (setq result2 (with-current-buffer b2 (compare-windows-skip-whitespace opoint2)))
	  (setq p2a (point b2))
	  (setq p1 p1a
		p2 p2a)))

      ;; Try advancing comparing 1000 chars at a time.
      ;; When that fails, go 500 chars at a time, and so on.
      (let ((size 1000)
	    success-1
	    (case-fold-search t))
	(while (> size 0)
	  (setq success-1 t)
	  ;; Try comparing SIZE chars at a time, repeatedly, till that fails.
	  (while success-1
	    (setq size (min size (- maxp1 p1) (- maxp2 p2)))
	    (setq success-1
		  (and (> size 0)
		       (= 0 (compare-buffer-substrings b2 p2 (+ size p2)
						       b1 p1 (+ size p1)))))
	    (if success-1
		(setq p1 (+ p1 size) p2 (+ p2 size)
		      success t)))
	  ;; If SIZE chars don't match, try fewer.
	  (setq size (/ size 2)))))

    (goto-char p1 b1)
    (with-current-buffer b2 (goto-char p2 b2))
    (= (point b1) opoint1)))
