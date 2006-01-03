
;;; JLM: Mon Jan  2 02:57:26 PST 2006
;;;
;;; Peculiar stuff needed when XEmacs is installed under Windows 
;;; by a user without administrative privileges.
;;;
;;; Without this, when XEmacs starts, load-path will be something like
;;; '("C:\\Xemacs\\XEmacs-21.4.18\\lisp\\")
;;;
;;; That makes it impossible to find various packages (e.g. ring or regexp-opt)
;;; which results in calls to undefined functions (e.g. make-ring).
;;; This code attempts to build a plausible load-path.

;;; This is not needed if XEmacs was installed by a user with
;;; administrative privileges, but (I think) doesn't hurt.

(defun package-subdirs (dir)
  (let ((dirs (list dir)))
    (dolist (pkg (directory-files dir))
      (unless (member pkg '("." ".."))
	(let ((path (format nil "%s%s\\" dir pkg)))
	  (when (paths-file-readable-directory-p path)
	    (setq dirs (cons path dirs))))))
    (reverse dirs)))

(when (eq system-type 'windows-nt)
  (let ((version-subdir (concat "\\XEmacs-" emacs-program-version)))
    ;; e.g. "\\XEmacs-21.4.18"
    (when (equal (length load-path) 1)
      ;; e.g. '("C:\\Xemacs\\XEmacs-21.4.18\\lisp\\")
      ;;      '("C:\\Program Files\Xemacs\\XEmacs-21.4.18\\lisp\\")
      ;;      etc.
      (let ((n (search version-subdir (car load-path))))
	(unless (null n)
	  (let* ((xemacs-dir     (subseq (car load-path) 0 n)) ; "C:\\Xemacs", "C:\\Program Files\\Xemacs". etc.
		 (site-pkg-dir   (concat xemacs-dir "\\Packages\\site-packages\\lisp\\"))
		 (xemacs-pkg-dir (concat xemacs-dir "\\Packages\\xemacs-packages\\lisp\\"))
		 (mule-pkg-dir   (concat xemacs-dir "\\Packages\\mule-packages\\lisp\\")))
	    (dolist (file (append (package-subdirs site-pkg-dir)
				  (package-subdirs xemacs-pkg-dir)
				  (package-subdirs mule-pkg-dir)
				  ))
	      (unless (member file load-path) 
		(setq load-path (append load-path (list file))))
	      )))))

    (let ((xemacs-version-dir (getenv "XEMACS")))
      ;; e.g. "C:\\Xemacs\\XEmacs-21.4.18"
      ;;  or  "C:\\Program Files\\XEmacs\\XEmacs-21.4.18"
      (when (not (null xemacs-version-dir))
	(let* ((n (search version-subdir xemacs-version-dir)))
	  (unless (null n)
	    (let* ((xemacs-dir      (subseq xemacs-version-dir 0 n)) ; "C:\\Xemacs", "C:\\Program Files\\XEmacs", etc.
		   (xemacs-lisp-dir (concat xemacs-version-dir "\\lisp\\"))
		   (mule-pkg-dir    (concat xemacs-dir "\\Packages\\mule-packages\\lisp\\"))
		   (site-pkg-dir    (concat xemacs-dir "\\Packages\\site-packages\\lisp\\"))
		   (xemacs-pkg-dir  (concat xemacs-dir "\\Packages\\xemacs-packages\\lisp\\")))
	      (dolist (file (append (package-subdirs site-pkg-dir)
				    (package-subdirs xemacs-pkg-dir)
				    (package-subdirs mule-pkg-dir)
				    (pacakge-subdirs xemacs-lisp-dir)
				    ))
		(unless (member file load-path) 
		  (setq load-path (append load-path (list file))))
		)))))))

  (require 'ring) 
  (require 'regexp-opt)
  )
