
;; This is called to start Specware. It is invoked by a command-line
;; argument to Xemacs. This spawns a Lisp process.
(defun run-specware4 ()
  (interactive)
  (setq fi:common-lisp-host "localhost")
  (setq-default fi::lisp-host fi:common-lisp-host)
;;
;; fi:common-lisp-directory is the directory in which the lisp subprocess will
;; be executed. It is defined in eli/fi-subproc.el with a default value nil
;; This seems to work fine under Unix/Linux but under Windows there is 
;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.
;;
  (setq fi:common-lisp-directory (or (getenv "LISP_DIRECTORY")
				     (getenv "SPECWARE4")))
;;
;; Specware can be started in two ways. The familiar way is to start the
;; Lisp environment augmented with a Specware image. The term "image" comes
;; from the Franz manual. At Kestrel, an image is called a "world". The other
;; way is to create a new executable application using the ACL primitive
;; generate-application. By executable we mean a .exe in the Windows world.
;; The latter requires the Enterprise Edition of ACL. It has the advantage that
;; we can ship Specware to users who do not already have ACL installed.
;;
;; Below we set a parameter fi:common-lisp-image-name. Just to confuse things
;; further, this is the name used by eli/fi-subproc.el for the Lisp
;; executable (and not an image in the ACL sense). The image file
;; (in the ACL sense) or world, is bound to common-lisp-image-file
;; If the executable is produced by generate-application, then typically,
;; there will not be an ACL image file.
;;
  (setq fi:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
;;
;; A "HEAP_IMAGE" is what Franz calls an image and what Kestrel calls a world.
;; The suffix on such files is .dxl.
;;
  (setq fi:common-lisp-image-file
    (concat (getenv "SPECWARE4")
	    "/Applications/Specware/bin/"
	    ; This could be elaborated
	    (if (memq system-type '(ms-dos windows-nt windows-95
				    ms-windows))
		"windows"
	      (symbol-name system-type))
	    "/Specware4.dxl"))
  (setq fi:common-lisp-image-arguments nil ;'("+c")
	)

  (fi:common-lisp fi:common-lisp-buffer-name
		  fi:common-lisp-directory
		  fi:common-lisp-image-name
		  fi:common-lisp-image-arguments
		  fi:common-lisp-host
		  fi:common-lisp-image-file
		  )
  (sleep-for 2)
;;;  (while (not (inferior-lisp-running-p))
;;;    (sleep-for 1))
;;;  (delete-windows-on "*Warnings*" t)
  )

;;;(defun run-specware (&optional openSpecWindow)
;;;  (interactive "P")
;;;  (setq fi:common-lisp-host "localhost")
;;;;;
;;;;; fi:common-lisp-directory is the directory in which the lisp subprocess will
;;;;; be executed. It is defined in eli/fi-subproc.el with a default value nil
;;;;; This seems to work fine under Unix/Linux but under Windows there is 
;;;;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.
;;;;;
;;;  (setq fi:common-lisp-directory (getenv "LISP_DIRECTORY"))
;;;;;
;;;;; Specware can be started in two ways. The familiar way is to start the
;;;;; Lisp environment augmented with a Specware image. The term "image" comes
;;;;; from the Franz manual. At Kestrel, an image is called a "world". The other
;;;;; way is to create a new executable application using the ACL primitive
;;;;; generate-application. By executable we mean a .exe in the Windows world.
;;;;; The latter requires the Enterprise Edition of ACL. It has the advantage that
;;;;; we can ship Specware to users who do not already have ACL installed.
;;;;;
;;;;; Below we set a parameter fi:common-lisp-image-name. Just to confuse things
;;;;; further, this is the name used by eli/fi-subproc.el for the Lisp
;;;;; executable (and not an image in the ACL sense). The image file
;;;;; (in the ACL sense) or world, is bound to common-lisp-image-file
;;;;; If the executable is produced by generate-application, then typically,
;;;;; there will not be an ACL image file.
;;;;;
;;;  (setq fi:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
;;;;;
;;;;; A "HEAP_IMAGE" is what Franz calls an image and what Kestrel calls a world.
;;;;; The suffix on such files is .dxl.
;;;;;
;;;  (setq fi:common-lisp-image-file (getenv "LISP_HEAP_IMAGE"))
;;;
;;;  (fi:common-lisp fi:common-lisp-buffer-name
;;;		  fi:common-lisp-directory
;;;		  fi:common-lisp-image-name
;;;		  fi:common-lisp-image-arguments
;;;		  fi:common-lisp-host
;;;		  fi:common-lisp-image-file
;;;		  ) 
;;; 
;;;;; Works only in an image where specware2000 resides.
;;;  (when openSpecWindow
;;;    (sw:eval-in-lisp "(progn (SpecwareUI::openSpecWindow) \"Done\")")))

;; The following is almost the same as the above. The difference is that
;; in the following we execute a Specware application (rather than run Lisp
;; with a Specware world);

(defun run-lisp-application ()
  (interactive)
  (when (inferior-lisp-running-p)
    (fi:exit-lisp)
    (sleep-for 2))
  (setq fi:common-lisp-host "localhost")
;;
;; fi:common-lisp-directory is the directory in which the lisp subprocess will
;; be executed. It is defined in eli/fi-subproc.el with a default value nil
;; This seems to work fine under Unix/Linux but under Windows there is 
;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.
;;
  (setq fi:common-lisp-directory (getenv "LISP_DIRECTORY"))

;; Below we set a parameter fi:common-lisp-image-name. This is the name 
;; used by eli/fi-subproc.el for the Lisp executable. This is the application
;; we want to run.  The image file (in the ACL sense) or world, is bound 
;; to common-lisp-image-file. If the executable is produced by
;; generate-application, then typically, there will not be an ACL image file.

  (setq fi:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
  (setq fi:common-lisp-image-file nil)
  (setq fi:common-lisp-image-arguments nil) ; '("+c"))

  (fi:common-lisp fi:common-lisp-buffer-name
		  fi:common-lisp-directory
		  fi:common-lisp-image-name)
  (sleep-for 1))

;; (simulate-input-expression "t")
(defun simulate-input-expression (str)
  (let ((win (get-buffer-window *specware-buffer-name*)))
    (if win (select-window win)
      (switch-to-lisp)))
  (goto-char (point-max))
  (insert str)
  (inferior-lisp-newline))

(defun build-specware4 (in-current-dir?)
  (interactive "P")
  (let* ((root-dir (if in-current-dir? default-directory
		     (getenv "SPECWARE4")))
	 (dir (concat root-dir "/Applications/Specware/Handwritten/Lisp"))
	 (bin-dir (concat root-dir
			     "/Applications/Specware/bin/"
			     (if (memq system-type '(ms-dos windows-nt windows-95
						     ms-windows))
				 "windows"
			       (symbol-name system-type))))
	 (world-name (concat bin-dir "/Specware4.dxl")))
    (run-lisp-application)
    (sw:eval-in-lisp (format "(top-level::do-command :cd %S)" dir))
    (sw:eval-in-lisp "(load \"Specware4.lisp\")")
    (run-lisp-application)
    (unless (inferior-lisp-running-p)
      (sleep-for 1))
    (sw:eval-in-lisp (format "(top-level::do-command :cd %S)" dir))
    (sw:eval-in-lisp "(load \"Specware4.lisp\")")
    (when (file-exists-p world-name)
      (rename-file world-name (concat bin-dir "/Specware4-saved.dxl") t))
    (sleep-for 1)
    (simulate-input-expression (format "(excl::dumplisp :name %S)" world-name))
;;;    (simulate-input-expression
;;;     "(if (probe-file \"bin/specware2000-new.world\")
;;;	  (progn (when (probe-file \"bin/specware2000.world\")
;;;                   (rename-file  \"bin/specware2000.world\" \"bin/specware2000-old.world\"))
;;;		 (rename-file  \"bin/specware2000-new.world\" \"bin/specware2000.world\")
;;;		 \"Wrote a new bin/specware2000.world\")
;;;	\"Failed to build a new world!\")")
    ))

(defun bootstrap-specware4 (in-current-dir?)
  (interactive "P")
  (run-specware4)
  (sleep-for 2)
  (let ((root-dir (if in-current-dir? default-directory
		    (getenv "SPECWARE4"))))
    (sw:eval-in-lisp (format "(top-level::do-command :swpath %S)" root-dir))
    (sw:eval-in-lisp "(user::boot)")
    (build-specware4 in-current-dir?)))

(defun test-specware-bootstrap (in-current-dir?)
  (interactive "P")
  (let ((current-dir default-directory))
    (if (not (inferior-lisp-running-p))
	(message "Do M-x bootstrap-specware first")
      (progn (shell-command (concatenate 'string "cd "
					 (if in-current-dir? current-dir
					   *specware-home-directory*)
					 "; /bin/rm */sig/*.sig"))
	     (sleep-for 4)		; Necessary? Enough?
	     (simulate-input-expression "(Bootstrap-Spec::compileBootstrap)")
	     (simulate-input-expression ":exit")
	     (sleep-for 5)
	     (while (inferior-lisp-running-p`)
	       (sleep-for 2))
	     (run-lisp-application)
	     (simulate-input-expression "(load \"load.lisp\")")
	     (simulate-input-expression "(Bootstrap-Spec::compileAll)")))))
