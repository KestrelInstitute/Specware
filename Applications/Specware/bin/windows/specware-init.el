;; This is called to start Specware. It is invoked by a command-line
;; argument to Xemacs. This spawns a Lisp process.
(defun run-specware (&optional in-current-dir?)
  (interactive "P")
  (let* ((root-dir (if in-current-dir?
		       (strip-final-slash (if (stringp in-current-dir?)
					      in-current-dir?
					    default-directory))
		     (concat (getenv "SPECWARE4"))))
	 (bin-dir (concat root-dir
			  "/Applications/Specware/bin/"
			  (if *windows-system-p*
			      "windows"
			    (symbol-name system-type))))
	 (world-name (concat bin-dir "/Specware4.dxl")))

    (setq sw:common-lisp-host "localhost")
    (setq-default sw::lisp-host sw:common-lisp-host)
    ;;
    ;; sw:common-lisp-directory is the directory in which the lisp subprocess will
    ;; be executed. It is defined in eli/fi-subproc.el with a default value nil
    ;; This seems to work fine under Unix/Linux but under Windows there is 
    ;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.
    ;;
    (setq sw:common-lisp-directory (concat root-dir "/"))
    ;;
    ;; Specware can be started in two ways. The familiar way is to start the
    ;; Lisp environment augmented with a Specware image. The term "image" comes
    ;; from the Franz manual. At Kestrel, an image is called a "world". The other
    ;; way is to create a new executable application using the ACL primitive
    ;; generate-application. By executable we mean a .exe in the Windows world.
    ;; The latter requires the Enterprise Edition of ACL. It has the advantage that
    ;; we can ship Specware to users who do not already have ACL installed.
    ;;
    ;; Below we set a parameter sw:common-lisp-image-name. Just to confuse things
    ;; further, this is the name used by eli/fi-subproc.el for the Lisp
    ;; executable (and not an image in the ACL sense). The image file
    ;; (in the ACL sense) or world, is bound to common-lisp-image-file
    ;; If the executable is produced by generate-application, then typically,
    ;; there will not be an ACL image file.
    ;;
    (setq sw:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
    ;;
    ;; A "HEAP_IMAGE" is what Franz calls an image and what Kestrel calls a world.
    ;; The suffix on such files is .dxl.
    ;;
    (setq sw:common-lisp-image-file (getenv "LISP_HEAP_IMAGE"))
    (unless (and sw:common-lisp-image-file (not in-current-dir?))
      (setq sw:common-lisp-image-file world-name))
    (setq sw:common-lisp-image-arguments
      (if *windows-system-p* '("+cn") nil))

    (let ((log-warning-minimum-level 'error))
      ;; Don't show spurious warning message
      (sw:common-lisp sw:common-lisp-buffer-name
		      sw:common-lisp-directory
		      sw:common-lisp-image-name
		      sw:common-lisp-image-arguments
		      sw:common-lisp-host
		      sw:common-lisp-image-file
		      ))
    (goto-char (point-max))
    ))

(defun build-specware ()
  (interactive "P")
  (let* ((root-dir (getenv "SPECWARE4"))
	 (dir (concat root-dir "/Applications/Specware/Handwritten/Lisp"))
	 (bin-dir (concat root-dir
			     "/Applications/Specware/bin/"
			     (if *windows-system-p*
				 "windows"
			       (symbol-name system-type))))
	 (slash-dir (sw::normalize-filename "/"))
	 (world-name (concat bin-dir "/Specware4.dxl")))
    (run-plain-lisp)
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SWPATH\") %S)"
			     (concat (sw::normalize-filename root-dir)
				     (if *windows-system-p* ";" ":")
				     slash-dir)))
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SPECWARE4\") %S)"
			     (sw::normalize-filename root-dir)))
    
    (sw:eval-in-lisp (format "(top-level::do-command :cd %S)" dir))
    (sw:eval-in-lisp "(load \"Specware4.lisp\")")

    (run-plain-lisp)
    (unless (inferior-lisp-running-p)
      (sleep-for 1))
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SWPATH\") %S)"
			     (concat (sw::normalize-filename root-dir)
				     (if *windows-system-p* ";" ":")
				     slash-dir)))
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SPECWARE4\") %S)" (sw::normalize-filename root-dir)))
    (sw:eval-in-lisp (format "(top-level::do-command :cd %S)" dir))
    (sw:eval-in-lisp "(load \"Specware4.lisp\")")
    (when (file-exists-p world-name)
      (rename-file world-name (concat bin-dir "/Specware4-saved.dxl") t))
    (sleep-for 1)
    (simulate-input-expression (format "(excl::dumplisp :name %S)" world-name))
    ))

(defun bootstrap-specware (in-current-dir?)
  (interactive "P")
  (let ((root-dir (if in-current-dir? (strip-final-slash default-directory)
		    (concat (getenv "SPECWARE4"))))
	(slash-dir "/"))
    (run-specware4 root-dir)
    (sleep-for 2)
    (sw:eval-in-lisp (format "(top-level::do-command :cd %S)" root-dir))
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SWPATH\") %S)"
			     (concat (sw::normalize-filename root-dir)
				     (if *windows-system-p* ";" ":")
				     slash-dir)))
    (sw:eval-in-lisp (format "(setf (sys:getenv \"SPECWARE4\") %S)" (sw::normalize-filename root-dir)))
    (sw:eval-in-lisp "#+allegro(sys::set-stack-cushion 10000000)
                      #-allegro()")
    (sw:eval-in-lisp "(time (CL-USER::sw \"Applications/Specware/Specware4\"))")
    (build-specware root-dir)))


(defun run-specware ()
  (interactive)
  (let* ((root-dir (concat (getenv "SPECWARE4") "/"))
	 (bin-dir (concat root-dir
			  "Applications/Specware/bin/"
			  (if *windows-system-p*
			      "windows"
			    (symbol-name system-type))))
	 (world-name (concat bin-dir "/Specware4.dxl")))

    (setq sw:common-lisp-host "localhost")
    (setq-default sw::lisp-host sw:common-lisp-host)
    (setq sw:common-lisp-directory root-dir)
    (setq sw:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
    (setq sw:common-lisp-image-file world-name)
    (setq sw:common-lisp-image-arguments
      (if *windows-system-p* '("+cn") nil))

    (let ((log-warning-minimum-level 'error))
      (sw:common-lisp sw:common-lisp-buffer-name
		      sw:common-lisp-directory
		      sw:common-lisp-image-name
		      sw:common-lisp-image-arguments
		      sw:common-lisp-host
		      sw:common-lisp-image-file
		      ))
    ))
