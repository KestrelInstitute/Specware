(defvar lisp-emacs-interface-type)
(defvar *windows-system-p*)

(defvar *specware-lisp*) ; allegro, cmulisp, openmcl, sbcl, etc.
(defvar *specware-buffer-name*)
(defvar *specware4-dir)
(defvar *specware-home-directory*)

(defvar *lisp-image-extension*)
(defvar *lisp-executable-extension*)
(defvar *fasl-extension*)

(defvar sw:common-lisp-directory)
(defvar sw:common-lisp-image-name)
(defvar sw:common-lisp-image-file)
(defvar sw:common-lisp-image-arguments)
(defvar sw:common-lisp-host)
(defvar sw:common-lisp-buffer-name)
(defvar sw::lisp-host)


;; This is called to start Specware. 
;; It is invoked by a command-line argument to Xemacs, and spawns a Lisp process.

(defun run-specware4 (&optional in-current-dir?)
  (interactive "P")
  (if (inferior-lisp-running-p)
      (sw:switch-to-lisp t)
    (let* ((*specware4-dir (strip-final-slash
			    (sw::normalize-filename ; may rename "Program Files" to "Progra~1" etc.
			     (expand-file-name 
			      (if in-current-dir?
				  (if (stringp in-current-dir?)
				      in-current-dir?
				    default-directory)
				(concat (or (getenv "LISP_DIRECTORY") 
					    (getenv "SPECWARE4"))))))))
	   (bin-dir               (binary-directory *specware4-dir))
	   (default-sw-executable (sw::normalize-filename (expand-file-name (concat bin-dir "/Specware4." *lisp-executable-extension*))))
	   (default-sw-image      (sw::normalize-filename (expand-file-name (concat bin-dir "/Specware4." *lisp-image-extension*)))))

      ;; sw:common-lisp-buffer-name is defined in compat.el

      ;; sw:common-lisp-directory is the directory in which the lisp subprocess will
      ;; be executed. It is defined in eli/fi-subproc.el with a default value nil
      ;; This seems to work fine under Unix/Linux but under Windows there is 
      ;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.

      (setq sw:common-lisp-directory (concat *specware4-dir "/"))

      ;; Specware can be started in two ways. 
      ;;
      ;; One way is to start a generic Lisp augmented with a Specware image. 
      ;; The term "image" comes from Franz Allegro. 
      ;; (At Kestrel, an image is called a "world".)
      ;;
      ;; The other way is to create a new standalone executable application.
      ;;
      ;; ACL uses the primitive generate-application to create standalone applications.
      ;; This requires the Enterprise Edition of ACL, but has the advantage that
      ;; we can ship Specware to users who do not already have ACL installed.
      ;;
      ;; Below we set a parameter sw:common-lisp-image-name. Just to confuse things
      ;; further, this is the name used by eli/fi-subproc.el for the Lisp
      ;; executable (and not an image in the ACL sense). The image file
      ;; (in the ACL sense) or world, is bound to common-lisp-image-file
      ;; If the executable is produced by generate-application, then typically,
      ;; there will not be an ACL image file.
      ;;
      ;; The suffix for image names is .exe, .sbclexe, etc.

      (setq sw:common-lisp-image-name 
	    ;; executable: either generic lisp or standalone specware
	    (sw::normalize-filename 
	     (expand-file-name 
	      (or (getenv "LISP_EXECUTABLE")
		  default-sw-executable))))

      ;; A heap image is loaded into a (presumably generic) lisp.
      ;; (Franz calls this an image.)
      ;; The suffix on such files is .dxl or .sbclimage, etc.

      (setq sw:common-lisp-image-file 
	    (if (equal sw:common-lisp-image-name default-sw-executable)
		nil
	      (sw::normalize-filename (expand-file-name 
				       (or (getenv "LISP_HEAP_IMAGE")
					   default-sw-image)))))

      (setq sw:common-lisp-image-arguments

	;; From http://www.franz.com/support/documentation/7.0/doc/startup.htm#command-line-args-1
        ;;
	;; +c   Start Allegro CL without a console window. 
	;;      (Normally, there is a console window to read/write standard I/O. 
	;;      If you close the console window, the Lisp will be killed.) 
	;;      Note that there will not be an icon in the system tray regardless
	;;      of whether +R or +RR are specified when there is no console. 
	;;      (Having the console minimized with +cm, non-activated with +cn, or
	;;      hidden with +cx does not affect whether there is a system tray icon.)
	;; +cm  Start the console window in a minimized state.
	;; +cn 	Start the console window, but don't activate the console window. 
	;;      This allows Lisp to be started so as to not interfere with the currently selected window.
	;; +cx 	Start the console in a hidden state. 
        ;;      Double-clicking on the tray icon will make the console visible.
	;;      See also the right-click menu on the tray icon.
	;;
	;; In other words:
        ;;
	;;  +c  makes Allegro invisible
	;;  +cn leaves the Allegro window open, but behind other windows
	;;  +cm minimizes the Allegro window
        ;;  +cx minimizes the Allegro window down to a tiny icon in the tray
        ;;	    
	;; We use +cm (+cn and +cx would also be ok), because +c makes it too easy 
        ;; to leave Specware zombies behind if the user just exists from XEmacs 
	;; (which runs as a separate proccess communicating with Specware).

	(if *windows-system-p* '("+cm") nil))

      (setq sw:common-lisp-host "localhost")
      (setq-default sw::lisp-host sw:common-lisp-host)

      (sw:add-specware-to-isabelle-path)

      (when (getenv "SOCKET_INIT_FILE")
	(set-socket-init-for-specware))
      ;(message "%s %s" sw:image-is-executable *specware-lisp*)
      (sleep-for 4)
      (let ((log-warning-minimum-level 'error))
	;; Don't show spurious warning message
	(sw:common-lisp sw:common-lisp-buffer-name
			sw:common-lisp-directory
			sw:common-lisp-image-name
			sw:common-lisp-image-arguments
			sw:common-lisp-host
			sw:common-lisp-image-file))
      (wait-for-prompt 0.1)
      (sw:eval-in-lisp-no-value
       (format "(cl:namestring (specware::change-directory %S))" sw:common-lisp-directory))
      (let ((init-form (or (getenv "SPECWARE_INIT_FORM")
			   "(swshell::specware-shell nil)")))
	(goto-char (point-max))
	(if (eq lisp-emacs-interface-type 'slime)
	    (unless (member init-form '(nil ""))
	      (sw:eval-in-lisp-no-value init-form))
	  (simulate-input-expression init-form))
	(sleep-for 0.1)))))

(defun binary-directory (specware-dir)
  (concat specware-dir
	  "/Applications/Specware/bin/"
	  (if *windows-system-p*
	      "windows"
	    (case system-type
	      (darwin "linux")
	      (t (symbol-name system-type))))))

(defun wait-for-prompt (&optional timeout)
  (unless (eq lisp-emacs-interface-type 'slime)
    (sit-for 0.1 t)
    (let ((proc (get-buffer-process *specware-buffer-name*)))
      (while (not (if (eq lisp-emacs-interface-type 'franz)
		      (equal fi:allegro-run-status-string "Idle")
		    (if (eq lisp-emacs-interface-type 'slime)
			(eq (process-status slime-buffer-connection) 'open)
		      (equal comint-status " :ready"))))
	(accept-process-output proc (or timeout 5))))))

(defun set-socket-init-for-specware ()
  (message "set-socket-init-for-specware")
  (setq sw:common-lisp-image-arguments
    (list "-L" (getenv "SOCKET_INIT_FILE"))))

(defun run-lisp-application (&optional lisp-executable image-file)
  (interactive "sExecutable Lisp Program: 
sLisp Heap Image File: ")
  (when (equal lisp-executable "") (setq lisp-executable nil))
  (when (equal image-file      "") (setq image-file      nil))

  (setq sw:common-lisp-host "localhost")
  (setq-default sw::lisp-host sw:common-lisp-host)

  ;; sw:common-lisp-directory is the directory in which the lisp subprocess will
  ;; be executed. It is defined in eli/fi-subproc.el with a default value nil
  ;; This seems to work fine under Unix/Linux but under Windows there is 
  ;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.

  (setq sw:common-lisp-directory (getenv "LISP_DIRECTORY"))

  ;; Below we set a parameter sw:common-lisp-image-name. This is the name 
  ;; used by eli/fi-subproc.el for the Lisp executable. This is the application
  ;; we want to run.  The image file (in the ACL sense) or world, is bound 
  ;; to common-lisp-image-file. If the executable is produced by
  ;; generate-application, then typically, there will not be an image file.

  (setq sw:common-lisp-image-name 
	(or lisp-executable
	    (and (boundp 'sw:common-lisp-image-name) sw:common-lisp-image-name)
	    (getenv "LISP_EXECUTABLE")))

  (setq sw:common-lisp-image-file
	(or image-file
	    (and (boundp 'sw:common-lisp-image-file) sw:common-lisp-image-file)
	    (getenv "LISP_HEAP_IMAGE")))

  (message "[%s][%s]" sw:common-lisp-image-name sw:common-lisp-image-file)
  (sit-for 4)

  (setq sw:common-lisp-image-name 
	(if (equal sw:common-lisp-image-name "NONE")
	    nil
	  (sw::normalize-filename (expand-file-name sw:common-lisp-image-name))))
	 
  (setq sw:common-lisp-image-file
	(if (equal sw:common-lisp-image-file "NONE")
	    nil
	  (sw::normalize-filename (expand-file-name sw:common-lisp-image-file))))

  (setq sw:common-lisp-image-arguments
    (if *windows-system-p* '("+cm") nil)) ; see note above

  (let ((log-warning-minimum-level 'error))
    (sw:common-lisp sw:common-lisp-buffer-name
		    sw:common-lisp-directory
		    sw:common-lisp-image-name
		    sw:common-lisp-image-arguments
		    sw:common-lisp-host
		    sw:common-lisp-image-file)))

(defun run-plain-lisp (&optional sleep)
  (interactive)
  (sit-for 1)
  (when (inferior-lisp-running-p)
    (sw:exit-lisp)
    (sit-for 2))
  (setq sw:common-lisp-host "localhost")

  ;; sw:common-lisp-directory is the directory in which the lisp subprocess will
  ;; be executed. It is defined in eli/fi-subproc.el with a default value nil
  ;; This seems to work fine under Unix/Linux but under Windows there is 
  ;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.

  (setq sw:common-lisp-directory (getenv "LISP_DIRECTORY"))

  ;; Below we set a parameter sw:common-lisp-image-name. This is the name 
  ;; used by eli/fi-subproc.el for the Lisp executable. This is the application
  ;; we want to run.  The image file (in the ACL sense) or world, is bound 
  ;; to common-lisp-image-file. If the executable is produced by
  ;; generate-application, then typically, there will not be an ACL image file.

  (setq sw:common-lisp-image-name (getenv "LISP_EXECUTABLE"))
  (setq sw:common-lisp-image-file nil)
  (setq sw:common-lisp-image-arguments
	(if *windows-system-p* '("+cm") nil)) ; see note above

  (let ((log-warning-minimum-level 'error))
    (sw:common-lisp sw:common-lisp-buffer-name
		    sw:common-lisp-directory
		    sw:common-lisp-image-name
		    sw:common-lisp-image-arguments)
    (when sleep (sit-for sleep))))

(defvar *specware-auto-start* nil
  "If T start Specware when needed if it not already running")

(defun ensure-specware-running ()
  (unless (inferior-lisp-running-p)
    ;; first wait up to 5 seconds to see if existing lisp is available
    (if (dotimes (i 100)
	  (when (> i 50)
	    (message "Checking to see if existing lisp is running in buffer %S -- %S"
		     sw:common-lisp-buffer-name (- 100 i)))
	  (sit-for 0.2 t)
	  (when (inferior-lisp-running-p)
	    (return t)))
	()   ;; (message "Specware is running..")
      ;; timed out -- see if we should and can start lisp
      (if *specware-auto-start*
	  (progn     
	    (run-specware4)
	    ;; similar wait for up to 10 seconds
	    (if (dotimes (i 100)
		  (message "Checking to see if new lisp has started in buffer %S -- %S"
			   sw:common-lisp-buffer-name i (- 100 i))
		  (sit-for 0.1 t)
		  (when (inferior-lisp-running-p)
		    (return t)))
		(message "New Specware now runnning...")
	      (error "Could not start Specware.")))
	(error "Specware not running. Do M-x run-specware4")))))

;; (simulate-input-expression "t")
(defun simulate-input-expression (str)
  (ensure-specware-running)
  (let ((win (get-buffer-window *specware-buffer-name*)))
    (if win (select-window win)
      (sw:switch-to-lisp)))
  (pop-to-buffer *specware-buffer-name*) ; might want to choose explicit frame
  (goto-char (point-max))
  (insert str)
  (inferior-lisp-newline)
  (sit-for 0.1))

(defvar *specware-continue-form* nil)
(defvar *last-specware-continue-form* nil)

(defvar *sentinel-data* '()) ; for debugging continue-form-when-ready

(defun continue-emacs-computation (process event)
  ;; for debugging continue-form-when-ready...
;  (setq *sentinel-data* 
;	;; use format to capture current descriptions
;	(cons (list (current-time-string)
;		    (format "%S" process) 
;		    (list 'event (format "%S" event)))
;	      *sentinel-data*))
  (let ((fm *specware-continue-form*))
    (setq *last-specware-continue-form* fm)
    (setq *specware-continue-form* nil)
    (eval fm)))

(defun continue-form-when-ready (form)
  (setq *specware-continue-form* form)
  (let ((sw-proc (get-buffer-process *specware-buffer-name*)))
    ;; for debugging continue-form-when-ready...
;    (setq *sentinel-data* 
;	  ;; use format to capture current descriptions...
;	  (cons (list (current-time-string)
;		      (format "%S" sw-proc)
;		      (list (list 'old-sentinel (format "%S" (process-sentinel sw-proc)))
;			    (list 'new-sentinel 'continue-emacs-computation (format "%S" form))))
;		*sentinel-data*))
    (when sw-proc
      (set-process-sentinel sw-proc 'continue-emacs-computation)))
  (simulate-input-expression (exit-form)))

(defun exit-form ()
  (if (eq lisp-emacs-interface-type 'slime)
      "(specware::exit-when-done)"
    "(specware::exit)"))

;(defun exit-lisp ()
;  (if (eq lisp-emacs-interface-type 'slime)
;      (sw:exit-lisp)
;    (eval-in-lisp-in-order "(cl-user::exit)")))

(defun kill-lisp-and-then-emacs (&optional delay)
  (when (null delay) (setq delay 10))
  ;; mutual lisp/emacs suicide...
  (message "Will automatically exit in %S seconds..." delay)
  (sit-for delay)
  (continue-form-when-ready
   ;; continue-form-when-ready kills the sublisp process, 
   ;; then waits for a status change signal on that process
   ;; before processing the given command
   (`(kill-emacs t))))
  
(defun delete-continuation ()
  (interactive)
  (let ((sw-proc (get-buffer-process *specware-buffer-name*)))
    ;; for debugging continue-form-when-ready...
    (setq *sentinel-data* 
	  ;; use format to capture current descriptions...
	  (cons (list (current-time-string) 
		      (format "%S" sw-proc)
		      (list 'delete-continuation))
		*sentinel-data*))
    (setq *specware-continue-form* nil)
    (when sw-proc
      (set-process-sentinel sw-proc nil))))

(defun eval-in-lisp-in-order (str)
  (sit-for 0.1)
  (if (eq lisp-emacs-interface-type 'slime)
      (progn (when (slime-rex-continuations)
	       (sit-for 2)
	       (when (slime-rex-continuations)
		 (sit-for 2)))
	     (simulate-input-expression str))
    (simulate-input-expression str)))

(defun build-specware4-and-then-exit (&optional in-current-dir?)
  (interactive "P")
  (build-specware4 in-current-dir? t))
  
(defun build-specware4 (&optional in-current-dir? auto-exit?)
  (interactive "P")
  (let* ((*specware4-dir (sw::normalize-filename
			 (if in-current-dir?
			     (strip-final-slash (if (stringp in-current-dir?)
						    in-current-dir?
						  default-directory))
			   (getenv "SPECWARE4"))))
	 (build-dir (concat *specware4-dir "/Applications/Specware/Handwritten/Lisp"))
	 (bin-dir (binary-directory *specware4-dir))
	 (lisp-dir (concat *specware4-dir "/Applications/Specware/lisp"))
	 (slash-dir (sw::normalize-filename "/"))
	 (world-name (concat bin-dir "/Specware4." *lisp-image-extension*))
	 (base-world-name
	   (if (and (eq *specware-lisp* 'allegro))
	       (concat bin-dir "/big-alisp." *lisp-image-extension*)
	     nil))
	 (specware4-lisp (concat lisp-dir "/Specware4.lisp"))
	 (specware4-base-lisp (concat *specware4-dir "/Applications/Specware/Specware4-base.lisp")))
    (run-plain-lisp 1)
    (when (and (file-exists-p specware4-base-lisp)
	       (or (not (file-exists-p specware4-lisp))
		   (file-newer-than-file-p specware4-base-lisp specware4-lisp)))
      (when (file-exists-p specware4-lisp)
	(copy-file specware4-lisp (concat lisp-dir "/Specware4-saved.lisp") t))
      (copy-file specware4-base-lisp specware4-lisp t))
    (sit-for 3)
    (eval-in-lisp-in-order
     (format "(cl:load %S)"
	     (concat *specware4-dir "/Applications/Handwritten/Lisp/load-utilities.lisp")))
    (eval-in-lisp-in-order
     (format "(cl:load %S)"
	     (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors")))
    (eval-in-lisp-in-order
     (format "(specware::setenv \"SWPATH\" %S)"
	     (concat (sw::normalize-filename *specware4-dir)
		     (if *windows-system-p* ";" ":")
		     slash-dir)))
    (eval-in-lisp-in-order
     (format "(specware::setenv \"SPECWARE4\" %S)"
	     (sw::normalize-filename *specware4-dir)))
    (eval-in-lisp-in-order
     (format "(cl:namestring (specware::change-directory %S))" build-dir))
    (eval-in-lisp-in-order "(cl:time (cl:load \"Specware4.lisp\"))")
    (continue-form-when-ready
     ;; continue-form-when-ready kills the sublisp process, 
     ;; then waits for a status change signal on that process
     ;; before processing the given command
     (`(build-specware4-continue (, *specware4-dir) (, build-dir) (, bin-dir)
				 (, slash-dir) (, world-name) (, base-world-name)
				 (, auto-exit?))))))

(defun build-specware4-continue (*specware4-dir build-dir bin-dir slash-dir world-name base-world-name auto-exit?)
  (when (and base-world-name (not (file-exists-p base-world-name)))
    (run-plain-lisp 1)
    ;; Currently
    (eval-in-lisp-in-order
     (format (if *windows-system-p*
		 ;; various configurations that were used in Allegro 6.2 for windows:
		 ;; "(build-lisp-image %S :c-heap-start  #x7d200000 :oldspace #x100)" ; Paulo's "magic number"
		 ;; "(build-lisp-image %S :c-heap-start  #x7c623000 :oldspace #x100)"
		 ;; "(build-lisp-image %S :c-heap-start  #x7e000000 :oldspace #x100)"
		 "(build-lisp-image %S)"
	       ;; non-windows:
	       ;; read-from-string is because of slime misfeature
	       "(cl-user::build-lisp-image %S :lisp-heap-start (cl:read-from-string \"#x48000000\")
                                              :oldspace #x100)")
	     base-world-name))
    (sit-for 4)
    (dotimes (i 10)
      (sit-for 2)
      (when (file-exists-p base-world-name)
	(return nil)))
    (sw:exit-lisp)
    (sit-for 3))
  (cond ((null base-world-name)
	 (run-plain-lisp 1))
	(t
	 (sit-for 3)
	 (run-lisp-application (getenv "LISP_EXECUTABLE") base-world-name)))
  (sit-for 3)
  (eval-in-lisp-in-order
   (format "(cl:load %S)"
	   (concat *specware4-dir "/Applications/Handwritten/Lisp/load-utilities." *fasl-extension*)))
  (sit-for 3)
  (eval-in-lisp-in-order (format "(specware::setenv \"SWPATH\" %S)"
				    (concat (sw::normalize-filename *specware4-dir)
					    (if *windows-system-p* ";" ":")
					    slash-dir)))
  (eval-in-lisp-in-order (format "(specware::setenv \"SPECWARE4\" %S)"
				    (sw::normalize-filename *specware4-dir)))
  (eval-in-lisp-in-order (format "(cl:load %S)"
				 (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors")))
  (eval-in-lisp-in-order (format "(cl:load %S)"
				 (concat *specware4-dir "/Applications/Handwritten/Lisp/memory-management")))
  (eval-in-lisp-in-order (format "(cl:namestring (specware::change-directory %S))" 
				 build-dir))
  (eval-in-lisp-in-order "(cl-user::set-gc-parameters-for-build nil)")
  (eval-in-lisp-in-order "(cl:load \"Specware4.lisp\")")
  (eval-in-lisp-in-order "(cl-user::compact-memory t)")
  (eval-in-lisp-in-order "(cl-user::set-gc-parameters-for-use nil)")
  (when (file-exists-p world-name)
    (rename-file world-name 
		 (concat bin-dir "/Specware4-saved." *lisp-image-extension*)
		 t))
  (sit-for 5)
  (eval-in-lisp-in-order (format (case *specware-lisp*
				   (cmulisp "(ext:save-lisp %S)")
				   (allegro "(excl::dumplisp :name %S)")
				   (openmcl "(ccl:save-application %S)")
				   (sbcl "
 (progn (dolist (thread (sb-thread:list-all-threads))
    (unless (eq thread sb-thread:*current-thread*)
      (sb-thread:terminate-thread thread)))
    (sleep 0.1)
    (sb-ext:save-lisp-and-die %S))"))
				 world-name))
  (sit-for 2)
  (dotimes (i 10)
    (sit-for 2)
    (when (file-exists-p world-name)
      (return nil)))
  (unless (eq *specware-lisp* 'sbcl)
    (eval-in-lisp-in-order
     (format "(cl:let ((filename %S))
             (cl:cond ((cl:probe-file filename)
                    (cl:format t \"~2&Wrote new ~A~2%%\" filename)
    	            (cl:format t \"~&It is safe to exit now..~%%\"))
                   (t
	            (cl:warn \"Failed to write new ~A\" filename))))"
	     world-name))
    (when auto-exit?
      (kill-lisp-and-then-emacs)))
  )

(defun build-specware4-from-base (in-current-dir?)
  (interactive "P")
  (let* ((*specware4-dir (sw::normalize-filename
			 (if in-current-dir?
			     (strip-final-slash (if (stringp in-current-dir?)
						    in-current-dir?
						  default-directory))
			   (getenv "SPECWARE4"))))
	 (dir (concat *specware4-dir "/Applications/Specware/Handwritten/Lisp"))
	 (bin-dir (binary-directory *specware4-dir))
	 (lisp-dir (concat *specware4-dir
			     "/Applications/Specware/lisp"))
	 (slash-dir (sw::normalize-filename "/"))
	 (world-name (concat bin-dir "/Specware4." *lisp-image-extension*))
	 (base-world-name
	   (if (and (eq *specware-lisp* 'allegro))
	       (concat bin-dir "/big-alisp." *lisp-image-extension*)
	     nil))
	 (specware4-lisp (concat lisp-dir "/Specware4.lisp"))
	 (specware4-base-lisp (concat *specware4-dir "/Applications/Specware/Specware4-base.lisp")))
    (run-plain-lisp 1)
    (eval-in-lisp-in-order
     (format "(cl:load %S)"
	     (concat *specware4-dir "/Applications/Handwritten/Lisp/load-utilities")))
    (eval-in-lisp-in-order (format "(specware::setenv \"SWPATH\" %S)"
				   (concat (sw::normalize-filename *specware4-dir)
					   (if *windows-system-p* ";" ":")
					   slash-dir)))
    (eval-in-lisp-in-order (format "(specware::setenv \"SPECWARE4\" %S)"
				      (sw::normalize-filename *specware4-dir)))
        
    (when (file-exists-p specware4-lisp)
      (copy-file specware4-lisp (concat lisp-dir "/Specware4-saved.lisp") t))
    (when (file-exists-p specware4-base-lisp)
      (copy-file specware4-base-lisp specware4-lisp t))
    (eval-in-lisp-in-order (format "(cl:namestring (specware::change-directory %S))" dir))
    (eval-in-lisp-in-order "(cl:load \"Specware4.lisp\")")
    (continue-form-when-ready
     ;; continue-form-when-ready kills the sublisp process, 
     ;; then waits for a status change signal on that process
     ;; before processing the given command
     (`(build-specware4-continue (, *specware4-dir) (, dir) (, bin-dir)
				 (, slash-dir) (, world-name) (, base-world-name)
				 nil)))))

(defun bootstrap-specware4-and-then-exit (&optional in-current-dir?)
  (interactive "P")
  (bootstrap-specware4 in-current-dir? t))

(defun bootstrap-specware4 (&optional in-current-dir? auto-exit?)
  (interactive "P")
  (let ((*specware4-dir (sw::normalize-filename
			(if in-current-dir? (strip-final-slash default-directory)
			  (concat (getenv "SPECWARE4"))))))
    (run-specware4 *specware4-dir)
    (sit-for 0.1)
    (eval-in-lisp-in-order
     (format "(cl:namestring (specware::change-directory %S))" *specware4-dir))
;    (eval-in-lisp-in-order (format "(specware::setenv \"SWPATH\" %S)"
;				   (concat (sw::normalize-filename *specware4-dir))))
    (eval-in-lisp-in-order (format "(specware::setenv \"SPECWARE4\" %S)"
				      (sw::normalize-filename *specware4-dir)))
    (eval-in-lisp-in-order "(progn #+allegro(sys::set-stack-cushion 10000000)
                                   #-allegro())")
    (eval-in-lisp-in-order "(cl:time (cl-user::boot))")
    (sit-for 1)
    (continue-form-when-ready 
     ;; continue-form-when-ready kills the sublisp process, 
     ;; then waits for a status change signal on that process
     ;; before processing the given command
     (`(build-specware4 (, *specware4-dir) (, auto-exit?))))))


(defun test-specware-bootstrap (in-current-dir?)
  (interactive "P")
  (let ((current-dir default-directory))
    (if (not (inferior-lisp-running-p))
	(message "Do M-x bootstrap-specware first")
      (progn (shell-command (concatenate 'string "cd "
					 (if in-current-dir? current-dir
					   *specware-home-directory*)
					 "; /bin/rm */sig/*.sig"))
	     (sit-for 4)		; Necessary? Enough?
	     (eval-in-lisp-in-order "(Bootstrap-Spec::compileBootstrap)")
	     (eval-in-lisp-in-order ":exit")
	     (sit-for 5)
	     (while (inferior-lisp-running-p)
	       (sit-for 2))
	     (run-plain-lisp 1)
	     (eval-in-lisp-in-order "(cl:load \"load.lisp\")")
	     (eval-in-lisp-in-order "(Bootstrap-Spec::compileAll)")))))

(defun strip-final-slash (dirname)
  (let ((len (length dirname)))
    (if (equal ?/ (elt dirname (- len 1)))
	(substring dirname 0 (- len 1))
      dirname)))

(defun run-PSL (&optional in-current-dir?)
  ;;  ... SEMI-OBSOLETE -- NEEDS REVIEW IF USED ...
  (interactive "P")
  (let* ((*specware4-dir (sw::normalize-filename
			 (if in-current-dir?
			     (strip-final-slash (if (stringp in-current-dir?)
						    in-current-dir?
						  default-directory))
			   (concat (getenv "SPECWARE4")))))
	 (bin-dir (concat *specware4-dir
			  "/Applications/PSL/bin/"
			  (if *windows-system-p*
			      "windows"
			    (case system-type
			      (darwin "linux")
			      (t (symbol-name system-type))))))
	 (world-name (concat bin-dir "/PSL." *lisp-image-extension*)))

    (setq sw:common-lisp-host "localhost")
    (setq-default sw::lisp-host sw:common-lisp-host)
    ;;
    ;; sw:common-lisp-directory is the directory in which the lisp subprocess will
    ;; be executed. It is defined in eli/fi-subproc.el with a default value nil
    ;; This seems to work fine under Unix/Linux but under Windows there is 
    ;; a "stringp, nil" error message. So we set it to "c:." to avoid the problem.
    ;;
    (setq sw:common-lisp-directory (concat *specware4-dir "/"))
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
    (setq sw:common-lisp-image-file world-name)
    (setq sw:common-lisp-image-arguments
      (if *windows-system-p* '("+cm") nil)) ; see note above
    (when (getenv "SOCKET_INIT_FILE")
      (set-socket-init-for-specware))

    (let ((log-warning-minimum-level 'error))
      ;; Don't show spurious warning message
      (sw:common-lisp sw:common-lisp-buffer-name
		      sw:common-lisp-directory
		      sw:common-lisp-image-name
		      sw:common-lisp-image-arguments
		      sw:common-lisp-host
		      sw:common-lisp-image-file))
    (goto-char (point-max))
    ))
