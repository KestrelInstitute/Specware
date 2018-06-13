(require 'sw-slime)

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
	      (or (getenv "SPECWARE_EXECUTABLE")
		  (getenv "LISP_EXECUTABLE")
		  default-sw-executable))))

      ;; A heap image is loaded into a (presumably generic) lisp.
      ;; (Franz calls this an image.)
      ;; The suffix on such files is .dxl or .sbclimage, etc.

      (setq sw:common-lisp-image-file
	    (if (equal sw:common-lisp-image-name default-sw-executable)
		nil
	      (if (equal (getenv "LISP_HEAP_IMAGE") "NONE")
		  nil
		(sw::normalize-filename (expand-file-name
					 (or (getenv "LISP_HEAP_IMAGE")
					     default-sw-image))))))

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

	(if (and *windows-system-p* (eq *specware-lisp* 'allegro))
            '("+cm") nil))

      (setq sw:common-lisp-host "localhost")
      (setq-default sw::lisp-host sw:common-lisp-host)

      ;(sw:add-specware-to-isabelle-path)

      (when (getenv "SOCKET_INIT_FILE")
	(set-socket-init-for-specware))
      ;(message "%s %s" sw:image-is-executable *specware-lisp*)
      (when (null (cdr (window-list))) (split-window nil nil (> (frame-width) 160)))
      (sleep-for 0.1)
      (let ((log-warning-minimum-level 'error))
	;; Don't show spurious warning message
	(sw:common-lisp sw:common-lisp-buffer-name
			sw:common-lisp-directory
			sw:common-lisp-image-name
			sw:common-lisp-image-arguments
			sw:common-lisp-host
			sw:common-lisp-image-file))
      (sleep-for 1)
      (wait-for-prompt 0.5)
      ;(delete-other-windows)
      (when (and (fboundp 'set-frame-pixel-size) (fboundp 'frames-of-buffer) (< (frame-pixel-width) 1200))
        (set-frame-pixel-size (car (frames-of-buffer)) 1200 800))
      (sw:eval-in-lisp-no-value
       (format "(cl:namestring (Specware::change-directory %S))" sw:common-lisp-directory))
      (let ((init-form (or (getenv "SPECWARE_INIT_FORM")
			   "(SWShell::specware-shell nil)")))
	(goto-char (point-max))
	(if (eq lisp-emacs-interface-type 'slime)
	    (unless (member init-form '(nil "" "NIL"))
	      (sw:eval-in-lisp-no-value init-form))
	  (simulate-input-expression init-form))
	(sleep-for 0.1)))))

(defun binary-directory (specware-dir)
  (concat specware-dir
	  "/Applications/Specware/bin/"
	  (if *windows-system-p*
	      "windows"
	    (case system-type
	      (darwin "unix")
              (gnu/linux "unix")
	      (t (symbol-name system-type))))))

(defvar comint-status)

(defun wait-for-prompt (&optional timeout)
  (unless (eq lisp-emacs-interface-type 'slime)
    (sit-for 0.1 t)
    (let ((proc (get-buffer-process *specware-buffer-name*)))
      (while (not (if (eq lisp-emacs-interface-type 'slime)
                      (eq (process-status slime-buffer-connection) 'open)
                    (equal comint-status " :ready")))
	(accept-process-output proc (or timeout 1))))))

(defun set-socket-init-for-specware ()
  ;; (message "set-socket-init-for-specware")
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
	    (getenv "SPECWARE_EXECUTABLE")
	    (getenv "LISP_EXECUTABLE")))

  (setq sw:common-lisp-image-file
	(or image-file
	    (and (boundp 'sw:common-lisp-image-file) sw:common-lisp-image-file)
	    (getenv "LISP_HEAP_IMAGE")))

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
  (sit-for 0.5)
  (when (inferior-lisp-running-p)
    (sw:exit-lisp)
    (sit-for 1))
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

  (setq sw:common-lisp-image-name (or (getenv "LISP")
                                      (getenv "LISP_EXECUTABLE")))
  (setq sw:common-lisp-image-file nil)
  (setq sw:common-lisp-image-arguments
	(if (and *windows-system-p* (eq *specware-lisp* 'allegro))
            '("+cm") nil)) ; see note above

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
			   sw:common-lisp-buffer-name (- 100 i))
		  (sit-for 0.1 t)
		  (when (inferior-lisp-running-p)
		    (return t)))
		(message "New Specware now runnning...")
	      (error "Could not start Specware.")))
	(error "Specware not running. Do M-x run-specware4")))))

(defun simulate-input-expression (str)
  (ensure-specware-running)
  (let ((win (get-buffer-window *specware-buffer-name*)))
    (if win (select-window win)
      (sw:switch-to-lisp))
    (pop-to-buffer *specware-buffer-name*) ; might want to choose explicit frame
    (goto-char (point-max))
    (sw:move-beginning-of-line 1)
    (unless (= (point) (point-max))
      (kill-line))
    (insert str)
    (inferior-lisp-newline))
  (sit-for 0.1))

(defun simulate-input-expression-quiet (str)
  (ensure-specware-running)
  (with-current-buffer *specware-buffer-name*
    (goto-char (point-max))
    (sw:move-beginning-of-line 1)
    (unless (= (point) (point-max))
      (kill-line))
    (insert str)
    (inferior-lisp-newline))
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
  (simulate-input-expression (exit-form))
  )

(defun exit-form ()
  (if (eq lisp-emacs-interface-type 'slime)
      "(Specware::exit-when-done)"
    "(Specware::exit)"))

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
   `(kill-emacs t)))

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
	       (sit-for 0.5)
	       (when (slime-rex-continuations)
		 (sit-for 1)))
	     (simulate-input-expression str))
    (simulate-input-expression str)))

;;; ================================================================================

(defun generate-compile-build-specware4 (&optional in-current-dir?)
  (interactive "P")
  (generate-specware4-aux in-current-dir? t nil))

(defun just-generate-specware4 (&optional in-current-dir?)
  (interactive "P")
  (generate-specware4-aux in-current-dir? nil nil))

(defun generate-specware4-aux (in-current-dir? also-compile-and-build? regenerating?)
  (let* ((*specware4-dir      (sw::normalize-filename
                               (if in-current-dir?
                                   (strip-final-slash default-directory)
                                 (concat (getenv "SPECWARE4")))))
         (bin-dir             (binary-directory *specware4-dir))
         (specware-executable (concat bin-dir "/Specware4."
                                      (if *windows-system-p* "exe"
                                        *lisp-executable-extension*)))
         (specware4-base-lisp (concat *specware4-dir "/Applications/Specware/Specware4-base.lisp")))

    (prepare-specware-build-buffer "*Generate Specware lisp files from specs*" *specware4-dir)

    (cond ((not (file-exists-p specware-executable))
           ;; can't process Specware4.sw without a running specware, so compile, build, and come back here
           (progn (message "No specware executable, so will first build one, then try again.")
                  (sit-for 1))
           (specware-build-command "### No specware executable, so will first build one, then try again.")
           (compile-specware4-aux in-current-dir? t t))
          ((file-newer-than-file-p specware4-base-lisp specware-executable)
           ;; specware executable is not up to date with current sources, so compile, build, and come back here
           (progn (message "Previously generated specware lisp files are newer than specware executable.")
                  (sit-for 1)
                  (message "So will recompile them, rebuild specware, and then try again here.")
                  (sit-for 1))
           (specware-build-command "### Previously generated specware lisp files are newer than specware executable,")
           (specware-build-command "### so will recompile them, rebuild specware, and then try again here.")
           (compile-specware4-aux in-current-dir? t t))
          (t
           ;; we have an up-to-date specware, so generate new lisp files
           ;; Note: (boot) processes Specware4.sw to produce new lisp files

           (progn (message "Generating Specware lisp files from specs, via (cl-user::boot) ...")
                  (sit-for 1))

           (sit-for (if regenerating? 10 1)) ; avoid race with prior build process
           (specware-build-command "%S --dynamic-space-size %S" specware-executable *sbcl-size*)
           (sit-for 1)
           (let ((print-progress-message
		  (if also-compile-and-build?
		      '(format t "Call back to emacs to tell it to compile and build Specware.~%")
		    ""))
		 (callback-to-emacs
                  ;; if we are going to proceed on with compilation and building,
                  ;; then have lisp generate a call back to emacs just before quiting
                  (if also-compile-and-build?
                      ;; First time through, make the third arg true to cause a replay after oompile and build.
                      ;; Second time through, make it false so we don't replay yet again.
                      (specware-build-eval-emacs-str "(progn (sit-for 1) (compile-specware4-aux %s t %s))"
                                                     in-current-dir?
                                                     (not regenerating?))
                    "")))
             (specware-build-command "(progn (cl:time (cl-user::boot)) %S %s (cl-user::finish-output t) (sb-ext:exit))"
				     print-progress-message
				     callback-to-emacs))))))

;;; ================================================================================

(defun compile-build-specware4 (&optional in-current-dir?)
  (interactive "P")
  (compile-specware4-aux in-current-dir? t))

(defun just-compile-specware4 (&optional in-current-dir?)
  (interactive "P")
  (compile-specware4-aux in-current-dir? nil))

(defun compile-specware4-aux (&optional in-current-dir? also-build? also-regenerate?)
  (interactive "P")
  (let* ((*specware4-dir        (sw::normalize-filename
                                 (if in-current-dir?
                                     (strip-final-slash (if (stringp in-current-dir?)
                                                            in-current-dir?
                                                          default-directory))
                                   (getenv "SPECWARE4"))))
	 (build-dir             (concat *specware4-dir "/Applications/Specware/Handwritten/Lisp"))
	 (lisp-dir              (concat *specware4-dir "/Applications/Specware/lisp"))
	 (specware4-lisp        (concat lisp-dir "/Specware4.lisp"))
	 (specware4-base-lisp   (concat *specware4-dir "/Applications/Specware/Specware4-base.lisp"))
         (specware4-loader      (concat build-dir "/Specware4.lisp")))

    ;; move any old Specware.lisp out of the way
    (when (and (file-exists-p specware4-base-lisp)
	       (or (not (file-exists-p specware4-lisp))
		   (file-newer-than-file-p specware4-base-lisp specware4-lisp)))
      (when (file-exists-p specware4-lisp)
	(copy-file specware4-lisp (concat lisp-dir "/Specware4-saved.lisp") t))
      (copy-file specware4-base-lisp specware4-lisp t))

    (prepare-specware-build-buffer "*Compile Specware lisp files*" build-dir)

    (progn (message "Compiling Specware lisp files, by loading %s" specware4-loader)
           (sit-for 1))

    ;; start lisp
    (specware-build-command "sbcl --dynamic-space-size %S" *sbcl-size*) ; Generalize later
    (sit-for 1)

    ;; load utilities
    (specware-build-command "(cl:load %S)" (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors"))

    ;; loading Specare4.lisp will cause lisp files to be compiled
    (let ((print-progress-message
           (if also-build?
	       '(format t "Call back to emacs to tell it to build Specware.~%")
	     ""))
	  (callback-to-emacs
           ;; If we are doing more after we compile, then prepare a form for the lisp image
           ;; to pass back to emacs for invocation just before that lisp image dies.
           (if also-build?
               (specware-build-eval-emacs-str "(progn (sit-for 1) (new-build-specware4 %s %s))"
                                              in-current-dir?
                                              also-regenerate?)
             "")))
      (specware-build-command "(progn (cl:load %S) %S %s (terpri) (cl-user::finish-output t) (sb-ext:exit))"
                              specware4-loader
			      print-progress-message
                              callback-to-emacs))))

;;; ================================================================================

(defun just-build-specware4 (&optional in-current-dir? regenerate?)
  (interactive "P")
  (new-build-specware4 in-current-dir? nil))

(defun new-build-specware4 (&optional in-current-dir? regenerate?)
  (interactive "P")
  (let* ((*specware4-dir        (sw::normalize-filename
                                 (if in-current-dir?
                                     (strip-final-slash (if (stringp in-current-dir?)
                                                            in-current-dir?
                                                          default-directory))
                                   (getenv "SPECWARE4"))))
	 (build-dir             (concat *specware4-dir "/Applications/Specware/Handwritten/Lisp"))
	 (bin-dir               (binary-directory *specware4-dir))
	 (lisp-dir              (concat *specware4-dir "/Applications/Specware/lisp"))
	 (specware-executable   (concat bin-dir "/Specware4." (if *windows-system-p* "exe" *lisp-executable-extension*)))
	 (specware4-lisp        (concat lisp-dir "/Specware4.lisp"))
         (specware4-lisp-binary (concat lisp-dir "/Specware4." *fasl-extension*))
         (specware4-loader      (concat build-dir "/Specware4.lisp")))

    (prepare-specware-build-buffer "*Build Specware executable*" build-dir)

    (progn (message "Build new Specware executable after loading %s" specware4-loader)
           (sit-for 1))

    ;; start lisp
    (specware-build-command "sbcl --dynamic-space-size %S" *sbcl-size*) ; Generalize later
    (sit-for 1)

    ;; load utilities
    (specware-build-command "(cl:load %S)" (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors"))

    (cond ((not (file-exists-p specware4-lisp-binary))
           ;; error
           )
          ((not (file-newer-than-file-p specware4-lisp-binary specware4-lisp))
           ;; error
           )
          (t
           (let ((print-progress-message
		  (if regenerate?
		      '(format t "Call back to emacs to tell it to generate Specware again.~%")
		    ""))
		 (callback-to-emacs
                  ;; If we are regenerating, have the lisp image tell emacs to invoke generate-compile-build-specware4
                  ;; just before that lisp image saved itself and dies.
                  ;; To avoid races, have the form sent back to emacs delay for 5 seconds before proceeding,
                  ;; to give the lisp image time to save itself before it will be invoked.
                  (if regenerate?
                      (specware-build-eval-emacs-str "(progn (sit-for 3) (generate-specware4-aux %s t t))" in-current-dir?)
                    "")))
             (specware-build-command "(progn (cl:load %S) %S %s (force-output t) (sb-ext:save-lisp-and-die %S :executable t))"
                                     specware4-loader
				     print-progress-message
                                     callback-to-emacs
                                     specware-executable))))))

;;; ================================================================================

(defun build-specware4-and-then-exit (&optional in-current-dir?)
  (interactive "P")
  (build-specware4 in-current-dir? t))

(defun build-specware4 (&optional in-current-dir? auto-exit?)
  (interactive "P")
  (if (and (eq *specware-lisp* 'sbcl) (eq lisp-emacs-interface-type 'slime))
      (specware-build in-current-dir?)
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
      (sit-for 1)
      (eval-in-lisp-in-order
       (format "(cl:load %S)"
               (concat *specware4-dir "/Applications/Handwritten/Lisp/load-utilities.lisp")))
      (eval-in-lisp-in-order
       (format "(cl:load %S)"
               (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors")))
      (eval-in-lisp-in-order
       (format "(Specware::setenv \"SWPATH\" %S)"
               (concat (sw::normalize-filename *specware4-dir)
                       (if *windows-system-p* ";" ":")
                       slash-dir)))
      (eval-in-lisp-in-order
       (format "(Specware::setenv \"SPECWARE4\" %S)"
               (sw::normalize-filename *specware4-dir)))
      (eval-in-lisp-in-order
       (format "(cl:namestring (Specware::change-directory %S))" build-dir))
      (eval-in-lisp-in-order "(cl:time (cl:load \"Specware4.lisp\"))")
      (continue-form-when-ready
       ;; continue-form-when-ready kills the sublisp process,
       ;; then waits for a status change signal on that process
       ;; before processing the given command
       `(build-specware4-continue ,*specware4-dir ,build-dir ,bin-dir
                                  ,slash-dir ,world-name ,base-world-name
                                  ,auto-exit?)))))

(defun build-specware4-continue (*specware4-dir build-dir bin-dir slash-dir world-name base-world-name auto-exit?)
  (when (and base-world-name (not (file-exists-p base-world-name)))
    (run-plain-lisp 1)
    (sit-for 1)
    (let ((cmd (format (if (and *windows-system-p* (eq *specware-lisp* 'allegro))
			   ;; various configurations that were used in Allegro 6.2 for windows:
			   ;; "(build-lisp-image %S :c-heap-start  #x7d200000 :oldspace #x100)" ; Paulo's "magic number"
			   ;; "(build-lisp-image %S :c-heap-start  #x7c623000 :oldspace #x100)"
			   ;; "(build-lisp-image %S :c-heap-start  #x7e000000 :oldspace #x100)"
			   ;; build-lisp-image is defined in autloaded build.lisp, which will not be present if running from distribution image
			   "(let ((name %S)) #+specware-distribution (excl::dumplisp :name name) #-specware-distribution (build-lisp-image name))"
			 ;; non-windows:
			 ;; read-from-string is because of slime misfeature
			 "(cl-user::build-lisp-image %S :lisp-heap-start (cl:read-from-string \"#x48000000\")
                                                        :oldspace #x100)")
		       base-world-name)))
      (eval-in-lisp-in-order cmd))
    (sit-for 1)
    (dotimes (i 10)
      (sit-for 1)
      (when (file-exists-p base-world-name)
	(return nil)))
    (sw:exit-lisp)
    (sit-for 1))
  (cond ((null base-world-name)
	 (run-plain-lisp 1))
	(t
	 (sit-for 1)
	 (run-lisp-application (getenv "LISP_EXECUTABLE") base-world-name)))
  (sit-for 1)
  (eval-in-lisp-in-order
   (format "(cl:load %S)"
	   (concat *specware4-dir "/Applications/Handwritten/Lisp/load-utilities." *fasl-extension*)))
  (sit-for 1)
  (eval-in-lisp-in-order (format "(Specware::setenv \"SWPATH\" %S)"
				    (concat (sw::normalize-filename *specware4-dir)
					    (if *windows-system-p* ";" ":")
					    slash-dir)))
  (eval-in-lisp-in-order (format "(Specware::setenv \"SPECWARE4\" %S)"
				    (sw::normalize-filename *specware4-dir)))
  (eval-in-lisp-in-order (format "(cl:load %S)"
				 (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors")))
  (eval-in-lisp-in-order (format "(cl:load %S)"
				 (concat *specware4-dir "/Applications/Handwritten/Lisp/memory-management")))
  (eval-in-lisp-in-order (format "(cl:namestring (Specware::change-directory %S))"
				 build-dir))
  (eval-in-lisp-in-order "(cl-user::set-gc-parameters-for-build nil)")
  (eval-in-lisp-in-order "(cl:load \"Specware4.lisp\")")
  (eval-in-lisp-in-order "(cl-user::compact-memory t)")
  (eval-in-lisp-in-order "(cl-user::set-gc-parameters-for-use nil)")
  (when (file-exists-p world-name)
    (rename-file world-name
		 (concat bin-dir "/Specware4-saved." *lisp-image-extension*)
		 t))
  (sit-for 1)
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
  (sit-for 1)
  (dotimes (i 10)
    (sit-for 1)
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
    (eval-in-lisp-in-order (format "(Specware::setenv \"SWPATH\" %S)"
				   (concat (sw::normalize-filename *specware4-dir)
					   (if *windows-system-p* ";" ":")
					   slash-dir)))
    (eval-in-lisp-in-order (format "(Specware::setenv \"SPECWARE4\" %S)"
				      (sw::normalize-filename *specware4-dir)))

    (when (file-exists-p specware4-lisp)
      (copy-file specware4-lisp (concat lisp-dir "/Specware4-saved.lisp") t))
    (when (file-exists-p specware4-base-lisp)
      (copy-file specware4-base-lisp specware4-lisp t))
    (eval-in-lisp-in-order (format "(cl:namestring (Specware::change-directory %S))" dir))
    (eval-in-lisp-in-order "(cl:load \"Specware4.lisp\")")
    (continue-form-when-ready
     ;; continue-form-when-ready kills the sublisp process,
     ;; then waits for a status change signal on that process
     ;; before processing the given command
     `(build-specware4-continue ,*specware4-dir ,dir ,bin-dir
                                ,slash-dir ,world-name ,base-world-name
                                nil))))


;;; New scheme for booting Specware, specifically for Windows with sbcl
(defvar *specware-build-buffer-name* "*Specware Build Buffer*")
(defvar *specware-build-buffer* nil)
(defvar *specware)

(defun shell-filename (filename)
  (if *windows-system-p*
      (replace-in-string filename "/" "\\\\")
    filename))

(require 'bridge)
(require 'comint)

(defvar comint-last-prompt nil)

;; Patch to comint-output-filter to allow filter to move to new buffer
(defun comint-output-filter (process string)
  (let ((oprocbuf (process-buffer process)))
    ;; First check for killed buffer or no input.
    (when (and string oprocbuf (buffer-name oprocbuf))
      (with-current-buffer oprocbuf
	;; Run preoutput filters
	(let ((functions comint-preoutput-filter-functions))
	  (while (and functions string)
	    (if (eq (car functions) t)
		(let ((functions
                       (default-value 'comint-preoutput-filter-functions)))
		  (while (and functions string)
		    (setq string (funcall (car functions) string))
		    (setq functions (cdr functions))))
	      (setq string (funcall (car functions) string)))
	    (setq functions (cdr functions))))

	;; Insert STRING
	(let ((inhibit-read-only t)
              ;; The point should float after any insertion we do.
	      (saved-point (copy-marker (point) t)))

	  ;; We temporarily remove any buffer narrowing, in case the
	  ;; process mark is outside of the restriction
	  (save-restriction
	    (widen)

	    (goto-char (process-mark process))
	    (set-marker comint-last-output-start (point))

            ;; Try to skip repeated prompts, which can occur as a result of
            ;; commands sent without inserting them in the buffer.
            (let ((bol (save-excursion (forward-line 0) (point)))) ;No fields.
              (when (and (not (bolp))
                         (looking-back comint-prompt-regexp bol))
                (let* ((prompt (buffer-substring bol (point)))
                       (prompt-re (concat "\\`" (regexp-quote prompt))))
                  (while (string-match prompt-re string)
                    (setq string (substring string (match-end 0)))))))
            (while (string-match (concat "\\(^" comint-prompt-regexp
                                         "\\)\\1+")
                                 string)
              (setq string (replace-match "\\1" nil nil string)))

	    ;; insert-before-markers is a bad thing. XXX
	    ;; Luckily we don't have to use it any more, we use
	    ;; window-point-insertion-type instead.
	    (insert string)

	    ;; Advance process-mark
	    (set-marker (process-mark process) (point))

	    (unless comint-inhibit-carriage-motion
	      ;; Interpret any carriage motion characters (newline, backspace)
	      (comint-carriage-motion comint-last-output-start (point)))

	    ;; Run these hooks with point where the user had it.
	    (goto-char saved-point)
	    (run-hook-with-args 'comint-output-filter-functions string)
	    (set-marker saved-point (point))

	    (with-current-buffer oprocbuf         ; sjw: filter fn may have changed buffer
              (goto-char (process-mark process))) ; In case a filter moved it.

	    (unless comint-use-prompt-regexp
              (with-silent-modifications
                (add-text-properties comint-last-output-start (point)
                                     '(front-sticky
				       (field inhibit-line-move-field-capture)
				       rear-nonsticky t
				       field output
				       inhibit-line-move-field-capture t))))

	    ;; Highlight the prompt, where we define `prompt' to mean
	    ;; the most recent output that doesn't end with a newline.
	    (let ((prompt-start (save-excursion (forward-line 0) (point)))
		  (inhibit-read-only t))
	      (when comint-prompt-read-only
		(with-silent-modifications
		  (or (= (point-min) prompt-start)
		      (get-text-property (1- prompt-start) 'read-only)
		      (put-text-property (1- prompt-start)
					 prompt-start 'read-only 'fence))
		  (add-text-properties prompt-start (point)
				       '(read-only t front-sticky (read-only)))))
	      (when comint-last-prompt
		;; There might be some keywords here waiting for
		;; fontification, so no `with-silent-modifications'.
		(font-lock--remove-face-from-text-property
		 (car comint-last-prompt)
		 (cdr comint-last-prompt)
		 'font-lock-face
		 'comint-highlight-prompt))
	      (setq comint-last-prompt
		    (cons (copy-marker prompt-start) (point-marker)))
	      (font-lock-prepend-text-property prompt-start (point)
					       'font-lock-face
					       'comint-highlight-prompt)
	      (add-text-properties prompt-start (point) '(rear-nonsticky t)))
	    (goto-char saved-point)))))))

(defun start-specware-build-buffer (&optional name)
  (interactive)
  ;; Works with newer shell.el but not older
  ;;(setq *specware-build-buffer* (get-buffer-create *specware-build-buffer-name*))
  ;;(shell *specware-build-buffer*)
  (unless (null name)
    (setq *specware-build-buffer-name* name))

  (let ((shell-multiple-shells t)) ;; unused here, is this used by bridge code??
    (shell)
    (rename-buffer *specware-build-buffer-name*)
    (setq *specware-build-buffer* (current-buffer)))

  (set-buffer *specware-build-buffer-name*)
  (add-hook 'comint-output-filter-functions 'run-specware-after-saving-lisp-image nil t)
  (install-bridge)
  (setq bridge-handlers '(("(" . emacs-eval-handler)))
  )

(defvar buffer-counter 0)

(defun prepare-specware-build-buffer (buffer-name dir)

  ;; on windows, a shell may die inside a live buffer (sigh).
  ;; The end of that buffer may then say "Process shell finished",
  ;; so we could look for that and make this smarter...
  ;; In the meantime, make the buffer names distinct (maybe not a bad idea anyway).

  (when *windows-system-p*
    (setq buffer-name (concat (format "[%d] " (incf buffer-counter)) buffer-name)))

  (if (and (buffer-live-p (get-buffer buffer-name))
           (not *windows-system-p*)) ;; see note above
      (rename-specware-build-buffer buffer-name)
    (start-specware-build-buffer buffer-name))

  ;; kill any prior lisp accidentally running there...
  ;; (when (sbcl-running-in-build-buffer)
  ;;   (specware-build-command "(sb-ext:exit)"))
  ;; connect to build directory
  (sit-for 1) ;; give shell time to start (sigh)
  (specware-build-cd-command dir)
  (with-current-buffer *specware-build-buffer-name*
    ;(delete-other-windows)
    (when (and (fboundp 'set-frame-pixel-size) (fboundp 'frames-of-buffer)(< (frame-pixel-width) 1200))
      (set-frame-pixel-size (car (frames-of-buffer)) 1200 800)))
  )

(defun rename-specware-build-buffer (new-name)
  (set-buffer *specware-build-buffer-name*)
  (rename-buffer new-name)
  (setq *specware-build-buffer-name* new-name))

(defun sbcl-running-in-build-buffer()
  (sit-for 0.1)
  (with-current-buffer *specware-build-buffer-name*
    (goto-char (point-max))
    (comint-bol nil)
    (not (eq (point) (point-max)))))

(defun specware-build-cd-command (dir)
  (specware-build-command "cd %s" (if *windows-system-p* dir (shell-filename dir))))

(defun specware-build-command (str &rest args)
  (let ((win (get-buffer-window *specware-build-buffer-name*)))
    (if win (select-window win)))
  (pop-to-buffer *specware-build-buffer*) ; might want to choose explicit frame
  (goto-char (point-max))
  (insert (apply 'format str args))
  (comint-send-input)
  (sit-for 0.1))

(defun specware-build-eval-emacs (str &rest args)
  (specware-build-command "(format t \"~a\" %S)" (apply 'format str args)))

(defun specware-build-eval-emacs-str (str &rest args)
  (format "(format t \"~a\" %S)" (apply 'format str args)))

;Westfold uses this and specware-build.
(defun specware-boot (&optional in-current-dir? continuation?)
  (interactive "P")
  (let* ((*specware4-dir (sw::normalize-filename
                          (if in-current-dir? (strip-final-slash default-directory)
                            (concat (getenv "SPECWARE4")))))
         (bin-dir (binary-directory *specware4-dir))
         (specware-executable (concat bin-dir "/Specware4." (if *windows-system-p* "exe"
                                                              *lisp-executable-extension*)))
         (specware4-base-lisp (concat *specware4-dir
                                      "/Applications/Specware/Specware4-base.lisp")))
    (when continuation?
      ;; warning: race condition, previous lisp might still be running (e.g. to save itself)
      ;; so give it time to complete
      (sit-for 1))
    (prepare-specware-build-buffer *specware-build-buffer-name* *specware4-dir)
    (if (or (not (file-exists-p specware-executable))
            (file-newer-than-file-p specware4-base-lisp specware-executable))
        (specware-build in-current-dir? nil 'boot)
      (progn (specware-build-command "%S --dynamic-space-size %S" specware-executable *sbcl-size*)
             (sit-for 0.5)
             (specware-build-command "(progn (cl:time (cl-user::boot)) %s (cl-user::finish-output t) (sb-ext:exit))"
                                     (specware-build-eval-emacs-str "(specware-build %s nil t)"
                                                                    in-current-dir?))))))

;Westfold uses this and specware-boot.
(defun specware-build (&optional in-current-dir? secondTime? continuation?)
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
	 (specware-executable (concat bin-dir "/Specware4." (if *windows-system-p* "exe"
                                                              *lisp-executable-extension*)))
	 (specware4-lisp (concat lisp-dir "/Specware4.lisp"))
         (specware4-lisp-binary (concat lisp-dir "/Specware4." *fasl-extension*))
	 (specware4-base-lisp (concat *specware4-dir
                                      "/Applications/Specware/Specware4-base.lisp"))
         (specware-tgz (concat *specware4-dir
                               "/Applications/Specware/SpecwareLispFiles.tgz"))
         (specware4-loader (concat build-dir "/Specware4.lisp")))
    (when (and (file-exists-p specware4-base-lisp)
	       (or (not (file-exists-p specware4-lisp))
		   (file-newer-than-file-p specware4-base-lisp specware4-lisp)))
      (when (file-exists-p specware4-lisp)
	(copy-file specware4-lisp (concat lisp-dir "/Specware4-saved.lisp") t))
      (copy-file specware4-base-lisp specware4-lisp t))

    (prepare-specware-build-buffer *specware-build-buffer-name* build-dir)

    (when (or (not (file-exists-p specware4-lisp))
              (and (file-exists-p specware-tgz)
                   (file-newer-than-file-p specware-tgz specware4-lisp)))
      (specware-build-command "tar -xvzf %S -C %S" specware-tgz lisp-dir))

    (specware-build-command "sbcl --dynamic-space-size %S" *sbcl-size*)

    (sit-for 0.5)
    (specware-build-command "(cl:load %S)"
                            (concat *specware4-dir "/Applications/Handwritten/Lisp/exit-on-errors"))
    (if (and (file-exists-p specware4-lisp-binary)
             (file-newer-than-file-p specware4-lisp-binary specware4-lisp))
        (progn
          (when (inferior-lisp-running-p)
            (sw:exit-lisp))
          (if (eq continuation? 'boot)
              (specware-build-command "(progn (cl:load %S) %s (force-output t) (sb-ext:save-lisp-and-die %S :executable t))"
                                      specware4-loader
                                      (specware-build-eval-emacs-str "(specware-boot %s t)"
                                                                     in-current-dir?)
                                      specware-executable)
            (specware-build-command "(progn (cl:load %S) (force-output t) (sb-ext:save-lisp-and-die %S :executable t))"
                                    specware4-loader
                                    specware-executable)))
      (if secondTime?
          (message "Failed to build Specware!")
        (specware-build-command "(progn (cl:load %S) %s (cl-user::finish-output t) (sb-ext:exit))"
                                specware4-loader
                                (specware-build-eval-emacs-str "(specware-build %s t '%s)"
                                                               in-current-dir?
                                                               (or continuation? t))))))
    )

(defvar saving-lisp-image-regexp "\\[saving current Lisp image into ")

(defun run-specware-after-saving-lisp-image (output)
  (when (string-match saving-lisp-image-regexp output)
    (sit-for 2)
    (run-specware4))
  output)

(defun bootstrap-specware4-and-then-exit (&optional in-current-dir?)
  (interactive "P")
  (bootstrap-specware4 in-current-dir? t))

(defun bootstrap-specware4 (&optional in-current-dir? auto-exit?)
  (interactive "P")
  (if (and (eq *specware-lisp* 'sbcl) (eq lisp-emacs-interface-type 'slime))
      (specware-boot in-current-dir?)
    (let ((*specware4-dir (sw::normalize-filename
			(if in-current-dir? (strip-final-slash default-directory)
			  (concat (getenv "SPECWARE4"))))))
    (run-specware4 *specware4-dir)
    (sit-for 1)
    (eval-in-lisp-in-order
     (format "(cl:namestring (Specware::change-directory %S))" *specware4-dir))
;    (eval-in-lisp-in-order (format "(Specware::setenv \"SWPATH\" %S)"
;				   (concat (sw::normalize-filename *specware4-dir))))
    (eval-in-lisp-in-order (format "(Specware::setenv \"SPECWARE4\" %S)"
				      (sw::normalize-filename *specware4-dir)))
    (eval-in-lisp-in-order "(progn #+allegro(sys::set-stack-cushion 10000000)
                                   #-allegro())")
    (eval-in-lisp-in-order "(cl:time (cl-user::boot))")
    (sit-for 1)
    (continue-form-when-ready
     ;; continue-form-when-ready kills the sublisp process,
     ;; then waits for a status change signal on that process
     ;; before processing the given command
     `(build-specware4 ,*specware4-dir ,auto-exit?)))))


(defun test-specware-bootstrap (in-current-dir?)
  (interactive "P")
  (let ((current-dir default-directory))
    (if (not (inferior-lisp-running-p))
	(message "Do M-x bootstrap-specware first")
      (progn (shell-command (concat "cd "
                                    (if in-current-dir? current-dir
                                      *specware-home-directory*)
                                    "; /bin/rm */sig/*.sig"))
	     (sit-for 1)		; Necessary? Enough?
	     (eval-in-lisp-in-order "(Bootstrap-Spec::compileBootstrap)")
	     (eval-in-lisp-in-order ":exit")
	     (sit-for 1)
	     (while (inferior-lisp-running-p)
	       (sit-for 1))
	     (run-plain-lisp 1)
	     (eval-in-lisp-in-order "(cl:load \"load.lisp\")")
	     (eval-in-lisp-in-order "(Bootstrap-Spec::compileAll)")))))

(defun strip-final-slash (dirname)
  (let ((len (length dirname)))
    (if (equal ?/ (elt dirname (- len 1)))
	(substring dirname 0 (- len 1))
      (if (equal ?\\ (elt dirname (- len 1)))
	(substring dirname 0 (- len 1))
        dirname))))


(provide 'sw-init)
