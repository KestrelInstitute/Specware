
;;; Changes to the Franz Emacs Lisp Interface

;; From fi-utils.el :

(defun fi:note (format-string &rest args)
  (let ((string (apply 'format format-string args)))
    (delete-other-windows)
    (fi::switch-to-buffer "*Help*")
    (erase-buffer)
    (insert string)
    ;; nsb: add this message:
    (message (format "Error : %s" string))
    (beginning-of-buffer)))

;; From fi-lep.el :

(defun fi:bug-report ()
  "Create a mail buffer which contains information about the Common Lisp
environment in which the bug occurs.  A :zoom and other related information
is obtained from the \"Initial Lisp Listener\".  See M-x mail for more
information on how to send the mail."
  (interactive)
  (fi::make-request
      (lep::bug-report-session
       :process-name
       (fi::read-lisp-process-name "Process for stack :zoom: "))
    ;; Normal continuation
    (() (error-message stack lisp-info)
      (mail)
      (mail-to)
      (insert "bugs@franz.com")
      ;;(mail-subject)
      ;;(insert "Bug-report")
      (goto-char (point-max))
      (save-excursion
	(insert "\n")
	(when (and error-message (not (string= "" error-message)))
	  (insert "------------------------------\n\n")
	  (insert error-message))
        (insert "<<Please enter any comments or explanations here>>\n\n")
	(insert "\n------------------------------\n\n")
	(insert stack)
	(insert "\n------------------------------\n\n")
	(insert lisp-info)
	(insert "\n------------------------------\n\n")

	;;	(insert (format "Emacs version: %s\n"
	;;			(emacs-version)))
	;; Fix for Xemacs version 21
	;; nsb Thu Jul 20 13:22:40 PDT 2000
	(insert (format "Emacs version: %s\n"
			emacs-version))
	
	(insert (format "Emacs-Lisp interface version: %s\n\n"
			fi:emacs-lisp-interface-version))
	(insert (format "load-path: %s\n\n" load-path))
	(let* ((file (fi::find-path load-path "fi-site-init.el"))
	       (dir (when file
		      (file-name-directory file))))
	  (if dir
	      (progn
		(insert (format "Contents of %s directory:\n" dir))
		(call-process "ls" nil t nil "-la"
			      (expand-file-name dir))
		(insert "\n"))
	    (insert (format "Could not find fi-site-init.el\n")))
	  (insert "\n")))
      (message "Please enter a descriptive Subject: line")
      (mail-subject))
    ;; Error continuation
    (() (error)
      (fi::show-error-text "Cannot do a backtrace because: %s" error))))

;; This wasn't byte compiled in our ACL directory.
;; The call to remove ?\" seems to be missing!
;; From fi-basic-lep.el :

;;;(defun fi::make-connection-to-lisp (host port passwd ipc-version)
;;;  (cond ((eq ipc-version fi::required-ipc-version)
;;;	 (let* ((proc-name (format "*LEP %s %d %d*" host port passwd))
;;;		(buffer-name proc-name)
;;;		(buffer (when buffer-name
;;;			  (get-buffer-create buffer-name)))
;;;		(process (fi::open-network-stream proc-name nil host port)))
;;;	   (when buffer
;;;	     (bury-buffer buffer)
;;;	     (save-excursion (set-buffer buffer) (erase-buffer))
;;;	     (set-process-buffer process buffer))
;;;	   (set-process-filter process 'fi::lep-connection-filter)
;;;	   ;; new stuff to indicate that we want the lisp editor protocol
;;;	   (process-send-string process ":lep\n")
;;;	   (process-send-string process (format "\"%s\"\n" proc-name))
;;;	   (process-send-string process (format "%d \n" passwd))
;;;	   ;; Send the class of the editor to the lisp.
;;;	   ;; This might affect something!
;;;	   ;; For example, gnu 19 has some good features.
;;;	   (process-send-string
;;;	    process
;;;	    (format "\"%s\"\n"
;;;;;;; The following works in xemacs 20.x when this file is compiled
;;;;;;; with emacs 19.x, but we don't want to install this hack since
;;;;;;; there are hundreds of other places a similar hack would have to
;;;;;;; be installed.
;;;		    ;;(remove (aref "\"" 0) (emacs-version))
;;;		    (remove ?\" (emacs-version))
;;;		    ))
;;;	   (prog1
;;;	       (setq fi::*connection*
;;;		 (fi::make-connection (current-buffer) host process))
;;;	     (set-menubar-dirty-flag))))
;;;	(t
;;;	 (fi:error
;;;	  "
;;;The Allegro CL ipc version is ``%s'' (from the variable excl::*ipc-version*
;;;in the Lisp environment).  This version of the emacs-lisp interface
;;;requires version ``%s''.  This mismatch would most likely be caused by the
;;;Emacs and Lisp not being from the same distribution.  If the obtained ipc
;;;version is `nil', then it is most likely you are using the emacs-lisp
;;;interface from ACL 4.1 or later with an older Lisp.
;;;
;;;See lisp/fi/examples/emacs.el for code to correctly startup different
;;;versions of the emacs-lisp interface.
;;;"
;;;	  ipc-version fi::required-ipc-version))))

(defvar *allegro-prompt-regexp*
  "^\\(\\(\\[[0-9]+i?c?\\] \\|\\[step\\] \\)?\\(<?[-A-Za-z]* ?[0-9]*?>\\|[-A-Za-z0-9]+([0-9]+):\\) \\)+")

(defun simple-scan-works ()
  (while (and (not (eobp))
	      (not (or (looking-at "(")
		       (looking-at "\""))))
    (forward-char 1))
  (eobp))

(defun fi:inferior-lisp-newline ()
  "When at the end of the buffer, insert a newline into a Lisp subprocess
buffer, and if a complete form has been entered, send the input to the Lisp
subprocess.  This allows partially complete, multi-line expressions to be
edited before Lisp sees them.

If not at the end of the buffer, this function does its best to find a
complete form around the point, copy it to the end of the buffer, and send
it to the Lisp subprocess."
  (interactive)
  (if (eobp)
      (let ((start (marker-position
		    (process-mark (get-buffer-process (current-buffer)))))
	    (send-that-sexp t))
	(goto-char start)
	(while (and (not (eobp))
		    (condition-case ()
			(progn (forward-sexp 1) t)
		      (error (or (simple-scan-works)
				 (setq send-that-sexp nil)))))
	  (while (looking-at ")")
	    ;; Can either signal an error or delete them silently.  Hmm,
	    ;; for now we'll signal the error:
	    ;;(delete-char 1)
	    (error "too many )'s")
	    ))
	(goto-char (point-max))
	(if send-that-sexp
	    (fi:subprocess-send-input)
	  (progn
	    (newline)
	    (funcall indent-line-function))))

    ;;NOT AT THE END OF THE BUFFER!
    ;; find the user's input contained around the cursor and send that to
    ;; the inferior lisp
    (let ((start-of-last-prompt
	   (save-excursion
	     (or (and (re-search-backward fi::prompt-pattern nil t)
		      (point))
		 (point-max))))
	  start end)
      (if (or (and (bolp) (looking-at "("))
	      (re-search-backward "^(" start-of-last-prompt t)
	      (prog1 (re-search-backward fi::prompt-pattern nil t)
		(goto-char (match-end 0))))
	  (progn
	    (setq start (point))
	    (let* ((eol (save-excursion (end-of-line) (point)))
		   (state (save-excursion (parse-partial-sexp start eol)))
		   (depth (car state)))
	      (if (zerop depth)
		  (setq end eol)
		(setq end
		  (condition-case ()
		      (save-excursion
			(if (< depth 0)
			    (up-list (- depth))
			  (goto-char eol)
			  (up-list depth))
			(point))
		    (error nil))))

	      (if (or (null end) (= end (point-max)))
		  (progn
		    (goto-char (point-max))
		    (fi:inferior-lisp-newline))
		(fi:subprocess-input-region start end))))
	(error "couldn't find start of input")))))

;;; Make listener commands bound to same keys as comint
(defun add-specware-listener-key-bindings (m)
  (define-key m "\en" 'fi:push-input)
  (define-key m "\ep" 'fi:pop-input)
  (define-key m '(control meta y) 'fi:pop-input)
  (define-key m "\er" 'fi:re-search-backward-input)
  (define-key m "\es" 'fi:re-search-forward-input)
  (define-key m "\e." 'sw:meta-point)
  (define-key m "\e*" 'sw:switch-to-lisp)
  (define-key m '(tab) 'comint-dynamic-complete)
  (setq comint-prompt-regexp *allegro-prompt-regexp*)
  (define-key m "\C-a" 'comint-bol)
  (autoload 'comint-bol "comint" "\
Beginning of line; skip prompt." t nil)
  (easy-menu-define specware-interaction-buffer-menu
		    m
		    "Menu used in Specware buffer."
		    specware-interaction-menu)
  (easy-menu-add specware-interaction-buffer-menu m))

(defun cleanup-fi:lisp-listener-mode ()
  (setq comint-input-ring-size 100)
  (and fi:lisp-listener-mode-map
       (add-specware-listener-key-bindings fi:lisp-listener-mode-map))
  (and fi:inferior-common-lisp-mode-map
       (add-specware-listener-key-bindings fi:inferior-common-lisp-mode-map)))

(if (and (boundp 'fi:inferior-common-lisp-mode-map)
	 fi:inferior-common-lisp-mode-map)
    (cleanup-fi:lisp-listener-mode)
  (add-hook 'fi:inferior-common-lisp-mode-hook 'cleanup-fi:lisp-listener-mode))

(if (and (boundp 'fi:lisp-listener-mode-map)
	 fi:lisp-listener-mode-map)
    (cleanup-fi:lisp-listener-mode)
  (add-hook 'fi:lisp-listener-mode-hook 'cleanup-fi:lisp-listener-mode))
