
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

;;; Make listener commands bound to same keys as comint
(defun add-comint-key-bindings (m)
  (define-key m "\en" 'fi:push-input)
  (define-key m "\ep" 'fi:pop-input)
  (define-key m '(control meta y) 'fi:pop-input)
  (define-key m "\er" 'fi:re-search-backward-input)
  (define-key m "\es" 'fi:re-search-forward-input)
  (define-key m "\e." 'slang-meta-point)
  (define-key m "\e*" 'switch-to-lisp))

(defun cleanup-fi:lisp-listener-mode ()
  (and fi:lisp-listener-mode-map
       (add-comint-key-bindings fi:lisp-listener-mode-map))
  (and fi:inferior-common-lisp-mode-map
       (add-comint-key-bindings fi:inferior-common-lisp-mode-map)))

(if (and (boundp 'fi:inferior-common-lisp-mode-map)
	 fi:inferior-common-lisp-mode-map)
    (cleanup-fi:lisp-listener-mode)
  (add-hook 'fi:inferior-common-lisp-mode-hook 'cleanup-fi:lisp-listener-mode))

(if (and (boundp 'fi:lisp-listener-mode-map)
	 fi:lisp-listener-mode-map)
    (cleanup-fi:lisp-listener-mode)
  (add-hook 'fi:lisp-listener-mode-hook 'cleanup-fi:lisp-listener-mode))
