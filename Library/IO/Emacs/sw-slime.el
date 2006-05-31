(require 'slime)

;;; Based on slime-repl-mode
(defvar specware-listener-mode-map)

(setq specware-listener-mode-map (make-sparse-keymap))
(set-keymap-parent specware-listener-mode-map slime-repl-mode-map)

(defun add-specware-listener-key-bindings (m)
					;(define-key m '(tab) 'comint-dynamic-complete)
  (define-key m "\e." 'sw:meta-point)
					;(define-key m "\C-c\C-d" 'ild-abort)
  (easy-menu-define specware-interaction-buffer-menu
		    m
		    "Menu used in Specware buffer."
		    specware-interaction-menu)
  (easy-menu-add specware-interaction-buffer-menu m))

(add-specware-listener-key-bindings specware-listener-mode-map)


(slime-define-keys specware-listener-mode-map
  ("\C-m" 'sw-return)
 ; ("\C-j" 'slime-repl-newline-and-indent)
;  ("\C-\M-m" 'slime-repl-closing-return)
;  ([(control return)] 'slime-repl-closing-return)
;  ("\C-a" 'slime-repl-bol)
;  ([home] 'slime-repl-bol)
;  ("\C-e" 'slime-repl-eol)
;  ("\M-p" 'slime-repl-previous-input)
;  ((kbd "C-<up>") 'slime-repl-previous-input)
;  ("\M-n" 'slime-repl-next-input)
;  ((kbd "C-<down>") 'slime-repl-next-input)
;  ("\M-r" 'slime-repl-previous-matching-input)
;  ("\M-s" 'slime-repl-next-matching-input)
;  ("\C-c\C-c" 'slime-interrupt)
;  ("\C-c\C-b" 'slime-interrupt)
;  ("\C-c:"    'slime-interactive-eval)
;  ("\C-c\C-e" 'slime-interactive-eval)
;  ("\C-cE"     'slime-edit-value)
;  ;("\t"   'slime-complete-symbol)
;  ("\t"   'slime-indent-and-complete-symbol)
;  (" "    'slime-space)
;  ("\C-c\C-d" slime-doc-map)
;  ("\C-c\C-w" slime-who-map)
;  ("\C-\M-x" 'slime-eval-defun)
;  ("\C-c\C-o" 'slime-repl-clear-output)
;  ("\C-c\C-t" 'slime-repl-clear-buffer)
;  ("\C-c\C-u" 'slime-repl-kill-input)
;  ("\C-c\C-n" 'slime-repl-next-prompt)
;  ("\C-c\C-p" 'slime-repl-previous-prompt)
;  ("\M-\C-a" 'slime-repl-beginning-of-defun)
;  ("\M-\C-e" 'slime-repl-end-of-defun)
;  ("\C-c\C-l" 'slime-load-file)
;  ("\C-c\C-k" 'slime-compile-and-load-file)
;  ("\C-c\C-z" 'slime-nop)
)

;;; based on slime-repl-return
(defun sw-return (&optional end-of-input)
  "Evaluate the current input string, or insert a newline.  
Send the current input ony if a whole expression has been entered,
i.e. the parenthesis are matched. 

With prefix argument send the input even if the parenthesis are not
balanced."
  (interactive "P")
  (slime-check-connected)
  (assert (<= (point) slime-repl-input-end-mark))
  (cond (end-of-input
         (sw-send-input))
        (slime-repl-read-mode ; bad style?
         (sw-send-input t))
        ((and (get-text-property (point) 'slime-repl-old-input)
              (< (point) slime-repl-input-start-mark))
         (slime-repl-grab-old-input end-of-input)
         (slime-repl-recenter-if-needed))
        ((and (car (slime-presentation-around-or-before-point (point)))
                   (< (point) slime-repl-input-start-mark))
         (slime-repl-grab-old-output end-of-input)
         (slime-repl-recenter-if-needed))
        ((slime-input-complete-p slime-repl-input-start-mark 
                                 slime-repl-input-end-mark)
         (sw-send-input t))
        (t 
         (slime-repl-newline-and-indent)
         (message "[input not complete]"))))

;; Based on slime-repl-send-input
(defun sw-send-input (&optional newline)
  "Goto to the end of the input and send the current input.
If NEWLINE is true then add a newline at the end of the input."
  (when (< (point) slime-repl-input-start-mark)
    (error "No input at point."))
  (goto-char slime-repl-input-end-mark)
  (let ((end (point))) ; end of input, without the newline
    (when newline 
      (insert "\n")
      (slime-repl-show-maximum-output))
    (let ((inhibit-read-only t))
      (add-text-properties slime-repl-input-start-mark 
                           (point)
                           `(slime-repl-old-input
                             ,(incf slime-repl-old-input-counter))))
    (let ((overlay (make-overlay slime-repl-input-start-mark end)))
      ;; These properties are on an overlay so that they won't be taken
      ;; by kill/yank.
      (overlay-put overlay 'read-only t)
      (overlay-put overlay 'face 'slime-repl-input-face)))
  (slime-repl-add-to-input-history 
   (buffer-substring slime-repl-input-start-mark
                     slime-repl-input-end-mark)) 

  (let* ((input (slime-repl-current-input))
	 (input (if specware-use-x-symbol
		    (x-symbol-encode-string input (current-buffer))
		  input))
	 (input (sw-input-to-command input)))
    (goto-char slime-repl-input-end-mark)
    (slime-mark-input-start)
    (slime-mark-output-start)
    (if (eq input :exit)
	(slime-quit-specware)
      (slime-repl-send-string input))))


(defun slime-quit-specware (&optional keep-buffers)
  "Quit lisp, kill the inferior process and associated buffers."
  (interactive)
  (slime-eval-async '(swank:quit-lisp))
  ;(kill-buffer (slime-output-buffer))
  (set-process-filter (slime-connection) nil)
  (set-process-sentinel (slime-connection) 'slime-quit-specware-sentinel))

(defun slime-quit-specware-sentinel (process message)
  (assert (process-status process) 'closed)
  (let* ((inferior (slime-inferior-process process))
         ;(inferior-buffer (if inferior (process-buffer inferior)))
	 )
    (when inferior (delete-process inferior))
    ;(when inferior-buffer (kill-buffer inferior-buffer))
    (slime-net-close process)
    (message "Connection closed.")
    (continue-emacs-computation process message)))

(defvar sw:*shell-command-function* "SWShell::process-raw-command")

(defun sw-input-to-command (input)
  (let ((input (strip-extra-whitespace input)))
    (if (eq (elt input 0) ?\()
	input
      (let* ((ws (or (position ?\  input) (position ?\n  input)))
	     (command (if ws (substring input 0 ws) input))
	     (argstr  (if ws (substring input (1+ ws)) nil)))
	(if (member command '("quit" "QUIT" "exit" "EXIT" "ok" "OK"
			      ":quit" ":QUIT" ":exit" ":EXIT" ":ok" ":OK"))
	    ':exit
	  (if (equal command "")
	      command
	    (format "(%s '%s %S)" sw:*shell-command-function* command argstr)))))))

(defun strip-extra-whitespace (s)
  (let ((first-non-ws-pos (string-match "[^ \t\n]" s))
	(end-pos (string-match "[ \t\n]*\\'" s)))
    (if first-non-ws-pos
	(substring s first-non-ws-pos end-pos)
      s)))

(defun specware-listener-mode-init ()
  (when specware-use-x-symbol
    (x-symbol-mode))
  (setq slime-words-of-encouragement
	'("Welcome to Specware!")))

(add-hook 'specware-listener-mode-hook
	  'specware-listener-mode-init)

(defun specware-listener-mode () 
  "Major mode for Specware Shell."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'specware-listener-mode)
  (set (make-local-variable 'specware-listener-p) t)
  (use-local-map specware-listener-mode-map)
  (lisp-mode-variables t)
  (setq slime-buffer-package "CL-USER")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (setq font-lock-defaults nil)
  (setq mode-name "SW")
  (setq slime-current-thread :repl-thread)
  (set (make-local-variable 'scroll-conservatively) 20)
  (set (make-local-variable 'scroll-margin) 0)
  (slime-repl-safe-load-history)
  (make-local-hook 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook 'slime-repl-safe-save-merged-history nil t)
  (add-hook 'kill-emacs-hook 'slime-repl-save-all-histories)
  (slime-setup-command-hooks)
  (when slime-use-autodoc-mode 
    (slime-autodoc-mode 1))
  (run-hooks 'slime-repl-mode-hook)
  (run-hooks 'specware-listener-mode-hook))

;;; Redefining slime functions and variables
(defvar specware-listener-p nil)

(defvar old-slime-output-buffer (symbol-function 'slime-output-buffer))

(defun slime-output-buffer (&optional noprompt)
  "Return the output buffer, create it if necessary."
  (if (not specware-listener-p)
      (funcall old-slime-output-buffer noprompt)
    (let ((buffer (slime-connection-output-buffer)))
      (or (if (buffer-live-p buffer) buffer)
	  (setf (slime-connection-output-buffer)
		(let ((connection (slime-connection)))
		  (with-current-buffer (sw-slime-repl-buffer t connection)
		    (unless (eq major-mode 'specware-listener-mode) 
		      (specware-listener-mode))
		    (setq slime-buffer-connection connection)
		    (slime-reset-repl-markers)
		    (unless noprompt 
		      (slime-repl-insert-prompt '(;:suppress-output
						  )
						0))
		    (current-buffer))))))))

(defun sw-slime-repl-buffer (&optional create connection)
  "Get the REPL buffer for the current connection; optionally create."
  (funcall (if create #'get-buffer-create #'get-buffer)
           sw:common-lisp-buffer-name))

(defvar old-slime-repl-insert-prompt (symbol-function 'slime-repl-insert-prompt))

(defvar *sw-after-prompt-forms* nil)

(defun slime-repl-insert-prompt (result &optional time)
  "Goto to point max, insert RESULT and the prompt.
Set slime-output-end to start of the inserted text slime-input-start
to end end."
  (if (not specware-listener-p)
      (funcall old-slime-repl-insert-prompt result time)  
    (progn
      (goto-char (point-max))
      (let ((start (point)))
	(unless (bolp) (insert "\n"))
	(slime-repl-insert-result result)
	(let ((prompt-start (point))
	      (prompt (format "* ")))
	  (slime-propertize-region
	      '(face slime-repl-prompt-face read-only t intangible t
		     slime-repl-prompt t
		     ;; emacs stuff
		     rear-nonsticky (slime-repl-prompt read-only face intangible)
		     ;; xemacs stuff
		     start-open t end-open t)
	    (insert prompt))
	  ;; FIXME: we could also set beginning-of-defun-function
	  (setq defun-prompt-regexp (concat "^" prompt))
	  (set-marker slime-output-end start)
	  (set-marker slime-repl-prompt-start-mark prompt-start)
	  (slime-mark-input-start)
	  (while (not (null *sw-after-prompt-forms*))
	    (eval (pop *sw-after-prompt-forms*)))
	  (let ((time (or time 0.2)))
	    (cond ((zerop time)
		   (slime-repl-move-output-mark-before-prompt (current-buffer)))
		  (t 
		   (run-at-time time nil 'slime-repl-move-output-mark-before-prompt
				(current-buffer)))))))
      (slime-repl-show-maximum-output))))



;;; Mods to slime.el
(defun slime-write-string (string)
  (with-current-buffer (slime-output-buffer)
    (slime-with-output-end-mark
     (slime-propertize-region '(face slime-repl-output-face)
       (let ((start (point)))
	  (insert string)
	  (x-symbol-decode-region start (point))))
     (when (and (= (point) slime-repl-prompt-start-mark)
                (not (bolp)))
       (insert "\n")
       (set-marker slime-output-end (1- (point)))))))

(defun slime-repl-show-maximum-output (&optional force)
  "Put the end of the buffer at the bottom of the window."
  ;; Don't know about this assert
  ;;(assert (eobp))
  (let ((win (get-buffer-window (current-buffer))))
    (when (and win (or force (not (pos-visible-in-window-p))))
      (save-selected-window
        (save-excursion
          (select-window win)
          (goto-char (point-max))
          (recenter -1))))))


(defface slime-repl-output-face
  (if (slime-face-inheritance-possible-p)
      '((t (:inherit font-lock-string-face)))
  ;; sjw: RosyBrown --> DarkBrown as was too light
    '((((class color) (background light)) (:foreground "DarkBrown"))
      (((class color) (background dark)) (:foreground "LightSalmon"))
      (t (:slant italic))))
  "Face for Lisp output in the SLIME REPL."
  :group 'slime-repl)


(defun slime-repl-update-banner ()
  (let* ((banner (format "%s  Port: %s  Pid: %s
; Specware %s"
                         (slime-lisp-implementation-type)
                         (slime-connection-port (slime-connection))
                         (slime-pid)
			 (sw:eval-in-lisp "(if (boundp 'Specware-version) Specware-version \"\")")))
         ;; Emacs21 has the fancy persistent header-line.
         (use-header-p (and slime-header-line-p
                            (boundp 'header-line-format)))
         ;; and dancing text
         (animantep (and (fboundp 'animate-string)
                         slime-startup-animation
                         (zerop (buffer-size)))))
    (when use-header-p
      (setq header-line-format banner))
    (when animantep
      (pop-to-buffer (current-buffer))
      (animate-string (format "; SLIME %s" (or (slime-changelog-date) 
                                               "- ChangeLog file not found"))
                      0 0))
    (slime-repl-insert-prompt (cond (use-header-p `(:suppress-output))
                                    (t `(:values (,(concat "; " banner))))))))

(defun slime-check-connected ()
  "Signal an error if we are not connected to Lisp."
  (unless (slime-connected-p)
    (error "Not connected. Use `%s' to start Specware."
	   ;; sjw: was slime
           (substitute-command-keys "\\[run-specware4]"))))

(defun slime-dispatch-event (event &optional process)
  (let ((slime-dispatching-connection (or process (slime-connection))))
    (destructure-case event
      ((:write-string output)
       (slime-write-string output))
      ((:presentation-start id)
       (slime-mark-presentation-start id))
      ((:presentation-end id)
       (slime-mark-presentation-end id))
      ;;
      ((:emacs-rex form package thread continuation)
       (slime-set-state "|eval...")
       (when (and (slime-use-sigint-for-interrupt) (slime-busy-p))
         (message "; pipelined request... %S" form))
       (let ((id (incf (slime-continuation-counter))))
         (push (cons id continuation) (slime-rex-continuations))
         (slime-send `(:emacs-rex ,form ,package ,thread ,id))))
      ((:return value id)
       (let ((rec (assq id (slime-rex-continuations))))
         (cond (rec (setf (slime-rex-continuations)
                          (remove rec (slime-rex-continuations)))
                    (when (null (slime-rex-continuations))
                      (slime-set-state ""))
                    (funcall (cdr rec) value))
               (t
                (error "Unexpected reply: %S %S" id value)))))
      ((:debug-activate thread level)
       (assert thread)
       (sldb-activate thread level))
      ((:debug thread level condition restarts frames conts)
       (assert thread)
       (sldb-setup thread level condition restarts frames conts))
      ((:debug-return thread level stepping)
       (assert thread)
       (sldb-exit thread level stepping))
      ((:emacs-interrupt thread)
       (cond ((slime-use-sigint-for-interrupt) (slime-send-sigint))
             (t (slime-send `(:emacs-interrupt ,thread)))))
      ((:read-string thread tag)
       (assert thread)
       (slime-repl-read-string thread tag))
      ((:y-or-n-p thread tag question)
       (slime-y-or-n-p thread tag question))
      ((:read-aborted thread tag)
       (assert thread)
       (slime-repl-abort-read thread tag))
      ((:emacs-return-string thread tag string)
       (slime-send `(:emacs-return-string ,thread ,tag ,string)))
      ;;
      ((:new-package package prompt-string)
       (setf (slime-lisp-package) package)
       (setf (slime-lisp-package-prompt-string) prompt-string))
      ((:new-features features)
       (setf (slime-lisp-features) features))
      ((:indentation-update info)
       (slime-handle-indentation-update info))
      ((:open-dedicated-output-stream port)
       (slime-open-stream-to-lisp port))
      ((:eval-no-wait form-string)
       (slime-check-eval-in-emacs-enabled)
       (message form-string)
       (eval (read form-string))
       ;(apply (intern fun) args) : sjw: was this a bug?
       )
      ((:eval thread tag form-string)
       (slime-eval-for-lisp thread tag form-string))
      ((:emacs-return thread tag value)
       (slime-send `(:emacs-return ,thread ,tag ,value)))
      ((:ed what)
       (slime-ed what))
      ((:background-message message)
       (slime-background-message "%s" message))
      ((:debug-condition thread message)
       (assert thread)
       (message "%s" message)))))

(provide 'sw-slime)