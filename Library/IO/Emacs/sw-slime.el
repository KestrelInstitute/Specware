(require 'slime)
(require 'slime-repl)

;;; Based on slime-repl-mode
(defvar specware-listener-mode-map)

(setq specware-listener-mode-map (make-sparse-keymap))
(set-keymap-parent specware-listener-mode-map slime-repl-mode-map)

(defun add-specware-listener-key-bindings (m)
					;(define-key m '(tab) 'comint-dynamic-complete)
  (define-key m "\e."      'sw:meta-point)
  (define-key m "\C-cfc"   'sw:find-case-dispatch-on-type)
  (define-key m "\C-cfr"   'sw:find-op-references)
					;(define-key m "\C-c\C-d" 'ild-abort)
  (easy-menu-define specware-interaction-buffer-menu
		    m
		    "Menu used in Specware buffer."
		    specware-interaction-menu)
  (easy-menu-add specware-interaction-buffer-menu m))

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

;;; Based on slime-init-command -- Allow for pre-loaded swank
(defun slime-cond-init-command (port-filename coding-system)
  "Return a string to initialize Lisp."
  (let ((loader (if (file-name-absolute-p slime-backend)
                    slime-backend
                  (concat slime-path slime-backend)))
        (encoding (slime-coding-system-cl-name coding-system)))
    (format "(progn %S\n%S\n%S\n%S\n%S)\n\n"
            `(unless (and (find-package "SWANK") 
			  (fboundp (intern "START-SERVER" "SWANK")))
	       (load ,(slime-to-lisp-filename (expand-file-name loader)) :verbose t))
	    `(unless (find-package :Specware) 
	       (defpackage :Specware (:use "CL")))
	    `(set (intern "*USING-SLIME-INTERFACE?*" :Specware) t)
            `(funcall (read-from-string "swank-loader:init"))
            `(funcall (read-from-string "swank:start-server")
                        ,(slime-to-lisp-filename port-filename)
                        :coding-system ,encoding))))

;;; based on slime-repl-return
(defun sw-return (&optional end-of-input)
  "Evaluate the current input string, or insert a newline.  
Send the current input ony if a whole expression has been entered,
i.e. the parenthesis are matched. 

With prefix argument send the input even if the parenthesis are not
balanced."
  (interactive "P")
  (slime-check-connected)
  (cond (end-of-input
         (sw-send-input))
        (slime-repl-read-mode ; bad style?
         (sw-send-input t))
        ((and (get-text-property (point) 'slime-repl-old-input)
              (< (point) slime-repl-input-start-mark))
         (slime-repl-grab-old-input end-of-input)
         (slime-repl-recenter-if-needed))
        ((run-hook-with-args-until-success 'slime-repl-return-hooks))
        ((slime-input-complete-p slime-repl-input-start-mark (point-max))
         (sw-send-input t))
        (t 
         (slime-repl-newline-and-indent)
         (message "[input not complete]"))))

(defcustom sw:input-read-only nil
  "If non-nil then make input read-only"
  :type 'boolean
  :group 'specware)

;; Based on slime-repl-send-input
(defun sw-send-input (&optional newline)
  "Goto to the end of the input and send the current input.
If NEWLINE is true then add a newline at the end of the input."
  (unless (slime-repl-in-input-area-p)
    (error "No input at point."))
  (goto-char (point-max))
  (let ((end (point))) ; end of input, without the newline
    (slime-repl-add-to-input-history 
     (buffer-substring slime-repl-input-start-mark end))
    (when newline 
      (insert "\n")
      (slime-repl-show-maximum-output))
    (let ((inhibit-modification-hooks t))
      (add-text-properties slime-repl-input-start-mark 
                           (point)
                           `(slime-repl-old-input
                             ,(incf slime-repl-old-input-counter))))
    (let ((overlay (make-overlay slime-repl-input-start-mark end)))
      ;; These properties are on an overlay so that they won't be taken
      ;; by kill/yank.
      (when sw:input-read-only
        (overlay-put overlay 'read-only t))
      (overlay-put overlay 'face 'slime-repl-input-face)))
  (let* ((input (slime-repl-current-input))
	 (input (if sw:use-x-symbol
		    (x-symbol-encode-string input (current-buffer))
		  input))
	 (input (sw-input-to-command input)))
    (goto-char (point-max))
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
	(if (member command '("quit" "QUIT" "exit" "EXIT" ":quit" ":QUIT" ":exit" ":EXIT"))
	    ':exit
	  (if (equal command "")
	      command
	    (format "(%s '%s %S)\n" sw:*shell-command-function* command argstr)))))))

(defun strip-extra-whitespace (s)
  (let ((first-non-ws-pos (string-match "[^ \t\n]" s))
	(end-pos (string-match "[ \t\n]*\\'" s)))
    (if first-non-ws-pos
	(substring s first-non-ws-pos end-pos)
      s)))

(defun specware-listener-mode-init ()
  (when sw:use-x-symbol
    (x-symbol-mode))
  (setq slime-words-of-encouragement
	'("Welcome to Specware!"))
  (add-specware-listener-key-bindings specware-listener-mode-map))

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
  (when (and (boundp 'slime-use-autodoc-mode) slime-use-autodoc-mode)
    (slime-autodoc-mode 1))
  (setq default-directory (concat *specware* "/"))
  (run-hooks 'slime-repl-mode-hook)
  (run-hooks 'specware-listener-mode-hook))

;;; Redefining slime functions and variables
(defun* slime-start (&key (program inferior-lisp-program) program-args
                          directory
                          (coding-system slime-net-coding-system)
                          (init 'slime-cond-init-command)
                          name
                          (buffer "*inferior-lisp*")
                          init-function
                          env)
  (if (and (eq *specware-lisp* 'allegro) *windows-system-p*)
      (slime-allegro-windows program program-args)
    (let ((args (list :program program :program-args program-args :buffer buffer 
                      :coding-system coding-system :init init :name name
                      :init-function init-function :env env)))
      (slime-check-coding-system coding-system)
      (when (slime-bytecode-stale-p)
        (slime-urge-bytecode-recompile))
      (let ((proc (slime-maybe-start-lisp program program-args env
                                          directory buffer)))
        (slime-inferior-connect proc args)
        (pop-to-buffer (process-buffer proc))))))

(defun slime-allegro-windows (program program-args)
  (let ((slime-port 4005))
    (let ((cmd
	   (format "%s +B %s -L %s/Library/IO/Emacs/load-slime.lisp&"
		   program
		   (apply 'concat (loop for arg in program-args append (list " " arg)))
		   (getenv "SPECWARE4")
		   ;;slime-port
		   )))
      (shell-command (sw::normalize-filename cmd)))
    ;;(delete-other-windows)
    (while (not (ignore-errors (slime-connect "localhost" slime-port)))
      (sleep-for 0.2))
    (slime-eval-async '(setq Specware::*using-slime-interface?* t))))

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
		      (slime-repl-insert-prompt))
		    (current-buffer))))))))

(defun sw-slime-repl-buffer (&optional create connection)
  "Get the REPL buffer for the current connection; optionally create."
  (funcall (if create #'get-buffer-create #'get-buffer)
           sw:common-lisp-buffer-name))

(defvar old-slime-repl-insert-prompt (symbol-function 'slime-repl-insert-prompt))

(defvar *sw-after-prompt-forms* nil)
(defvar *sw-slime-prompt* "* ")

(defun slime-repl-insert-prompt ()
  "Goto to point max, insert RESULT and the prompt.
Set slime-output-end to start of the inserted text slime-input-start
to end end."
  (if (not specware-listener-p)
      (funcall old-slime-repl-insert-prompt)  
    (progn
      (goto-char slime-repl-input-start-mark)
  (slime-save-marker slime-output-start
    (slime-save-marker slime-output-end
      (unless (bolp) (insert-before-markers "\n"))
      (let ((prompt-start (point)))
        (slime-propertize-region
            '(face slime-repl-prompt-face read-only t intangible t
                   slime-repl-prompt t
                   ;; emacs stuff
                   rear-nonsticky (slime-repl-prompt read-only face intangible)
                   ;; xemacs stuff
                   start-open t end-open t)
          (insert-before-markers *sw-slime-prompt*))
        (set-marker slime-repl-prompt-start-mark prompt-start)
        (while (not (null *sw-after-prompt-forms*))
	    (eval (pop *sw-after-prompt-forms*)))
        prompt-start))))))



;;; Mods to slime.el and slime-repl.el
(defun slime-repl-emit (string)
  ;; insert the string STRING in the output buffer
  (with-current-buffer (slime-output-buffer)
    (save-excursion
      (goto-char slime-output-end)
      (slime-save-marker slime-output-start
        (slime-propertize-region '(face slime-repl-output-face 
                                        rear-nonsticky (face))
          (insert-before-markers string)
          (when sw:use-x-symbol
	    (x-symbol-decode-region slime-output-start (point)))
          (when (and (= (point) slime-repl-prompt-start-mark)
                     (not (bolp)))
            (insert-before-markers "\n")
            (set-marker slime-output-end (1- (point)))))))
    (when slime-repl-popup-on-output
      (setq slime-repl-popup-on-output nil)
      (display-buffer (current-buffer)))
    (slime-repl-show-maximum-output)))


(defface slime-repl-output-face
  (if (slime-face-inheritance-possible-p)
      '((t (:inherit font-lock-string-face)))
  ;; sjw: RosyBrown --> DarkBrown as was too light
    '((((class color) (background light)) (:foreground "DarkBrown"))
      (((class color) (background dark)) (:foreground "LightSalmon"))
      (t (:slant italic))))
  "Face for Lisp output in the SLIME REPL."
  :group 'slime-repl)

(defvar sw:system-name "Specware")

;; Mod to use new slime-repl-update-banner hooks?
(setq slime-repl-banner-function 'sw-slime-repl-insert-banner)
(defun sw-slime-repl-insert-banner ()
  (let* ((banner (format "%s %s on %s %s"
                         sw:system-name
			 (sw:eval-in-lisp "(if (boundp '*Specware-Version*) *Specware-Version* \"\")")
                         (slime-lisp-implementation-type)
			 (slime-lisp-implementation-version)
                         ;(slime-connection-port (slime-connection))
                         ;(slime-pid)
			 )))
    (insert banner)))

(defun slime-check-connected ()
  "Signal an error if we are not connected to Lisp."
  (unless (slime-connected-p)
    (error "Not connected. Use `%s' to start Specware."
	   ;; sjw: was slime
           (substitute-command-keys "\\[run-specware4]"))))

(defun slime-maybe-complete-as-filename ()
  "If point is at a string starting with \", complete it as filename.
Return nil iff if point is not at filename."
  (if t  ;(save-excursion (re-search-backward "\"[^ \t\n]+\\=" nil t))
      (let ((comint-completion-addsuffix '("/" . "\"")))
        (if slime-when-complete-filename-expand
            (comint-replace-by-expanded-filename)
          (comint-dynamic-complete-as-filename))
        t)
    nil))

(provide 'sw-slime)
