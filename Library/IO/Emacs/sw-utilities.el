;;;; Emacs utilities for Specware...

;;; Changed Specware's default directory within Emacs to be the current
;;; directory rather than the root directory for Specware itself. That way,
;;; when the user wishes to load a file from a menu, the starting
;;; path is current directory. The function (default-directory) is part
;;; of emacs. This begs the question of what should be done if the user
;;; changes directory.
;;; (defvar default-directory-name (concat *specware* "/"))

(require 'dired)			; For (default-directory)
(require 'cl-macs)

(defvar default-directory-name default-directory) ; moved to top of file to avoid warning msg

;; (verify-emacs-version)

;; (require 'sw-interface)

(defun parse-specware-file (file-name)
  "Send a .sl file to LISP for parsing."
  (interactive (list
		(read-file-name-for-lisp-command "Parse specware-file")))
  (query-about-saving-file file-name)
  (send-preemptive-message-to-lisp
   (format "(sp::meta-slang-parse %S )" file-name)))

(defun read-file-name-for-lisp-command (type-string &optional default)
  "Prompt for an existing file name with prompt
  \"TYPE-STRING file: file-name\" .  If optional DEFAULT present, use it as
  default file-name, otherwise use buffer-file-name if non-NIL,
  otherwise use default-directory-name.
  Typing return with a unique file name prefix will quietly
  complete and use the file name.  Won't accept name of a directory."
  (let* ((guess (or default buffer-file-name default-directory-name))
	 (raw-file-name
	  (read-file-name (format "%s file: " type-string)
			  guess guess 'confirm))
	 (expanded-file-name (expand-file-name raw-file-name)))
    (if (file-directory-p expanded-file-name)
	(progn
	  (ding)
	  (message (format "File: %s [a directory]" raw-file-name))
	  (sit-for 1)
	  (read-file-name-for-lisp-command type-string raw-file-name))
      expanded-file-name)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mouse sensitive interfacing.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'sw-msp-emacs)


(require 'widget)
(require 'wid-edit)
(eval-when-compile
 (require 'wid-edit))


(defun insert-mouse-sensitive-spec (specAndMarking)
  ;; sjw: 3/11/02 This is necessary to work around a bug in the Allegro emacs
  ;; interface on windows
  (setq specAndMarking (replace-in-string specAndMarking "\r" ""))
  (save-excursion
    (when *mspe-buffer* (set-buffer *mspe-buffer*))
    (when *mspe-marker* (goto-char *mspe-marker*))
    (let ((font-lock-on font-lock-mode))
      (if font-lock-on (font-lock-mode -1))
      (eval (car (read-from-string specAndMarking)))
      (message (format "%S" (point)))
      (if font-lock-on (font-lock-mode 1)))
    (when *mspe-marker* (set-marker *mspe-marker* (point)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defvar *font-lock-new-object-face* nil)
;
;(unless *font-lock-new-object-face*
;  (setq *font-lock-new-object-face*
;	(copy-face (find-face 'font-lock-reference-face) 'font-lock-new-object-face)));
;
;(defvar *font-lock-changed-object-face* nil);
;
;(unless *font-lock-changed-object-face*
;  (setq *font-lock-changed-object-face*
;	(copy-face (find-face 'font-lock-reference-face) 'font-lock-changed-object-face))
;  (make-face-italic 'font-lock-changed-object-face)
;  (set-face-background 'font-lock-changed-object-face "LightGray"))
;
;(defun emphasize-new-objects (ns)
;  (dolist (n ns)
;    (emphasize-new-object n)));
;
;(defun emphasize-new-object (n)
;  (let ((ext (car (mspe-extents-for-object n))))
;    (set-extent-face ext *font-lock-new-object-face*)))
;
;(defun emphasize-changed-objects (ns)
;  (dolist (n ns)
;    (emphasize-changed-object n)))
;
;(defun emphasize-changed-object (n)
;  (let ((ext (car (mspe-extents-for-object n))))
;    (set-extent-face ext *font-lock-changed-object-face*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *current-specware-ui-foci-frame* nil)
;;; Displaying designware foci

;;; x-create-frame (set-specware-ui-foci-frame 300 80 800 1000 3 "foo" "foo-buf")
(defun set-specware-ui-foci-frame
  (left top width height borders frame-title buffer-title)
  (unless (and
	   *current-specware-ui-foci-frame*
	   (frame-live-p *current-specware-ui-foci-frame*))
    (let ((bdrs (* borders 2))
	  (left (+ left borders))
	  (top (+ top borders)))
      (select-frame-if-active (get-frame-for-buffer (get-buffer-create sw:common-lisp-buffer-name)))
      (let* ((frame (selected-frame))
	     (int-bdrs (frame-property frame 'scrollbar-width))
	     (int-h-bdrs (+ int-bdrs
			    (frame-property frame 'right-margin-width)
			    (frame-property frame 'left-margin-width)))
	     (char-width (/ (- (frame-pixel-width frame) int-h-bdrs)
			    (frame-width frame)))
	     (char-height (/ (+ (- (frame-pixel-height frame) int-bdrs
				   ;; subtraction of 48 is emprical for misc headers, etc.
				   48)
				;; adding next value gives us ceiling instead of floor
				(- (frame-height frame) 1))
			     (frame-height frame)))
	     (menubar-height (+ char-height bdrs))
	     (titlebar-height (+ char-height (max 8 int-bdrs)))
	     (inner-width (- width bdrs
			     (if (boundp 'scrollbar)
				 scrollbar-width
			       (specifier-instance scrollbar-width frame))
			     int-bdrs))
	     (inner-height (- height bdrs int-bdrs menubar-height
			      titlebar-height))
	     (width (/ inner-width char-width))
	     (height (- (/ inner-height char-height) 2)))
	(setq *current-specware-ui-foci-frame*
	      (make-frame (`((left (,@ left))
			     (top (,@ top))
			     (width (,@ width))
			     (height (,@ height)))))))))
  (select-frame *current-specware-ui-foci-frame*)
  (raise-frame *current-specware-ui-foci-frame*)
  (switch-to-buffer (get-buffer-create buffer-title) t)
;;  (switch-to-buffer (generate-new-buffer buffer-title) t)
  (setq buffer-read-only t)
  (let ((buffer-read-only nil))
    (delete-region (point) (point-max)))
  (setq *mspe-buffer* (current-buffer))
  (setq *mspe-marker* (point-marker))
  (specware-ui-foci-mode)
  (setq frame-title-format frame-title))

(defun finish-printing-specware-ui-foci ()
  (select-frame *current-specware-ui-foci-frame*)
  (when *mspe-buffer* (set-buffer *mspe-buffer*))
  (setq buffer-read-only t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defconst *specware-ui-foci-menubar*
  '(
    ("File"
     ["Load Module"
      load-specware-module
      t]
     ["Save Module"
      save-specware-module
      t]
     ["Load and execute Module"
      load-execute-specware-module
      t]

     "-------------------------"
     ["Compile and save in LISP"
      compile-and-save-in-lisp
      t]

     ["Compile and save in C"
      compile-and-save-in-c
      t]

;;; These features are now working on Unix but undocumented and not fully
;;; tested.  Have decided to make them unavailable in the current realeas
;;;     ["Save and view as pdf"
;;;      (send-message-to-lisp
;;;       "(SpecwareUI::doAction \"View as pdf\")")
;;;      t]
;;;
;;;     ["View as web page"
;;;      (send-message-to-lisp
;;;       "(SpecwareUI::doAction \"View as web page\")")
;;;      t]
     "-------------------------"
     ["Save session as tactic"
      save-tactic-file
      t]
     ["Load session as tactic"
      load-tactic-file
      t]
      "-------------------------"
      ["Exit"
       exit-action
       t])

    ("Edit"
     ["Undo"
      (send-message-to-lisp
       "(SpecwareUI::doAction \"Undo\")")
      t]
     ["Redo"
      (send-message-to-lisp
       "(SpecwareUI::doAction \"Redo\")")
      t]
     )

    ("Transformation"
      ["Simplify"
       (sw:eval-interruptable-in-lisp
	"(SpecwareUI::doAction \"Simplify\")")
       t]
      ["One step Simplify"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"Simplify1\")")
       t]
      ["Finite Differencing"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"FiniteDifferencing\")")
       t]
      ["Unfold by definition"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"UnfoldDefinition\")")
       t]
      ["Fold by definition"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"FoldDefinition\")")
       t]
      ["Case Split"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"CaseSplit\")")
       t]
      ["Case Analysis"
       (send-message-to-lisp
	"(SpecwareUI::doAction \"CaseAnalysis\")")
       t]
      ["Verify with Gandalf"
       (sw:eval-interruptable-in-lisp
	"(SpecwareUI::doAction \"Gandalf\")")
       t]
      ["Verify with SNARK"
       (sw:eval-interruptable-in-lisp
       "(SpecwareUI::doAction \"SNARK\")")
       t])

    ("Type Check"
     ["Generate type check conditions"
      (send-message-to-lisp
       "(SpecwareUI::doAction \"TypeCheck\")")
      t])

    ()

     ["Help"
      help-on-specware
      t]

    ["Cancel"
     cancel-action
     t]
))


(defun exit-action ()
  (interactive)
  (delete-frame)
  )

(defun help-on-specware ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"Help\")"))

(defun load-specware-module (file-name)
  (interactive (list
		(read-file-name-for-lisp-command "Parse specware")))
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2 \"Load\" %S)" file-name)))

(defun load-execute-specware-module (file-name)
  (interactive (list
		(read-file-name-for-lisp-command "Specware")))
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2 \"Load-Execute\" %S)" file-name)))

(defun save-specware-module (file-name)
  (interactive (list
		(read-file-name "Save module in file: "
				(or buffer-file-name default-directory-name))))
  (query-about-saving-file file-name)
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2 \"Save\" %S)" file-name)))

(defun save-tactic-file (file-name)
  (interactive (list
		(read-file-name "Save session as tactic in file: "
				(concat *specware* "/tactics/"))))
  (query-about-saving-file file-name)
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2  \"Save Tactic\" %S)" file-name)))

(defun load-tactic-file (file-name)
  (interactive (list
		(read-file-name-for-lisp-command
		 "Load and apply session tactic"
		 (concat *specware* "/tactics/"))))
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2  \"Load Tactic\" %S)" file-name)))


(defun compile-and-save-in-c (file-name)
  (interactive (list
		(read-file-name "File for C code: "
				(or buffer-file-name default-directory-name))))
  (query-about-saving-file file-name)
  (send-message-to-lisp
   (format "(SpecwareUI::doAction2  \"C\" %S)" file-name)))

(defun compile-and-save-in-lisp (file-name)
  (interactive (list
		(read-file-name "File for Lisp code: "
				(or buffer-file-name default-directory-name))))
    (query-about-saving-file file-name)
    (send-message-to-lisp
     (format "(SpecwareUI::doAction2 \"LISP\" %S)" file-name)))


;; Designware menu utilities

(defun focus-on-module ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::solicitAndSetSpecwareUIFocus t)"))

(defun focus-on-spec-diagram ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::solicitAndSetSpecwareUIFocus nil)"))

(defun apply-refinement-from-library-taxonomy ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::applyRefinementFromLibraryTaxonomy
       SpecwareUI::specware-ui-current-defining-diagram)"))

(defun apply-refinement-from-library-diagram ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::applyRefinementFromLibraryDiagram
       SpecwareUI::specware-ui-current-defining-diagram)"))

(defun context-dependent-simplify-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"ContextDependentSimplify\")"))

(defun context-independent-simplify-fast-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"ContextIndependentSimplifyFast\")"))

(defun cases-to-conditional-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"CasesToConditional\")"))

(defun fd-conditioning-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"FdConditioning\")"))


(defun invert-constructors-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"InvertConstructors\")"))

(defun remove-closures-by-partial-evaluation-tactic ()
  (interactive)
  (send-message-to-lisp
   "(SpecwareUI::doAction \"RemoveClosures\")"))

(defun cancel-action ()
  (interactive)
  (if (null sw:*current-specware-process*)
      ()
    (progn
      (sw:eval-in-lisp
       (format
	"(mp::process-kill (MP:PROCESS-NAME-TO-PROCESS \"%s\"))"
	sw:*current-specware-process*))
      (setq sw:*current-specware-process* nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar specware-ui-foci-mspe-keymap nil)

(defun specware-ui-foci-mode ()
  "Major mode for Specware"
  (interactive)
  (kill-all-local-variables)
  (lisp-mode-variables nil)
  (setq major-mode 'specware)
  (setq mode-name "Specware")
  (make-local-variable 'mspe-keymap)
  (make-local-variable 'frame-title-format)
  (setq frame-title-format "%S")
  (set-buffer-menubar *specware-ui-foci-menubar*)
  ;; make default file names reasonable
  ;; (setq default-directory-name (concat *specware* "/"))
  (setq default-directory-name default-directory)
;;  (make-local-variable 'save-buffers-skip)
;;  (setq save-buffers-skip t)
  (setq mspe-keymap specware-ui-foci-mspe-keymap)
  (use-local-map specware-ui-foci-mspe-keymap)
  (turn-on-font-lock)
  )

(unless specware-ui-foci-mspe-keymap
  (setq specware-ui-foci-mspe-keymap (copy-keymap view-minor-mode-map))
  (set-keymap-name specware-ui-foci-mspe-keymap 'specware-ui-foci-mspe-keymap)
  (define-key specware-ui-foci-mspe-keymap
    '(button2) 'specware-ui-object-menu)
  (define-key specware-ui-foci-mspe-keymap
    '(button3) 'extent-copy-as-kill)
  (define-key specware-ui-foci-mspe-keymap
    '(control button1) 'extent-insert-lisp-ref))

(defun specware-ui-object-menu (e)
  (interactive "e")
  (let ((ext (extent-of-event e)))
    (send-message-to-lisp
     (format "(SpecwareUI::specware-ui-object-menu-from-emacs %d)"
       (extent-property ext 'object-number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Open window for user to view message


;; Mock line counter: allocate 20 chars per line.

(defun adhoc-count-lines (message)
  (+ 2 (/ (length message) 20)))

(defun open-output-window (message)
  (interactive)
  (let* ((buf (get-buffer-create "Message"))
	 (frame (or (buffer-dedicated-frame buf)
		    (make-frame (`((left (,@ 400))
				 (top (,@ 400))
				 (width (,@ 80))
				 (height (,@ (min 40 (adhoc-count-lines message))))))))))
    (set-buffer-dedicated-frame buf frame)
    (select-frame frame)
    (switch-to-buffer buf)
    (make-local-variable 'frame-title-format)
    (setq frame-title-format "Message")
    ;;(message message)
    (hacked-set-buffer-menubar '(nil ["Cancel" delete-frame t]))
    (setq buffer-read-only nil)
    (erase-buffer)
    (widget-insert message)
    (setq buffer-read-only t)
    (make-frame-visible frame)))
;; (open-output-window "test 1")

(defun hacked-set-buffer-menubar (menubar)
  (if (eq window-system 'mswindows)
      (let ()
	(make-local-variable 'menubar-show-keybindings)
	(setq menubar-show-keybindings nil)
	(set-menubar-dirty-flag)
	(set-buffer-menubar (cons "Dummyname" menubar))
	;(raise-frame)
	)
    (set-buffer-menubar menubar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Open window for user to type input
(defun open-input-window ()
  (interactive)
  (select-frame (make-frame (`((left (,@ 400))
			       (top (,@ 400))
			       (width (,@ 80))
			       (height (,@ 8))))))
  (switch-to-buffer (generate-new-buffer "Input Window"))
  (make-local-variable 'frame-title-format)
  (setq frame-title-format "Input")
  (hacked-set-buffer-menubar '(nil ["Done Editing" return-string-from-buffer t]
			       ["Cancel" cancel-string-from-buffer t])))

(defun return-string-from-buffer ()
  (interactive)
  (send-preemptive-message-to-lisp (format "(Emacs::parseTerm %S)" (buffer-string)))
  (delete-frame))

(defun cancel-string-from-buffer ()
  (interactive)
  (send-preemptive-message-to-lisp "(Emacs::parseTerm \"\")")
  (delete-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Swith focus on modules

(defun set-module-focus (specName)
  (send-message-to-lisp (format nil "(SpecwareUI::setFocus %S)" specName)))

(defun set-module-focus-0 ()
  (interactive)
  (send-message-to-lisp (format nil "(SpecwareUI::setFocus \"Triv\")")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Create a window with selectable choices
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun open-choice-window (choices)
  (interactive)
  (select-frame (make-frame (`((left (,@ 400))
                               (top (,@ 400))
                               (width (,@ 80))
                               (height (,@ 8))
			       (has-modeline-p nil)
			       (minibuffer . none)))))
  (switch-to-buffer (get-buffer-create "*Choose an alternative*"))
  (setq buffer-read-only nil)
  (erase-buffer)
  (make-local-variable 'frame-title-format)
  (setq frame-title-format "Choose among alternatives")
  (setq buffer-read-only t)
  (hacked-set-buffer-menubar '(["Cancel" cancel-choice-from-buffer]))
  (add-choices choices)
)

(defun return-choice-from-buffer (choice event)
  (interactive)
  (send-preemptive-message-to-lisp (format "(Emacs::choiceItem %S)" choice))
  (delete-frame (event-frame event)))

(defun cancel-choice-from-buffer (event)
  (interactive "e")
  (send-preemptive-message-to-lisp "(Emacs::choiceItem -1)")
  (delete-frame (event-frame event)))

(defvar *numbered-choices*)

(defun add-choices (choices)
  (interactive)
  (let* (
	 (counter 0)
	 (numbered-choices (mapcar (lambda (ch) (progn (setq counter (1+ counter))
						       (cons ch counter)))
				   choices))
	 (item-choices (mapcar (lambda(ch) (list 'item ch)) choices))
	 )
    (make-local-variable '*numbered-choices*)
    (setq *numbered-choices* numbered-choices)
    (apply 'widget-create
	   (cl-list* 'radio-button-choice
	             :value nil
	             :notify 'choice-notify
	             item-choices))
    (message "Choose an entry")))

(defun choice-notify (widget ignore event)
  (let* ((value (widget-value widget))
	 (numbered-choices *numbered-choices*)
	 (int-value (cdr (find-if (lambda(ch)
				    (string= (car ch) value))
				  numbered-choices))))
    (return-choice-from-buffer int-value event)))


(defun testchoices()
   (open-choice-window '("Choice 1" "Choice 2" "Choice 3")))

(defun theorem-widget (thm-number enabled sos?)
  (let ((w (widget-create 'checkbox
			  :notify
			  (if sos?
			      (lambda(widget &rest ignore)
				(let ((value (widget-value widget))
				      (thm-number (widget-get widget 'thm-number)))
				  (message "%s set of support"
					   (if value "Adding to" "Removing from"))
				  (send-message-to-lisp
				   (format "(Emacs::toggleSosIndex %s %s)" thm-number value))))
			    (lambda(widget &rest ignore)
			      (let ((value (widget-value widget))
				    (thm-number (widget-get widget 'thm-number)))
				(message "%s property"
					 (if value "Enabling" "Disabling"))
				(send-message-to-lisp
				 (format "(Emacs::toggleIndex %s %s)" thm-number value)))))
			  :value enabled)))
    (widget-put w 'thm-number thm-number)
    w))

(provide 'sw-utilities)
